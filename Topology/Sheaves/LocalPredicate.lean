/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz
-/
module

public import Mathlib.Topology.Sheaves.SheafOfFunctions
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Functions satisfying a local predicate form a sheaf.

At this stage, in `Mathlib/Topology/Sheaves/SheafOfFunctions.lean`
we've proved that not-necessarily-continuous functions from a topological space
into some type (or type family) form a sheaf.

Why do the continuous functions form a sheaf?
The point is just that continuity is a local condition,
so one can use the lifting condition for functions to provide a candidate lift,
then verify that the lift is actually continuous by using the factorisation condition for the lift
(which guarantees that on each open set it agrees with the functions being lifted,
which were assumed to be continuous).

This file abstracts this argument to work for
any collection of dependent functions on a topological space
satisfying a "local predicate".

As an application, we check that continuity is a local predicate in this sense, and provide
* `TopCat.sheafToTop`: continuous functions into a topological space form a sheaf

A sheaf constructed in this way has a natural map `stalkToFiber` from the stalks
to the types in the ambient type family.

We give conditions sufficient to show that this map is injective and/or surjective.
-/

@[expose] public section

noncomputable section

variable {X : TopCat}
variable (T : X -> Type*)

open TopologicalSpace

open Opposite

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Limits.Types

namespace TopCat

/--
Definition of `PrelocalPredicate` / `PrelocalPredicate` 的定义

English:
structure PrelocalPredicate
  parameters: where
  axioms and operations (2):
    - pred : forall {U : Opens X}, (forall x : U, T x) -> Prop
    - res : forall {U V : Opens X} (i : U ⟶ V) (f : forall x : V, T x) (_ : pred f), pred fun x : U => f (i x)

中文:
结构 PrelocalPredicate
  参数: where
  公理与运算 (2 个):
    - pred : 对任意 {U : Opens X}, (对任意 x : U, T x) -> 命题
    - res : 对任意 {U V : Opens X} (i : U ⟶ V) (f : 对任意 x : V, T x) (_ : pred f), pred fun x : U => f (i x)
-/
structure PrelocalPredicate where
  /-- The underlying predicate of a prelocal predicate -/
  pred : forall {U : Opens X}, (forall x : U, T x) -> Prop
  /-- The underlying predicate should be invariant under restriction -/
  res : forall {U V : Opens X} (i : U ⟶ V) (f : forall x : V, T x) (_ : pred f), pred fun x : U => f (i x)

variable (X)

/-- Continuity is a "prelocal" predicate on functions to a fixed topological space `T`.
-/
@[simps!]
/--
Definition of `continuousPrelocal` / `continuousPrelocal` 的定义

English:
definition continuousPrelocal
  signature: (T) [TopologicalSpace T]
  body: Continuous f
  res {_ _} i _ h := Continuous.comp h (Opens.isOpenEmbedding_of_le i.le).continuous

中文:
定义 continuousPrelocal
  签名: (T) [拓扑空间 T]
  定义体: Continuous f
  res {_ _} i _ h := Continuous.comp h (Opens.isOpenEmbedding_of_le i.le).continuous

Depends on / 依赖: Continuous
-/
def continuousPrelocal (T) [TopologicalSpace T] : PrelocalPredicate fun _ : X => T where
  pred {_} f := Continuous f
  res {_ _} i _ h := Continuous.comp h (Opens.isOpenEmbedding_of_le i.le).continuous

/--
Instance `inhabitedPrelocalPredicate` / 实例 `inhabitedPrelocalPredicate`

English:
instance inhabitedPrelocalPredicate
  signature: (T) [TopologicalSpace T]
  body: ⟨continuousPrelocal X T⟩

中文:
实例 inhabitedPrelocalPredicate
  签名: (T) [拓扑空间 T]
  定义体: ⟨continuousPrelocal X T⟩

Depends on / 依赖: continuousPrelocal
-/
instance inhabitedPrelocalPredicate (T) [TopologicalSpace T] :
    Inhabited (PrelocalPredicate fun _ : X => T) :=
  ⟨continuousPrelocal X T⟩

variable {X} in
/--
Definition of `LocalPredicate` / `LocalPredicate` 的定义

English:
structure LocalPredicate
  parameters: extends PrelocalPredicate T
  extends: PrelocalPredicate T
  axioms and operations (1):
    - locality : forall {U : Opens X} (f : forall x : U, T x) (_ : forall x : U, exists (V : Opens X) (_ : x.1 in V) (i : V ⟶ U), pred fun x : V => f (i x : U)), pred f

中文:
结构 LocalPredicate
  参数: extends PrelocalPredicate T
  继承: PrelocalPredicate T
  公理与运算 (1 个):
    - locality : 对任意 {U : Opens X} (f : 对任意 x : U, T x) (_ : 对任意 x : U, 存在 (V : Opens X) (_ : x.1 in V) (i : V ⟶ U), pred fun x : V => f (i x : U)), pred f
-/
structure LocalPredicate extends PrelocalPredicate T where
  /-- A local predicate must be local --- provided that it is locally satisfied, it is also globally
  satisfied -/
  locality :
    forall {U : Opens X} (f : forall x : U, T x)
      (_ : forall x : U, exists (V : Opens X) (_ : x.1 in V) (i : V ⟶ U),
        pred fun x : V => f (i x : U)), pred f

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `continuousLocal` / `continuousLocal` 的定义

English:
definition continuousLocal
  signature: (T) [TopologicalSpace T]
  body: { continuousPrelocal X T with
    locality := fun {U} f w => by
      apply continuous_iff_continuousAt.2
      intro x
      specialize w x
      rcases w with ⟨V, m, i, w⟩
      dsimp at w
      rw [continuous_iff_continuousAt] at w
      specialize w ⟨x, m⟩
      simpa using (Opens.isOpenEmbeddin

中文:
定义 continuousLocal
  签名: (T) [拓扑空间 T]
  定义体: { continuousPrelocal X T with
    locality := fun {U} f w => by
      apply continuous_iff_continuousAt.2
      intro x
      specialize w x
      rcases w with ⟨V, m, i, w⟩
      dsimp at w
      rw [continuous_iff_continuousAt] at w
      specialize w ⟨x, m⟩
      simpa using (Opens.isOpenEmbeddin

Depends on / 依赖: Opens.isOpenEmbedding_of_le, continuousAt_iff, continuousPrelocal, continuous_iff_continuousAt, i.le, isOpenEmbedding_of_le, locality, specialize
-/
def continuousLocal (T) [TopologicalSpace T] : LocalPredicate fun _ : X => T :=
  { continuousPrelocal X T with
    locality := fun {U} f w => by
      apply continuous_iff_continuousAt.2
      intro x
      specialize w x
      rcases w with ⟨V, m, i, w⟩
      dsimp at w
      rw [continuous_iff_continuousAt] at w
      specialize w ⟨x, m⟩
      simpa using (Opens.isOpenEmbedding_of_le i.le).continuousAt_iff.1 w }

/--
Instance `inhabitedLocalPredicate` / 实例 `inhabitedLocalPredicate`

English:
instance inhabitedLocalPredicate
  signature: (T) [TopologicalSpace T]
  body: ⟨continuousLocal X T⟩

中文:
实例 inhabitedLocalPredicate
  签名: (T) [拓扑空间 T]
  定义体: ⟨continuousLocal X T⟩

Depends on / 依赖: continuousLocal
-/
instance inhabitedLocalPredicate (T) [TopologicalSpace T] :
    Inhabited (LocalPredicate fun _ : X => T) :=
  ⟨continuousLocal X T⟩

variable {X T}

/--
Definition of `PrelocalPredicate.and` / `PrelocalPredicate.and` 的定义

English:
definition PrelocalPredicate.and
  signature: (P Q : PrelocalPredicate T)
  body: P.pred f ∧ Q.pred f
  res i f h := ⟨P.res i f h.1, Q.res i f h.2⟩

中文:
定义 PrelocalPredicate.and
  签名: (P Q : PrelocalPredicate T)
  定义体: P.pred f ∧ Q.pred f
  res i f h := ⟨P.res i f h.1, Q.res i f h.2⟩

Depends on / 依赖: P.pred, Q.pred
-/
def PrelocalPredicate.and (P Q : PrelocalPredicate T) : PrelocalPredicate T where
  pred f := P.pred f ∧ Q.pred f
  res i f h := ⟨P.res i f h.1, Q.res i f h.2⟩

/--
Definition of `LocalPredicate.and` / `LocalPredicate.and` 的定义

English:
definition LocalPredicate.and
  signature: (P Q : LocalPredicate T)
  body: P.1.and Q.1
  locality f w := by
    refine ⟨P.locality f ?_, Q.locality f ?_⟩ <;>
      (intro x; have ⟨V, hV, i, h⟩ := w x; use V, hV, i)
    exacts [h.1, h.2]

中文:
定义 LocalPredicate.and
  签名: (P Q : LocalPredicate T)
  定义体: P.1.and Q.1
  locality f w := by
    refine ⟨P.locality f ?_, Q.locality f ?_⟩ <;>
      (intro x; have ⟨V, hV, i, h⟩ := w x; use V, hV, i)
    exacts [h.1, h.2]
-/
def LocalPredicate.and (P Q : LocalPredicate T) : LocalPredicate T where
  __ := P.1.and Q.1
  locality f w := by
    refine ⟨P.locality f ?_, Q.locality f ?_⟩ <;>
      (intro x; have ⟨V, hV, i, h⟩ := w x; use V, hV, i)
    exacts [h.1, h.2]

/--
Definition of `isSection` / `isSection` 的定义

English:
definition isSection
  signature: {T} (p : T -> X)
  body: p ∘ f = (↑)
  res _ _ h := funext fun _ => congr_fun h _
  locality _ w := funext fun x => have ⟨_, hV, _, h⟩ := w x; congr_fun h ⟨x, hV⟩

中文:
定义 isSection
  签名: {T} (p : T -> X)
  定义体: p ∘ f = (↑)
  res _ _ h := funext fun _ => congr_fun h _
  locality _ w := funext fun x => have ⟨_, hV, _, h⟩ := w x; congr_fun h ⟨x, hV⟩
-/
def isSection {T} (p : T -> X) : LocalPredicate fun _ : X => T where
  pred f := p ∘ f = (↑)
  res _ _ h := funext fun _ => congr_fun h _
  locality _ w := funext fun x => have ⟨_, hV, _, h⟩ := w x; congr_fun h ⟨x, hV⟩

/--
Definition of `PrelocalPredicate.sheafify` / `PrelocalPredicate.sheafify` 的定义

English:
definition PrelocalPredicate.sheafify
  signature: {T : X -> Type*} (P : PrelocalPredicate T)
  body: forall x : U, exists (V : Opens X) (_ : x.1 in V) (i : V ⟶ U), P.pred fun x : V => f (i x : U)
  res {V U} i f w x := by
    specialize w (i x)
    rcases w with ⟨V', m', i', p⟩
    exact ⟨V ⊓ V', ⟨x.2, m'⟩, V.infLELeft _, P.res (V.infLERight V') _ p⟩
  locality {U} f w x := by
    specialize w x
  

中文:
定义 PrelocalPredicate.sheafify
  签名: {T : X -> 类型} (P : PrelocalPredicate T)
  定义体: forall x : U, exists (V : Opens X) (_ : x.1 in V) (i : V ⟶ U), P.pred fun x : V => f (i x : U)
  res {V U} i f w x := by
    specialize w (i x)
    rcases w with ⟨V', m', i', p⟩
    exact ⟨V ⊓ V', ⟨x.2, m'⟩, V.infLELeft _, P.res (V.infLERight V') _ p⟩
  locality {U} f w x := by
    specialize w x
  

Depends on / 依赖: P.pred
-/
def PrelocalPredicate.sheafify {T : X -> Type*} (P : PrelocalPredicate T) : LocalPredicate T where
  pred {U} f := forall x : U, exists (V : Opens X) (_ : x.1 in V) (i : V ⟶ U), P.pred fun x : V => f (i x : U)
  res {V U} i f w x := by
    specialize w (i x)
    rcases w with ⟨V', m', i', p⟩
    exact ⟨V ⊓ V', ⟨x.2, m'⟩, V.infLELeft _, P.res (V.infLERight V') _ p⟩
  locality {U} f w x := by
    specialize w x
    rcases w with ⟨V, m, i, p⟩
    specialize p ⟨x.1, m⟩
    rcases p with ⟨V', m', i', p'⟩
    exact ⟨V', m', i' ≫ i, p'⟩

namespace PrelocalPredicate

/--
theorem `sheafifyOf` / 定理 `sheafifyOf`

English:
theorem sheafifyOf
  statement: {T : X -> Type*} {P : PrelocalPredicate T} {U : Opens X}
  proof: fun x =>
  ⟨U, x.2, 𝟙 _, by convert! h⟩

中文:
定理 sheafifyOf
  结论: {T : X -> 类型} {P : PrelocalPredicate T} {U : Opens X}
  证明: fun x =>
  ⟨U, x.2, 𝟙 _, by convert! h⟩
-/
theorem sheafifyOf {T : X -> Type*} {P : PrelocalPredicate T} {U : Opens X}
    {f : forall x : U, T x} (h : P.pred f) : P.sheafify.pred f := fun x =>
  ⟨U, x.2, 𝟙 _, by convert! h⟩

/--
theorem `sheafify_inductionOn` / 定理 `sheafify_inductionOn`

English:
theorem sheafify_inductionOn
  statement: {X : TopCat} {T : X -> Type*} (P : PrelocalPredicate T)
  proof: by
  intro x
  rcases ha x with ⟨Va, ma, ia, ha⟩
  rcases hop ha ⟨x, ma⟩ with ⟨W, sa, hx, hw⟩
  exact ⟨W, hx, sa ≫ ia, hw⟩

中文:
定理 sheafify_inductionOn
  结论: {X : 顶元素范畴} {T : X -> 类型} (P : PrelocalPredicate T)
  证明: by
  intro x
  rcases ha x with ⟨Va, ma, ia, ha⟩
  rcases hop ha ⟨x, ma⟩ with ⟨W, sa, hx, hw⟩
  exact ⟨W, hx, sa ≫ ia, hw⟩
-/
theorem sheafify_inductionOn {X : TopCat} {T : X -> Type*} (P : PrelocalPredicate T)
    (op : {x : X} -> T x -> T x)
    (hop : forall {U : Opens X} {a : (x : U) -> T x}, P.pred a ->
      forall (p : U), exists (W : Opens X) (i : W ⟶ U), p.1 in W ∧ P.pred fun x : W => op (a (i x)))
    {U : Opens X} {a : (x : U) -> T x} (ha : P.sheafify.pred a) :
    P.sheafify.pred (fun x : U => op (a x)) := by
  intro x
  rcases ha x with ⟨Va, ma, ia, ha⟩
  rcases hop ha ⟨x, ma⟩ with ⟨W, sa, hx, hw⟩
  exact ⟨W, hx, sa ≫ ia, hw⟩

/--
theorem `sheafify_inductionOn'` / 定理 `sheafify_inductionOn'`

English:
theorem sheafify_inductionOn'
  statement: {X : TopCat} {T : X -> Type*} (P : PrelocalPredicate T)
  proof: P.sheafify_inductionOn op (fun ha p => ⟨_, 𝟙 _, p.2, hop ha⟩) ha

中文:
定理 sheafify_inductionOn'
  结论: {X : 顶元素范畴} {T : X -> 类型} (P : PrelocalPredicate T)
  证明: P.sheafify_inductionOn op (fun ha p => ⟨_, 𝟙 _, p.2, hop ha⟩) ha

Depends on / 依赖: P.sheafify_inductionOn, sheafify_inductionOn
-/
theorem sheafify_inductionOn' {X : TopCat} {T : X -> Type*} (P : PrelocalPredicate T)
    (op : {x : X} -> T x -> T x)
    (hop : forall {U : Opens X} {a : (x : U) -> T x}, P.pred a -> P.pred fun x : U => op (a x))
    {U : Opens X} {a : (x : U) -> T x} (ha : P.sheafify.pred a) :
    P.sheafify.pred (fun x : U => op (a x)) :=
  P.sheafify_inductionOn op (fun ha p => ⟨_, 𝟙 _, p.2, hop ha⟩) ha

/--
theorem `sheafify_inductionOn₂` / 定理 `sheafify_inductionOn₂`

English:
theorem sheafify_inductionOn₂
  statement: {X : TopCat} {T₁ T₂ T₃ : X -> Type*}
  proof: by
  intro x
  rcases ha x with ⟨Va, ma, ia, ha⟩
  rcases hb x with ⟨Vb, mb, ib, hb⟩
  rcases hop ha hb ⟨x, ma, mb⟩ with ⟨W, sa, sb, hx, hw⟩
  exact ⟨W, hx, sa ≫ ia, hw⟩

中文:
定理 sheafify_inductionOn₂
  结论: {X : 顶元素范畴} {T₁ T₂ T₃ : X -> 类型}
  证明: by
  intro x
  rcases ha x with ⟨Va, ma, ia, ha⟩
  rcases hb x with ⟨Vb, mb, ib, hb⟩
  rcases hop ha hb ⟨x, ma, mb⟩ with ⟨W, sa, sb, hx, hw⟩
  exact ⟨W, hx, sa ≫ ia, hw⟩
-/
theorem sheafify_inductionOn₂ {X : TopCat} {T₁ T₂ T₃ : X -> Type*}
    (P₁ : PrelocalPredicate T₁) (P₂ : PrelocalPredicate T₂) (P₃ : PrelocalPredicate T₃)
    (op : {x : X} -> T₁ x -> T₂ x -> T₃ x)
    (hop : forall {U V : Opens X} {a : (x : U) -> T₁ x} {b : (x : V) -> T₂ x}, P₁.pred a -> P₂.pred b ->
      forall (p : (U ⊓ V : Opens X)), exists (W : Opens X) (ia : W ⟶ U) (ib : W ⟶ V),
      p.1 in W ∧ P₃.pred fun x : W => op (a (ia x)) (b (ib x)))
    {U : Opens X} {a : (x : U) -> T₁ x} {b : (x : U) -> T₂ x}
    (ha : P₁.sheafify.pred a) (hb : P₂.sheafify.pred b) :
    P₃.sheafify.pred (fun x : U => op (a x) (b x)) := by
  intro x
  rcases ha x with ⟨Va, ma, ia, ha⟩
  rcases hb x with ⟨Vb, mb, ib, hb⟩
  rcases hop ha hb ⟨x, ma, mb⟩ with ⟨W, sa, sb, hx, hw⟩
  exact ⟨W, hx, sa ≫ ia, hw⟩

/--
theorem `sheafify_inductionOn₂'` / 定理 `sheafify_inductionOn₂'`

English:
theorem sheafify_inductionOn₂'
  statement: {X : TopCat} {T₁ T₂ T₃ : X -> Type*}
  proof: P₁.sheafify_inductionOn₂ P₂ P₃ op
    (fun ha hb p => ⟨_, Opens.infLELeft _ _, Opens.infLERight _ _, p.2, hop ha hb⟩) ha hb

中文:
定理 sheafify_inductionOn₂'
  结论: {X : 顶元素范畴} {T₁ T₂ T₃ : X -> 类型}
  证明: P₁.sheafify_inductionOn₂ P₂ P₃ op
    (fun ha hb p => ⟨_, Opens.infLELeft _ _, Opens.infLERight _ _, p.2, hop ha hb⟩) ha hb

Depends on / 依赖: Opens.infLELeft, Opens.infLERight, infLELeft, infLERight
-/
theorem sheafify_inductionOn₂' {X : TopCat} {T₁ T₂ T₃ : X -> Type*}
    (P₁ : PrelocalPredicate T₁) (P₂ : PrelocalPredicate T₂) (P₃ : PrelocalPredicate T₃)
    (op : {x : X} -> T₁ x -> T₂ x -> T₃ x)
    (hop : forall {U V : Opens X} {a : (x : U) -> T₁ x} {b : (x : V) -> T₂ x}, P₁.pred a -> P₂.pred b ->
      P₃.pred fun x : (U ⊓ V : Opens X) => op (a ⟨x, x.2.1⟩) (b ⟨x, x.2.2⟩))
    {U : Opens X} {a : (x : U) -> T₁ x} {b : (x : U) -> T₂ x}
    (ha : P₁.sheafify.pred a) (hb : P₂.sheafify.pred b) :
    P₃.sheafify.pred (fun x : U => op (a x) (b x)) :=
  P₁.sheafify_inductionOn₂ P₂ P₃ op
    (fun ha hb p => ⟨_, Opens.infLELeft _ _, Opens.infLERight _ _, p.2, hop ha hb⟩) ha hb

end PrelocalPredicate

/-- The subpresheaf of dependent functions on `X` satisfying the "pre-local" predicate `P`.
-/
@[simps]
/--
Definition of `subpresheafToTypes` / `subpresheafToTypes` 的定义

English:
definition subpresheafToTypes
  signature: (P : PrelocalPredicate T)
  body: { f : forall x : U.unop, T x // P.pred f }
  map i := ↾fun f => ⟨fun x => f.1 (i.unop x), P.res i.unop f.1 f.2⟩

中文:
定义 subpresheafToTypes
  签名: (P : PrelocalPredicate T)
  定义体: { f : forall x : U.unop, T x // P.pred f }
  map i := ↾fun f => ⟨fun x => f.1 (i.unop x), P.res i.unop f.1 f.2⟩

Depends on / 依赖: P.pred, U.unop
-/
def subpresheafToTypes (P : PrelocalPredicate T) : Presheaf (Type _) X where
  obj U := { f : forall x : U.unop, T x // P.pred f }
  map i := ↾fun f => ⟨fun x => f.1 (i.unop x), P.res i.unop f.1 f.2⟩

namespace subpresheafToTypes

variable (P : PrelocalPredicate T)

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: : subpresheafToTypes P ⟶ presheafToTypes X T where app _
  body: ↾fun f => f.1

中文:
定义 subtype
  签名: : subpresheafToTypes P ⟶ presheafToTypes X T where app _
  定义体: ↾fun f => f.1
-/
def subtype : subpresheafToTypes P ⟶ presheafToTypes X T where app _ := ↾fun f => f.1

open TopCat.Presheaf

/--
theorem `isSheaf` / 定理 `isSheaf`

English:
theorem isSheaf
  given: (P : LocalPredicate T)
  statement: (subpresheafToTypes P.toPrelocalPredicate).IsSheaf
  proof: Presheaf.isSheaf_of_isSheafUniqueGluing_types _ fun ι U sf sf_comp => by
    -- We show the sheaf condition in terms of unique gluing.
    -- First we obtain a family of sections for the underlying sheaf of functions,
    -- by forgetting that the predicate holds
    let sf' (i : ι) : (presheafToTyp

中文:
定理 isSheaf
  条件: (P : LocalPredicate T)
  结论: (subpresheafToTypes P.toPrelocalPredicate).是层
  证明: Presheaf.isSheaf_of_isSheafUniqueGluing_types _ fun ι U sf sf_comp => by
    -- We show the sheaf condition in terms of unique gluing.
    -- First we obtain a family of sections for the underlying sheaf of functions,
    -- by forgetting that the predicate holds
    let sf' (i : ι) : (presheafToTyp

Depends on / 依赖: Presheaf, Presheaf.isSheaf_of_isSheafUniqueGluing_types, isSheaf_of_isSheafUniqueGluing_types, sf_comp
-/
theorem isSheaf (P : LocalPredicate T) : (subpresheafToTypes P.toPrelocalPredicate).IsSheaf :=
  Presheaf.isSheaf_of_isSheafUniqueGluing_types _ fun ι U sf sf_comp => by
    -- We show the sheaf condition in terms of unique gluing.
    -- First we obtain a family of sections for the underlying sheaf of functions,
    -- by forgetting that the predicate holds
    let sf' (i : ι) : (presheafToTypes X T).obj (op (U i)) := (sf i).val
    -- Since our original family is compatible, this one is as well
    have sf'_comp : (presheafToTypes X T).IsCompatible U sf' := fun i j =>
      congr_arg Subtype.val (sf_comp i j)
    -- So, we can obtain a unique gluing
    obtain ⟨gl, gl_spec, gl_uniq⟩ := (sheafToTypes X T).existsUnique_gluing U sf'
      -- `by exact` to help Lean infer the `ConcreteCategory` instance
      (by exact sf'_comp)
    refine ⟨⟨gl, ?_⟩, ?_, ?_⟩
    · -- Our first goal is to show that this chosen gluing satisfies the
      -- predicate. Of course, we use locality of the predicate.
      apply P.locality
      rintro ⟨x, mem⟩
      -- Once we're at a particular point `x`, we can select some open set `x ∈ U i`.
      choose i hi using Opens.mem_iSup.mp mem
      -- We claim that the predicate holds in `U i`
      use U i, hi, Opens.leSupr U i
      -- This follows, since our original family `sf` satisfies the predicate
      convert! (sf i).property using 1
      exact gl_spec i
    -- It remains to show that the chosen lift is really a gluing for the subsheaf and
    -- that it is unique. Both of which follow immediately from the corresponding facts
    -- in the sheaf of functions without the local predicate.
    · exact fun i => Subtype.ext (gl_spec i)
    · intro gl' hgl'
      refine Subtype.ext ?_
      exact gl_uniq gl'.1 fun i => congr_arg Subtype.val (hgl' i)

end subpresheafToTypes

/-- The subsheaf of the sheaf of all dependently typed functions satisfying the local predicate `P`.
-/
@[simps]
/--
Definition of `subsheafToTypes` / `subsheafToTypes` 的定义

English:
definition subsheafToTypes
  signature: (P : LocalPredicate T)
  body: ⟨subpresheafToTypes P.toPrelocalPredicate, subpresheafToTypes.isSheaf P⟩

中文:
定义 subsheafToTypes
  签名: (P : LocalPredicate T)
  定义体: ⟨subpresheafToTypes P.toPrelocalPredicate, subpresheafToTypes.isSheaf P⟩

Depends on / 依赖: P.toPrelocalPredicate, isSheaf, subpresheafToTypes, subpresheafToTypes.isSheaf, toPrelocalPredicate
-/
def subsheafToTypes (P : LocalPredicate T) : Sheaf (Type _) X :=
  ⟨subpresheafToTypes P.toPrelocalPredicate, subpresheafToTypes.isSheaf P⟩

/--
Definition of `LocalPredicate.cocone` / `LocalPredicate.cocone` 的定义

English:
definition LocalPredicate.cocone
  signature: (P : LocalPredicate T) (x : X)
  body: T x
  ι := { app U := ↾fun f => f.1 ⟨x, (unop U).2⟩ }

中文:
定义 LocalPredicate.cocone
  签名: (P : LocalPredicate T) (x : X)
  定义体: T x
  ι := { app U := ↾fun f => f.1 ⟨x, (unop U).2⟩ }
-/
def LocalPredicate.cocone (P : LocalPredicate T) (x : X) :
    Cocone ((OpenNhds.inclusion x).op ⋙ subpresheafToTypes P.toPrelocalPredicate) where
  pt := T x
  ι := { app U := ↾fun f => f.1 ⟨x, (unop U).2⟩ }

/--
Definition of `stalkToFiber` / `stalkToFiber` 的定义

English:
definition stalkToFiber
  signature: (P : LocalPredicate T) (x : X)
  body: colimit.desc _ (P.cocone x)

中文:
定义 stalkToFiber
  签名: (P : LocalPredicate T) (x : X)
  定义体: colimit.desc _ (P.cocone x)

Depends on / 依赖: P.cocone, cocone, colimit, colimit.desc
-/
def stalkToFiber (P : LocalPredicate T) (x : X) :
    (subsheafToTypes P).presheaf.stalk x ⟶ T x :=
  colimit.desc _ (P.cocone x)

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `stalkToFiber_ι` / 引理 `stalkToFiber_ι`

English:
lemma stalkToFiber_ι
  statement: (P : LocalPredicate T) (x : X) (U : (OpenNhds x)ᵒᵖ)
  proof: colimit.ι_desc_apply _ _ _

中文:
引理 stalkToFiber_ι
  结论: (P : LocalPredicate T) (x : X) (U : (OpenNhds x)ᵒᵖ)
  证明: colimit.ι_desc_apply _ _ _

Depends on / 依赖: colimit
-/
lemma stalkToFiber_ι (P : LocalPredicate T) (x : X) (U : (OpenNhds x)ᵒᵖ)
    (fU : {f // P.pred f}) :
    dsimp% (stalkToFiber P x)
      (colimit.ι ((OpenNhds.inclusion x).op ⋙ subpresheafToTypes P.toPrelocalPredicate) U fU) =
      (P.cocone x).ι.app U fU :=
  colimit.ι_desc_apply _ _ _

/--
theorem `stalkToFiber_germ` / 定理 `stalkToFiber_germ`

English:
theorem stalkToFiber_germ
  given: (P : LocalPredicate T) (U : Opens X) (x : X) (hx : x in U) (f)
  proof: by
  dsimp [stalkToFiber, Presheaf.germ]
  exact colimit.ι_desc_apply _ _ _

中文:
定理 stalkToFiber_germ
  条件: (P : LocalPredicate T) (U : Opens X) (x : X) (hx : x in U) (f)
  证明: by
  dsimp [stalkToFiber, Presheaf.germ]
  exact colimit.ι_desc_apply _ _ _

Depends on / 依赖: Presheaf, Presheaf.germ, colimit, stalkToFiber
-/
theorem stalkToFiber_germ (P : LocalPredicate T) (U : Opens X) (x : X) (hx : x in U) (f) :
    stalkToFiber P x ((subsheafToTypes P).presheaf.germ U x hx f) = f.1 ⟨x, hx⟩ := by
  dsimp [stalkToFiber, Presheaf.germ]
  exact colimit.ι_desc_apply _ _ _

/--
theorem `stalkToFiber_surjective` / 定理 `stalkToFiber_surjective`

English:
theorem stalkToFiber_surjective
  statement: (P : LocalPredicate T) (x : X)
  proof: fun t => by
  rcases w t with ⟨U, f, h, rfl⟩
  fconstructor
  · exact (subsheafToTypes P).presheaf.germ _ x U.2 ⟨f, h⟩
  · exact stalkToFiber_germ P U.1 x U.2 ⟨f, h⟩

中文:
定理 stalkToFiber_surjective
  结论: (P : LocalPredicate T) (x : X)
  证明: fun t => by
  rcases w t with ⟨U, f, h, rfl⟩
  fconstructor
  · exact (subsheafToTypes P).presheaf.germ _ x U.2 ⟨f, h⟩
  · exact stalkToFiber_germ P U.1 x U.2 ⟨f, h⟩

Depends on / 依赖: fconstructor, presheaf, presheaf.germ, stalkToFiber_germ, subsheafToTypes
-/
theorem stalkToFiber_surjective (P : LocalPredicate T) (x : X)
    (w : forall t : T x, exists (U : OpenNhds x) (f : forall y : U.1, T y) (_ : P.pred f), f ⟨x, U.2⟩ = t) :
    Function.Surjective (stalkToFiber P x) := fun t => by
  rcases w t with ⟨U, f, h, rfl⟩
  fconstructor
  · exact (subsheafToTypes P).presheaf.germ _ x U.2 ⟨f, h⟩
  · exact stalkToFiber_germ P U.1 x U.2 ⟨f, h⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `stalkToFiber_injective` / 定理 `stalkToFiber_injective`

English:
theorem stalkToFiber_injective
  statement: (P : LocalPredicate T) (x : X)
  proof: fun tU tV h => by
  -- We promise to provide all the ingredients of the proof later:
  let Q :
    exists (W : (OpenNhds x)ᵒᵖ) (s : forall w : (unop W).1, T w) (hW : P.pred s),
      tU = (subsheafToTypes P).presheaf.germ _ x (unop W).2 ⟨s, hW⟩ ∧
        tV = (subsheafToTypes P).presheaf.germ _ x (u

中文:
定理 stalkToFiber_injective
  结论: (P : LocalPredicate T) (x : X)
  证明: fun tU tV h => by
  -- We promise to provide all the ingredients of the proof later:
  let Q :
    exists (W : (OpenNhds x)ᵒᵖ) (s : forall w : (unop W).1, T w) (hW : P.pred s),
      tU = (subsheafToTypes P).presheaf.germ _ x (unop W).2 ⟨s, hW⟩ ∧
        tV = (subsheafToTypes P).presheaf.germ _ x (u
-/
theorem stalkToFiber_injective (P : LocalPredicate T) (x : X)
    (w :
      forall (U V : OpenNhds x) (fU : forall y : U.1, T y) (_ : P.pred fU) (fV : forall y : V.1, T y)
        (_ : P.pred fV) (_ : fU ⟨x, U.2⟩ = fV ⟨x, V.2⟩),
        exists (W : OpenNhds x) (iU : W ⟶ U) (iV : W ⟶ V), forall w : W.1,
          fU (iU w : U.1) = fV (iV w : V.1)) :
    Function.Injective (stalkToFiber P x) := fun tU tV h => by
  -- We promise to provide all the ingredients of the proof later:
  let Q :
    exists (W : (OpenNhds x)ᵒᵖ) (s : forall w : (unop W).1, T w) (hW : P.pred s),
      tU = (subsheafToTypes P).presheaf.germ _ x (unop W).2 ⟨s, hW⟩ ∧
        tV = (subsheafToTypes P).presheaf.germ _ x (unop W).2 ⟨s, hW⟩ :=
    ?_
  · choose W s hW e using Q
    exact e.1.trans e.2.symm
  -- Then use induction to pick particular representatives of `tU tV : stalk x`
  dsimp at tU tV h
  obtain ⟨U, ⟨fU, hU⟩, rfl⟩ := jointly_surjective' tU
  obtain ⟨V, ⟨fV, hV⟩, rfl⟩ := jointly_surjective' tV
  -- Decompose everything into its constituent parts:
  simp only [Functor.whiskeringLeft_obj_obj, Functor.comp_obj, Functor.op_obj,
    subpresheafToTypes_obj, stalkToFiber_ι] at h
  specialize w (unop U) (unop V) fU hU fV hV h
  rcases w with ⟨W, iU, iV, w⟩
  -- and put it back together again in the correct order.
  refine ⟨op W, fun w => fU (iU w : (unop U).1), P.res ?_ _ hU, ?_⟩
  · rcases W with ⟨W, m⟩
    exact iU
  · exact ⟨colimit_sound iU.op (Subtype.ext rfl), colimit_sound iV.op (Subtype.ext (funext w).symm)⟩

universe u

/--
Definition of `subpresheafContinuousPrelocalIsoPresheafToTop` / `subpresheafContinuousPrelocalIsoPresheafToTop` 的定义

English:
definition subpresheafContinuousPrelocalIsoPresheafToTop
  signature: {X : TopCat.{u}} (T : TopCat.{u})
  body: NatIso.ofComponents fun X =>
    { hom := ↾fun f => ofHom ⟨f.1, f.2⟩
      inv := ↾fun f => ⟨f.1, f.1.2⟩ }

中文:
定义 subpresheafContinuousPrelocalIsoPresheafToTop
  签名: {X : 顶元素范畴.{u}} (T : 顶元素范畴.{u})
  定义体: NatIso.ofComponents fun X =>
    { hom := ↾fun f => ofHom ⟨f.1, f.2⟩
      inv := ↾fun f => ⟨f.1, f.1.2⟩ }

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents
-/
def subpresheafContinuousPrelocalIsoPresheafToTop {X : TopCat.{u}} (T : TopCat.{u}) :
    subpresheafToTypes (continuousPrelocal X T) ≅ presheafToTop X T :=
  NatIso.ofComponents fun X =>
    { hom := ↾fun f => ofHom ⟨f.1, f.2⟩
      inv := ↾fun f => ⟨f.1, f.1.2⟩ }

/--
Definition of `sheafToTop` / `sheafToTop` 的定义

English:
definition sheafToTop
  signature: (T : TopCat)
  body: ⟨presheafToTop X T,
    Presheaf.isSheaf_of_iso (subpresheafContinuousPrelocalIsoPresheafToTop T)
      (subpresheafToTypes.isSheaf (continuousLocal X T))⟩

中文:
定义 sheafToTop
  签名: (T : 顶元素范畴)
  定义体: ⟨presheafToTop X T,
    Presheaf.isSheaf_of_iso (subpresheafContinuousPrelocalIsoPresheafToTop T)
      (subpresheafToTypes.isSheaf (continuousLocal X T))⟩

Depends on / 依赖: Presheaf, Presheaf.isSheaf_of_iso, continuousLocal, isSheaf, isSheaf_of_iso, presheafToTop, subpresheafContinuousPrelocalIsoPresheafToTop, subpresheafToTypes, subpresheafToTypes.isSheaf
-/
def sheafToTop (T : TopCat) : Sheaf (Type _) X :=
  ⟨presheafToTop X T,
    Presheaf.isSheaf_of_iso (subpresheafContinuousPrelocalIsoPresheafToTop T)
      (subpresheafToTypes.isSheaf (continuousLocal X T))⟩

end TopCat
