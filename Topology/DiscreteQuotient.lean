/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Adam Topaz
-/
module

public import Mathlib.Data.Setoid.Partition
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!

# Discrete quotients of a topological space.

This file defines the type of discrete quotients of a topological space,
denoted `DiscreteQuotient X`. To avoid quantifying over types, we model such
quotients as setoids whose equivalence classes are clopen.

## Definitions
1. `DiscreteQuotient X` is the type of discrete quotients of `X`.
  It is endowed with a coercion to `Type`, which is defined as the
  quotient associated to the setoid in question, and each such quotient
  is endowed with the discrete topology.
2. Given `S : DiscreteQuotient X`, the projection `X → S` is denoted
  `S.proj`.
3. When `X` is compact and `S : DiscreteQuotient X`, the space `S` is
  endowed with a `Fintype` instance.

## Order structure

The type `DiscreteQuotient X` is endowed with an instance of a `SemilatticeInf` with `OrderTop`.
The partial ordering `A ≤ B` mathematically means that `B.proj` factors through `A.proj`.
The top element `⊤` is the trivial quotient, meaning that every element of `X` is collapsed
to a point. Given `h : A ≤ B`, the map `A → B` is `DiscreteQuotient.ofLE h`.

Whenever `X` is a locally connected space, the type `DiscreteQuotient X` is also endowed with an
instance of an `OrderBot`, where the bot element `⊥` is given by the `connectedComponentSetoid`,
i.e., `x ~ y` means that `x` and `y` belong to the same connected component. In particular, if `X`
is a discrete topological space, then `x ~ y` is equivalent (propositionally, not definitionally) to
`x = y`.

Given `f : C(X, Y)`, we define a predicate `DiscreteQuotient.LEComap f A B` for
`A : DiscreteQuotient X` and `B : DiscreteQuotient Y`, asserting that `f` descends to `A → B`. If
`cond : DiscreteQuotient.LEComap h A B`, the function `A → B` is obtained by
`DiscreteQuotient.map f cond`.

## Theorems

The two main results proved in this file are:

1. `DiscreteQuotient.eq_of_forall_proj_eq` which states that when `X` is compact, T₂, and totally
  disconnected, any two elements of `X` are equal if their projections in `Q` agree for all
  `Q : DiscreteQuotient X`.

2. `DiscreteQuotient.exists_of_compat` which states that when `X` is compact, then any
  system of elements of `Q` as `Q : DiscreteQuotient X` varies, which is compatible with
  respect to `DiscreteQuotient.ofLE`, must arise from some element of `X`.

## Remarks
The constructions in this file will be used to show that any profinite space is a limit
of finite discrete spaces.
-/

@[expose] public section


open Set Function TopologicalSpace Topology

variable {α X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The type of discrete quotients of a topological space. -/
@[ext]
/--
Definition of `DiscreteQuotient` / `DiscreteQuotient` 的定义

English:
structure DiscreteQuotient
  parameters: (X : Type*) [TopologicalSpace X]
  extends: Setoid X
  axioms and operations (1):
    - isOpen_setOfPred_rel : forall x, IsOpen (Set.ofPred (toSetoid x))

中文:
结构 DiscreteQuotient
  参数: (X : 类型) [拓扑空间 X]
  继承: 集合等价关系 X
  公理与运算 (1 个):
    - isOpen_setOfPred_rel : 对任意 x, 是开集 (集合.ofPred (toSetoid x))
-/
structure DiscreteQuotient (X : Type*) [TopologicalSpace X] extends Setoid X where
  /-- For every point `x`, the set `{ y | Rel x y }` is an open set. -/
  protected isOpen_setOfPred_rel : forall x, IsOpen (Set.ofPred (toSetoid x))

namespace DiscreteQuotient

variable (S : DiscreteQuotient X)

@[deprecated (since := "2026-07-09")]
protected alias isOpen_setOf_rel := DiscreteQuotient.isOpen_setOfPred_rel

/--
lemma `toSetoid_injective` / 引理 `toSetoid_injective`

English:
lemma toSetoid_injective
  statement: Function.Injective (@toSetoid X _)

中文:
引理 toSetoid_injective
  结论: 函数.单射 (@toSetoid X _)
-/
lemma toSetoid_injective : Function.Injective (@toSetoid X _)
  | ⟨_, _⟩, ⟨_, _⟩, _ => by congr

/--
Definition of `ofIsClopen` / `ofIsClopen` 的定义

English:
definition ofIsClopen
  signature: {A : Set X} (h : IsClopen A)
  body: ⟨fun x y => x in A ↔ y in A, fun _ => Iff.rfl, Iff.symm, Iff.trans⟩
  isOpen_setOfPred_rel x := by by_cases hx : x in A <;> simp [hx, h.1, h.2, ← compl_ofPred]

中文:
定义 ofIsClopen
  签名: {A : 集合 X} (h : IsClopen A)
  定义体: ⟨fun x y => x in A ↔ y in A, fun _ => Iff.rfl, Iff.symm, Iff.trans⟩
  isOpen_setOfPred_rel x := by by_cases hx : x in A <;> simp [hx, h.1, h.2, ← compl_ofPred]

Depends on / 依赖: Iff.rfl, Iff.symm, Iff.trans
-/
def ofIsClopen {A : Set X} (h : IsClopen A) : DiscreteQuotient X where
  toSetoid := ⟨fun x y => x in A ↔ y in A, fun _ => Iff.rfl, Iff.symm, Iff.trans⟩
  isOpen_setOfPred_rel x := by by_cases hx : x in A <;> simp [hx, h.1, h.2, ← compl_ofPred]

/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  statement: forall x, S.toSetoid x x
  proof: S.refl'

中文:
定理 refl
  结论: 对任意 x, S.toSetoid x x
  证明: S.refl'

Depends on / 依赖: S.refl
-/
theorem refl : forall x, S.toSetoid x x := S.refl'

/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: (x y : X)
  statement: S.toSetoid x y -> S.toSetoid y x
  proof: S.symm'

中文:
定理 symm
  条件: (x y : X)
  结论: S.toSetoid x y -> S.toSetoid y x
  证明: S.symm'

Depends on / 依赖: S.symm
-/
theorem symm (x y : X) : S.toSetoid x y -> S.toSetoid y x := S.symm'

/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: (x y z : X)
  statement: S.toSetoid x y -> S.toSetoid y z -> S.toSetoid x z
  proof: S.trans'

中文:
定理 trans
  条件: (x y z : X)
  结论: S.toSetoid x y -> S.toSetoid y z -> S.toSetoid x z
  证明: S.trans'

Depends on / 依赖: S.trans
-/
theorem trans (x y z : X) : S.toSetoid x y -> S.toSetoid y z -> S.toSetoid x z := S.trans'

/-- The setoid whose quotient yields the discrete quotient. -/
add_decl_doc toSetoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (DiscreteQuotient X) (Type _)
  body: ⟨fun S => Quotient S.toSetoid⟩

中文:
实例 :
  签名: CoeSort (DiscreteQuotient X) (类型 _)
  定义体: ⟨fun S => Quotient S.toSetoid⟩

Depends on / 依赖: Quotient, S.toSetoid, toSetoid
-/
instance : CoeSort (DiscreteQuotient X) (Type _) :=
  ⟨fun S => Quotient S.toSetoid⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace S
  body: inferInstanceAs (TopologicalSpace (Quotient S.toSetoid))

中文:
实例 :
  签名: 拓扑空间 S
  定义体: inferInstanceAs (TopologicalSpace (Quotient S.toSetoid))

Depends on / 依赖: Quotient, S.toSetoid, TopologicalSpace, toSetoid
-/
instance : TopologicalSpace S :=
  inferInstanceAs (TopologicalSpace (Quotient S.toSetoid))

/--
Definition of `proj` / `proj` 的定义

English:
definition proj
  signature: : X -> S
  body: Quotient.mk''

中文:
定义 proj
  签名: : X -> S
  定义体: Quotient.mk''

Depends on / 依赖: Quotient, Quotient.mk
-/
def proj : X -> S := Quotient.mk''

/--
theorem `fiber_eq` / 定理 `fiber_eq`

English:
theorem fiber_eq
  given: (x : X)
  statement: S.proj ⁻¹' {S.proj x} = Set.ofPred (S.toSetoid x)
  proof: Set.ext fun _ => eq_comm.trans Quotient.eq''

中文:
定理 fiber_eq
  条件: (x : X)
  结论: S.proj ⁻¹' {S.proj x} = 集合.ofPred (S.toSetoid x)
  证明: Set.ext fun _ => eq_comm.trans Quotient.eq''

Depends on / 依赖: Quotient, Quotient.eq, Set.ext, eq_comm, eq_comm.trans
-/
theorem fiber_eq (x : X) : S.proj ⁻¹' {S.proj x} = Set.ofPred (S.toSetoid x) :=
  Set.ext fun _ => eq_comm.trans Quotient.eq''

/--
theorem `proj_surjective` / 定理 `proj_surjective`

English:
theorem proj_surjective
  statement: Function.Surjective S.proj
  proof: Quotient.mk''_surjective

中文:
定理 proj_surjective
  结论: 函数.满射 S.proj
  证明: Quotient.mk''_surjective

Depends on / 依赖: Quotient, Quotient.mk, _surjective
-/
theorem proj_surjective : Function.Surjective S.proj :=
  Quotient.mk''_surjective

/--
theorem `proj_isQuotientMap` / 定理 `proj_isQuotientMap`

English:
theorem proj_isQuotientMap
  statement: IsQuotientMap S.proj
  proof: isQuotientMap_quot_mk

中文:
定理 proj_isQuotientMap
  结论: 是商映射 S.proj
  证明: isQuotientMap_quot_mk

Depends on / 依赖: isQuotientMap_quot_mk
-/
theorem proj_isQuotientMap : IsQuotientMap S.proj :=
  isQuotientMap_quot_mk

/--
theorem `proj_continuous` / 定理 `proj_continuous`

English:
theorem proj_continuous
  statement: Continuous S.proj
  proof: S.proj_isQuotientMap.continuous

中文:
定理 proj_continuous
  结论: 连续 S.proj
  证明: S.proj_isQuotientMap.continuous

Depends on / 依赖: S.proj_isQuotientMap.continuous, continuous, proj_isQuotientMap
-/
theorem proj_continuous : Continuous S.proj :=
  S.proj_isQuotientMap.continuous

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DiscreteTopology S
  body: discreteTopology_iff_isOpen_singleton.2 S.proj_surjective.forall.2 fun x => by
    rw [← S.proj_isQuotientMap.isOpen_preimage]; rw [fiber_eq]
    exact S.isOpen_setOfPred_rel _

中文:
实例 :
  签名: 离散拓扑 S
  定义体: discreteTopology_iff_isOpen_singleton.2 S.proj_surjective.forall.2 fun x => by
    rw [← S.proj_isQuotientMap.isOpen_preimage]; rw [fiber_eq]
    exact S.isOpen_setOfPred_rel _

Depends on / 依赖: S.isOpen_setOfPred_rel, S.proj_isQuotientMap.isOpen_preimage, S.proj_surjective.forall, discreteTopology_iff_isOpen_singleton, fiber_eq, isOpen_preimage, isOpen_setOfPred_rel, proj_isQuotientMap, proj_surjective
-/
instance : DiscreteTopology S :=
discreteTopology_iff_isOpen_singleton.2 S.proj_surjective.forall.2 fun x => by
    rw [← S.proj_isQuotientMap.isOpen_preimage]; rw [fiber_eq]
    exact S.isOpen_setOfPred_rel _

/--
theorem `proj_isLocallyConstant` / 定理 `proj_isLocallyConstant`

English:
theorem proj_isLocallyConstant
  statement: IsLocallyConstant S.proj
  proof: (IsLocallyConstant.iff_continuous S.proj).2 S.proj_continuous

中文:
定理 proj_isLocallyConstant
  结论: IsLocallyConstant S.proj
  证明: (IsLocallyConstant.iff_continuous S.proj).2 S.proj_continuous

Depends on / 依赖: IsLocallyConstant, IsLocallyConstant.iff_continuous, S.proj, S.proj_continuous, iff_continuous, proj_continuous
-/
theorem proj_isLocallyConstant : IsLocallyConstant S.proj :=
  (IsLocallyConstant.iff_continuous S.proj).2 S.proj_continuous

/--
theorem `isClopen_preimage` / 定理 `isClopen_preimage`

English:
theorem isClopen_preimage
  given: (A : Set S)
  statement: IsClopen (S.proj ⁻¹' A)
  proof: (isClopen_discrete A).preimage S.proj_continuous

中文:
定理 isClopen_preimage
  条件: (A : 集合 S)
  结论: IsClopen (S.proj ⁻¹' A)
  证明: (isClopen_discrete A).preimage S.proj_continuous

Depends on / 依赖: S.proj_continuous, isClopen_discrete, preimage, proj_continuous
-/
theorem isClopen_preimage (A : Set S) : IsClopen (S.proj ⁻¹' A) :=
  (isClopen_discrete A).preimage S.proj_continuous

/--
theorem `isOpen_preimage` / 定理 `isOpen_preimage`

English:
theorem isOpen_preimage
  given: (A : Set S)
  statement: IsOpen (S.proj ⁻¹' A)
  proof: (S.isClopen_preimage A).2

中文:
定理 isOpen_preimage
  条件: (A : 集合 S)
  结论: 是开集 (S.proj ⁻¹' A)
  证明: (S.isClopen_preimage A).2

Depends on / 依赖: S.isClopen_preimage, isClopen_preimage
-/
theorem isOpen_preimage (A : Set S) : IsOpen (S.proj ⁻¹' A) :=
  (S.isClopen_preimage A).2

/--
theorem `isClosed_preimage` / 定理 `isClosed_preimage`

English:
theorem isClosed_preimage
  given: (A : Set S)
  statement: IsClosed (S.proj ⁻¹' A)
  proof: (S.isClopen_preimage A).1

中文:
定理 isClosed_preimage
  条件: (A : 集合 S)
  结论: 是闭集 (S.proj ⁻¹' A)
  证明: (S.isClopen_preimage A).1

Depends on / 依赖: S.isClopen_preimage, isClopen_preimage
-/
theorem isClosed_preimage (A : Set S) : IsClosed (S.proj ⁻¹' A) :=
  (S.isClopen_preimage A).1

/--
theorem `isClopen_setOfPred_rel` / 定理 `isClopen_setOfPred_rel`

English:
theorem isClopen_setOfPred_rel
  given: (x : X)
  statement: IsClopen (Set.ofPred (S.toSetoid x))
  proof: by
  rw [← fiber_eq]
  apply isClopen_preimage

@[deprecated (since := "2026-07-09")]
alias isClopen_setOf_rel := isClopen_setOfPred_rel

中文:
定理 isClopen_setOfPred_rel
  条件: (x : X)
  结论: IsClopen (集合.ofPred (S.toSetoid x))
  证明: by
  rw [← fiber_eq]
  apply isClopen_preimage

@[deprecated (since := "2026-07-09")]
alias isClopen_setOf_rel := isClopen_setOfPred_rel

Depends on / 依赖: fiber_eq, isClopen_preimage
-/
theorem isClopen_setOfPred_rel (x : X) : IsClopen (Set.ofPred (S.toSetoid x)) := by
  rw [← fiber_eq]
  apply isClopen_preimage

@[deprecated (since := "2026-07-09")]
alias isClopen_setOf_rel := isClopen_setOfPred_rel

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (DiscreteQuotient X)
  body: ⟨fun S₁ S₂ => ⟨S₁.1 ⊓ S₂.1, fun x => (S₁.2 x).inter (S₂.2 x)⟩⟩

中文:
实例 :
  签名: 最小值 (DiscreteQuotient X)
  定义体: ⟨fun S₁ S₂ => ⟨S₁.1 ⊓ S₂.1, fun x => (S₁.2 x).inter (S₂.2 x)⟩⟩
-/
instance : Min (DiscreteQuotient X) :=
  ⟨fun S₁ S₂ => ⟨S₁.1 ⊓ S₂.1, fun x => (S₁.2 x).inter (S₂.2 x)⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (DiscreteQuotient X)
  body: PartialOrder.lift _ toSetoid_injective

中文:
实例 :
  签名: 偏序 (DiscreteQuotient X)
  定义体: PartialOrder.lift _ toSetoid_injective

Depends on / 依赖: PartialOrder, PartialOrder.lift, toSetoid_injective
-/
instance : PartialOrder (DiscreteQuotient X) :=
  PartialOrder.lift _ toSetoid_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeInf (DiscreteQuotient X)
  body: toSetoid_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

中文:
实例 :
  签名: SemilatticeInf (DiscreteQuotient X)
  定义体: toSetoid_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

Depends on / 依赖: semilatticeInf, toSetoid_injective, toSetoid_injective.semilatticeInf
-/
instance : SemilatticeInf (DiscreteQuotient X) :=
  toSetoid_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTop (DiscreteQuotient X)
  body: ⟨⊤, fun _ => isOpen_univ⟩
  le_top a := by tauto

中文:
实例 :
  签名: 有顶序 (DiscreteQuotient X)
  定义体: ⟨⊤, fun _ => isOpen_univ⟩
  le_top a := by tauto

Depends on / 依赖: isOpen_univ
-/
instance : OrderTop (DiscreteQuotient X) where
  top := ⟨⊤, fun _ => isOpen_univ⟩
  le_top a := by tauto

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (DiscreteQuotient X)
  body: ⟨⊤⟩

中文:
实例 :
  签名: 可居 (DiscreteQuotient X)
  定义体: ⟨⊤⟩
-/
instance : Inhabited (DiscreteQuotient X) := ⟨⊤⟩

/--
Instance `inhabitedQuotient` / 实例 `inhabitedQuotient`

English:
instance inhabitedQuotient
  signature: [Inhabited X]
  body: ⟨S.proj default⟩

中文:
实例 inhabitedQuotient
  签名: [可居 X]
  定义体: ⟨S.proj default⟩

Depends on / 依赖: S.proj
-/
instance inhabitedQuotient [Inhabited X] : Inhabited S := ⟨S.proj default⟩

-- TODO: add instances about `Nonempty (Quot _)`/`Nonempty (Quotient _)`
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: X] : Nonempty S
  body: Nonempty.map S.proj ‹_›

中文:
实例 [非空
  签名: X] : 非空 S
  定义体: Nonempty.map S.proj ‹_›

Depends on / 依赖: Nonempty, Nonempty.map, S.proj
-/
instance [Nonempty X] : Nonempty S := Nonempty.map S.proj ‹_›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (⊤ : DiscreteQuotient X)
  body: by rintro ⟨_⟩ ⟨_⟩; exact Quotient.sound trivial

中文:
实例 :
  签名: 子单例 (⊤ : DiscreteQuotient X)
  定义体: by rintro ⟨_⟩ ⟨_⟩; exact Quotient.sound trivial

Depends on / 依赖: Quotient, Quotient.sound
-/
instance : Subsingleton (⊤ : DiscreteQuotient X) where
  allEq := by rintro ⟨_⟩ ⟨_⟩; exact Quotient.sound trivial

section Comap

variable (g : C(Y, Z)) (f : C(X, Y))

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (S : DiscreteQuotient Y)
  body: Setoid.comap f S.1
  isOpen_setOfPred_rel _ := (S.2 _).preimage f.continuous

@[simp]

中文:
定义 comap
  签名: (S : DiscreteQuotient Y)
  定义体: Setoid.comap f S.1
  isOpen_setOfPred_rel _ := (S.2 _).preimage f.continuous

@[simp]

Depends on / 依赖: Setoid, Setoid.comap
-/
def comap (S : DiscreteQuotient Y) : DiscreteQuotient X where
  toSetoid := Setoid.comap f S.1
  isOpen_setOfPred_rel _ := (S.2 _).preimage f.continuous

@[simp]
/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  statement: S.comap (ContinuousMap.id X) = S
  proof: rfl

@[simp]

中文:
定理 comap_id
  结论: S.comap (连续映射.id X) = S
  证明: rfl

@[simp]
-/
theorem comap_id : S.comap (ContinuousMap.id X) = S := rfl

@[simp]
/--
theorem `comap_comp` / 定理 `comap_comp`

English:
theorem comap_comp
  given: (S : DiscreteQuotient Z)
  statement: S.comap (g.comp f) = (S.comap g).comap f
  proof: rfl

@[gcongr, mono]

中文:
定理 comap_comp
  条件: (S : DiscreteQuotient Z)
  结论: S.comap (g.comp f) = (S.comap g).comap f
  证明: rfl

@[gcongr, mono]
-/
theorem comap_comp (S : DiscreteQuotient Z) : S.comap (g.comp f) = (S.comap g).comap f :=
  rfl

@[gcongr, mono]
/--
theorem `comap_mono` / 定理 `comap_mono`

English:
theorem comap_mono
  given: {A B : DiscreteQuotient Y} (h : A <= B)
  statement: A.comap f <= B.comap f
  proof: by tauto

中文:
定理 comap_mono
  条件: {A B : DiscreteQuotient Y} (h : A <= B)
  结论: A.comap f <= B.comap f
  证明: by tauto
-/
theorem comap_mono {A B : DiscreteQuotient Y} (h : A <= B) : A.comap f <= B.comap f := by tauto

end Comap

section OfLE

variable {A B C : DiscreteQuotient X}

/--
Definition of `ofLE` / `ofLE` 的定义

English:
definition ofLE
  signature: (h : A <= B)
  body: Quotient.map' id h

@[simp]

中文:
定义 ofLE
  签名: (h : A <= B)
  定义体: Quotient.map' id h

@[simp]

Depends on / 依赖: Quotient, Quotient.map
-/
def ofLE (h : A <= B) : A -> B :=
  Quotient.map' id h

@[simp]
/--
theorem `ofLE_refl` / 定理 `ofLE_refl`

English:
theorem ofLE_refl
  statement: ofLE (le_refl A) = id
  proof: by
  ext ⟨⟩
  rfl

中文:
定理 ofLE_refl
  结论: ofLE (le_refl A) = id
  证明: by
  ext ⟨⟩
  rfl
-/
theorem ofLE_refl : ofLE (le_refl A) = id := by
  ext ⟨⟩
  rfl

/--
theorem `ofLE_refl_apply` / 定理 `ofLE_refl_apply`

English:
theorem ofLE_refl_apply
  given: (a : A)
  statement: ofLE (le_refl A) a = a
  proof: by simp

@[simp]

中文:
定理 ofLE_refl_apply
  条件: (a : A)
  结论: ofLE (le_refl A) a = a
  证明: by simp

@[simp]
-/
theorem ofLE_refl_apply (a : A) : ofLE (le_refl A) a = a := by simp

@[simp]
/--
theorem `ofLE_ofLE` / 定理 `ofLE_ofLE`

English:
theorem ofLE_ofLE
  given: (h₁ : A <= B) (h₂ : B <= C) (x : A)
  proof: by
  rcases x with ⟨⟩
  rfl

@[simp]

中文:
定理 ofLE_ofLE
  条件: (h₁ : A <= B) (h₂ : B <= C) (x : A)
  证明: by
  rcases x with ⟨⟩
  rfl

@[simp]
-/
theorem ofLE_ofLE (h₁ : A <= B) (h₂ : B <= C) (x : A) :
    ofLE h₂ (ofLE h₁ x) = ofLE (h₁.trans h₂) x := by
  rcases x with ⟨⟩
  rfl

@[simp]
/--
theorem `ofLE_comp_ofLE` / 定理 `ofLE_comp_ofLE`

English:
theorem ofLE_comp_ofLE
  given: (h₁ : A <= B) (h₂ : B <= C)
  statement: ofLE h₂ ∘ ofLE h₁ = ofLE (le_trans h₁ h₂)
  proof: funext ofLE_ofLE _ _

中文:
定理 ofLE_comp_ofLE
  条件: (h₁ : A <= B) (h₂ : B <= C)
  结论: ofLE h₂ ∘ ofLE h₁ = ofLE (le_trans h₁ h₂)
  证明: funext ofLE_ofLE _ _

Depends on / 依赖: ofLE_ofLE
-/
theorem ofLE_comp_ofLE (h₁ : A <= B) (h₂ : B <= C) : ofLE h₂ ∘ ofLE h₁ = ofLE (le_trans h₁ h₂) :=
funext ofLE_ofLE _ _

/--
theorem `ofLE_continuous` / 定理 `ofLE_continuous`

English:
theorem ofLE_continuous
  given: (h : A <= B)
  statement: Continuous (ofLE h)
  proof: continuous_of_discreteTopology

@[simp]

中文:
定理 ofLE_continuous
  条件: (h : A <= B)
  结论: 连续 (ofLE h)
  证明: continuous_of_discreteTopology

@[simp]

Depends on / 依赖: continuous_of_discreteTopology
-/
theorem ofLE_continuous (h : A <= B) : Continuous (ofLE h) :=
  continuous_of_discreteTopology

@[simp]
/--
theorem `ofLE_proj` / 定理 `ofLE_proj`

English:
theorem ofLE_proj
  given: (h : A <= B) (x : X)
  statement: ofLE h (A.proj x) = B.proj x
  proof: Quotient.sound' (B.refl _)

@[simp]

中文:
定理 ofLE_proj
  条件: (h : A <= B) (x : X)
  结论: ofLE h (A.proj x) = B.proj x
  证明: Quotient.sound' (B.refl _)

@[simp]

Depends on / 依赖: B.refl, Quotient, Quotient.sound
-/
theorem ofLE_proj (h : A <= B) (x : X) : ofLE h (A.proj x) = B.proj x :=
  Quotient.sound' (B.refl _)

@[simp]
/--
theorem `ofLE_comp_proj` / 定理 `ofLE_comp_proj`

English:
theorem ofLE_comp_proj
  given: (h : A <= B)
  statement: ofLE h ∘ A.proj = B.proj
  proof: funext ofLE_proj _

中文:
定理 ofLE_comp_proj
  条件: (h : A <= B)
  结论: ofLE h ∘ A.proj = B.proj
  证明: funext ofLE_proj _

Depends on / 依赖: ofLE_proj
-/
theorem ofLE_comp_proj (h : A <= B) : ofLE h ∘ A.proj = B.proj :=
funext ofLE_proj _

end OfLE

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LocallyConnectedSpace
  signature: X] : OrderBot (DiscreteQuotient X) where
  body: { toSetoid := connectedComponentSetoid X
      isOpen_setOfPred_rel := fun x => by
        convert! isOpen_connectedComponent (x := x)
        ext y
        simpa only [connectedComponentSetoid, ← connectedComponent_eq_iff_mem] using! eq_comm }
  bot_le S := fun x y (h : connectedComponent x = connectedComponent y) =>
(S.isClopen_setOfPred_rel x).connectedComponent_subset (S.refl _)
      h.symm ▸ mem_connectedComponent

@[simp]

中文:
实例 [局部连通空间
  签名: X] : 有底序 (DiscreteQuotient X) where
  定义体: { toSetoid := connectedComponentSetoid X
      isOpen_setOfPred_rel := fun x => by
        convert! isOpen_connectedComponent (x := x)
        ext y
        simpa only [connectedComponentSetoid, ← connectedComponent_eq_iff_mem] using! eq_comm }
  bot_le S := fun x y (h : connectedComponent x = connectedComponent y) =>
(S.isClopen_setOfPred_rel x).connectedComponent_subset (S.refl _)
      h.symm ▸ mem_connectedComponent

@[simp]

Depends on / 依赖: S.isClopen_setOfPred_rel, S.refl, bot_le, connectedComponent, connectedComponentSetoid, connectedComponent_eq_iff_mem, connectedComponent_subset, convert, eq_comm, h.symm, isClopen_setOfPred_rel, isOpen_connectedComponent, isOpen_setOfPred_rel, mem_connectedComponent, toSetoid
-/
instance [LocallyConnectedSpace X] : OrderBot (DiscreteQuotient X) where
  bot :=
    { toSetoid := connectedComponentSetoid X
      isOpen_setOfPred_rel := fun x => by
        convert! isOpen_connectedComponent (x := x)
        ext y
        simpa only [connectedComponentSetoid, ← connectedComponent_eq_iff_mem] using! eq_comm }
  bot_le S := fun x y (h : connectedComponent x = connectedComponent y) =>
(S.isClopen_setOfPred_rel x).connectedComponent_subset (S.refl _)
      h.symm ▸ mem_connectedComponent

@[simp]
/--
theorem `proj_bot_eq` / 定理 `proj_bot_eq`

English:
theorem proj_bot_eq
  given: [LocallyConnectedSpace X] {x y : X}
  proof: Quotient.eq''

中文:
定理 proj_bot_eq
  条件: [局部连通空间 X] {x y : X}
  证明: Quotient.eq''

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem proj_bot_eq [LocallyConnectedSpace X] {x y : X} :
    proj ⊥ x = proj ⊥ y ↔ connectedComponent x = connectedComponent y :=
  Quotient.eq''

/--
theorem `proj_bot_inj` / 定理 `proj_bot_inj`

English:
theorem proj_bot_inj
  given: [DiscreteTopology X] {x y : X}
  statement: proj ⊥ x = proj ⊥ y ↔ x = y
  proof: by simp

中文:
定理 proj_bot_inj
  条件: [离散拓扑 X] {x y : X}
  结论: proj ⊥ x = proj ⊥ y ↔ x = y
  证明: by simp
-/
theorem proj_bot_inj [DiscreteTopology X] {x y : X} : proj ⊥ x = proj ⊥ y ↔ x = y := by simp

/--
theorem `proj_bot_injective` / 定理 `proj_bot_injective`

English:
theorem proj_bot_injective
  given: [DiscreteTopology X]
  statement: Injective (⊥ : DiscreteQuotient X).proj
  proof: fun _ _ => proj_bot_inj.1

中文:
定理 proj_bot_injective
  条件: [离散拓扑 X]
  结论: 单射 (⊥ : DiscreteQuotient X).proj
  证明: fun _ _ => proj_bot_inj.1

Depends on / 依赖: proj_bot_inj
-/
theorem proj_bot_injective [DiscreteTopology X] : Injective (⊥ : DiscreteQuotient X).proj :=
  fun _ _ => proj_bot_inj.1

/--
theorem `proj_bot_bijective` / 定理 `proj_bot_bijective`

English:
theorem proj_bot_bijective
  given: [DiscreteTopology X]
  statement: Bijective (⊥ : DiscreteQuotient X).proj
  proof: ⟨proj_bot_injective, proj_surjective _⟩

中文:
定理 proj_bot_bijective
  条件: [离散拓扑 X]
  结论: 双射 (⊥ : DiscreteQuotient X).proj
  证明: ⟨proj_bot_injective, proj_surjective _⟩

Depends on / 依赖: proj_bot_injective, proj_surjective
-/
theorem proj_bot_bijective [DiscreteTopology X] : Bijective (⊥ : DiscreteQuotient X).proj :=
  ⟨proj_bot_injective, proj_surjective _⟩

section Map

variable (f : C(X, Y)) (A A' : DiscreteQuotient X) (B B' : DiscreteQuotient Y)

/--
Definition of `LEComap` / `LEComap` 的定义

English:
definition LEComap
  signature: : Prop
  body: A <= B.comap f

中文:
定义 LEComap
  签名: : 命题
  定义体: A <= B.comap f

Depends on / 依赖: B.comap
-/
def LEComap : Prop :=
  A <= B.comap f

/--
theorem `leComap_id` / 定理 `leComap_id`

English:
theorem leComap_id
  statement: LEComap (.id X) A A
  proof: le_rfl

中文:
定理 leComap_id
  结论: LEComap (.id X) A A
  证明: le_rfl

Depends on / 依赖: le_rfl
-/
theorem leComap_id : LEComap (.id X) A A := le_rfl

variable {A A' B B'} {f} {g : C(Y, Z)} {C : DiscreteQuotient Z}

@[simp]
/--
theorem `leComap_id_iff` / 定理 `leComap_id_iff`

English:
theorem leComap_id_iff
  statement: LEComap (ContinuousMap.id X) A A' ↔ A <= A'
  proof: Iff.rfl

中文:
定理 leComap_id_iff
  结论: LEComap (连续映射.id X) A A' ↔ A <= A'
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem leComap_id_iff : LEComap (ContinuousMap.id X) A A' ↔ A <= A' :=
  Iff.rfl

/--
theorem `LEComap.comp` / 定理 `LEComap.comp`

English:
theorem LEComap.comp
  statement: LEComap g B C -> LEComap f A B -> LEComap (g.comp f) A C
  proof: by tauto

@[gcongr, mono]

中文:
定理 LEComap.comp
  结论: LEComap g B C -> LEComap f A B -> LEComap (g.comp f) A C
  证明: by tauto

@[gcongr, mono]
-/
theorem LEComap.comp : LEComap g B C -> LEComap f A B -> LEComap (g.comp f) A C := by tauto

@[gcongr, mono]
/--
theorem `LEComap.mono` / 定理 `LEComap.mono`

English:
theorem LEComap.mono
  given: (h : LEComap f A B) (hA : A' <= A) (hB : B <= B')
  statement: LEComap f A' B'
  proof: hA.trans h.trans comap_mono _ hB

中文:
定理 LEComap.mono
  条件: (h : LEComap f A B) (hA : A' <= A) (hB : B <= B')
  结论: LEComap f A' B'
  证明: hA.trans h.trans comap_mono _ hB

Depends on / 依赖: comap_mono, h.trans, hA.trans
-/
theorem LEComap.mono (h : LEComap f A B) (hA : A' <= A) (hB : B <= B') : LEComap f A' B' :=
hA.trans h.trans comap_mono _ hB

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : C(X, Y)) (cond : LEComap f A B)
  body: Quotient.map' f cond

中文:
定义 map
  签名: (f : C(X, Y)) (cond : LEComap f A B)
  定义体: Quotient.map' f cond

Depends on / 依赖: Quotient, Quotient.map
-/
def map (f : C(X, Y)) (cond : LEComap f A B) : A -> B := Quotient.map' f cond

/--
theorem `map_continuous` / 定理 `map_continuous`

English:
theorem map_continuous
  given: (cond : LEComap f A B)
  statement: Continuous (map f cond)
  proof: continuous_of_discreteTopology

@[simp]

中文:
定理 map_continuous
  条件: (cond : LEComap f A B)
  结论: 连续 (map f cond)
  证明: continuous_of_discreteTopology

@[simp]

Depends on / 依赖: continuous_of_discreteTopology
-/
theorem map_continuous (cond : LEComap f A B) : Continuous (map f cond) :=
  continuous_of_discreteTopology

@[simp]
/--
theorem `map_comp_proj` / 定理 `map_comp_proj`

English:
theorem map_comp_proj
  given: (cond : LEComap f A B)
  statement: map f cond ∘ A.proj = B.proj ∘ f
  proof: rfl

@[simp]

中文:
定理 map_comp_proj
  条件: (cond : LEComap f A B)
  结论: map f cond ∘ A.proj = B.proj ∘ f
  证明: rfl

@[simp]
-/
theorem map_comp_proj (cond : LEComap f A B) : map f cond ∘ A.proj = B.proj ∘ f :=
  rfl

@[simp]
/--
theorem `map_proj` / 定理 `map_proj`

English:
theorem map_proj
  given: (cond : LEComap f A B) (x : X)
  statement: map f cond (A.proj x) = B.proj (f x)
  proof: rfl

@[simp]

中文:
定理 map_proj
  条件: (cond : LEComap f A B) (x : X)
  结论: map f cond (A.proj x) = B.proj (f x)
  证明: rfl

@[simp]
-/
theorem map_proj (cond : LEComap f A B) (x : X) : map f cond (A.proj x) = B.proj (f x) :=
  rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map _ (leComap_id A) = id
  proof: by ext ⟨⟩; rfl

中文:
定理 map_id
  结论: map _ (leComap_id A) = id
  证明: by ext ⟨⟩; rfl
-/
theorem map_id : map _ (leComap_id A) = id := by ext ⟨⟩; rfl

-- This can't be a `@[simp]` lemma since `h1` and `h2` can't be found by unification in a Prop.
/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: (h1 : LEComap g B C) (h2 : LEComap f A B)
  proof: by
  ext ⟨⟩
  rfl

@[simp]

中文:
定理 map_comp
  条件: (h1 : LEComap g B C) (h2 : LEComap f A B)
  证明: by
  ext ⟨⟩
  rfl

@[simp]
-/
theorem map_comp (h1 : LEComap g B C) (h2 : LEComap f A B) :
    map (g.comp f) (h1.comp h2) = map g h1 ∘ map f h2 := by
  ext ⟨⟩
  rfl

@[simp]
/--
theorem `ofLE_map` / 定理 `ofLE_map`

English:
theorem ofLE_map
  given: (cond : LEComap f A B) (h : B <= B') (a : A)
  proof: by
  rcases a with ⟨⟩
  rfl

@[simp]

中文:
定理 ofLE_map
  条件: (cond : LEComap f A B) (h : B <= B') (a : A)
  证明: by
  rcases a with ⟨⟩
  rfl

@[simp]
-/
theorem ofLE_map (cond : LEComap f A B) (h : B <= B') (a : A) :
    ofLE h (map f cond a) = map f (cond.mono le_rfl h) a := by
  rcases a with ⟨⟩
  rfl

@[simp]
/--
theorem `ofLE_comp_map` / 定理 `ofLE_comp_map`

English:
theorem ofLE_comp_map
  given: (cond : LEComap f A B) (h : B <= B')
  proof: funext ofLE_map cond h

@[simp]

中文:
定理 ofLE_comp_map
  条件: (cond : LEComap f A B) (h : B <= B')
  证明: funext ofLE_map cond h

@[simp]

Depends on / 依赖: ofLE_map
-/
theorem ofLE_comp_map (cond : LEComap f A B) (h : B <= B') :
    ofLE h ∘ map f cond = map f (cond.mono le_rfl h) :=
funext ofLE_map cond h

@[simp]
/--
theorem `map_ofLE` / 定理 `map_ofLE`

English:
theorem map_ofLE
  given: (cond : LEComap f A B) (h : A' <= A) (c : A')
  proof: by
  rcases c with ⟨⟩
  rfl

@[simp]

中文:
定理 map_ofLE
  条件: (cond : LEComap f A B) (h : A' <= A) (c : A')
  证明: by
  rcases c with ⟨⟩
  rfl

@[simp]
-/
theorem map_ofLE (cond : LEComap f A B) (h : A' <= A) (c : A') :
    map f cond (ofLE h c) = map f (cond.mono h le_rfl) c := by
  rcases c with ⟨⟩
  rfl

@[simp]
/--
theorem `map_comp_ofLE` / 定理 `map_comp_ofLE`

English:
theorem map_comp_ofLE
  given: (cond : LEComap f A B) (h : A' <= A)
  proof: funext map_ofLE cond h

中文:
定理 map_comp_ofLE
  条件: (cond : LEComap f A B) (h : A' <= A)
  证明: funext map_ofLE cond h

Depends on / 依赖: map_ofLE
-/
theorem map_comp_ofLE (cond : LEComap f A B) (h : A' <= A) :
    map f cond ∘ ofLE h = map f (cond.mono h le_rfl) :=
funext map_ofLE cond h

end Map

/--
theorem `eq_of_forall_proj_eq` / 定理 `eq_of_forall_proj_eq`

English:
theorem eq_of_forall_proj_eq
  statement: [T2Space X] [CompactSpace X] [disc : TotallyDisconnectedSpace X]
  proof: by
  rw [← mem_singleton_iff]; rw [← connectedComponent_eq_singleton]; rw [connectedComponent_eq_iInter_isClopen]; rw [mem_iInter]
  rintro ⟨U, hU1, hU2⟩
  exact (Quotient.exact' (h (ofIsClopen hU1))).mpr hU2

中文:
定理 eq_of_对任意_proj_eq
  结论: [T2空间 X] [紧空间 X] [disc : 全不连通空间 X]
  证明: by
  rw [← mem_singleton_iff]; rw [← connectedComponent_eq_singleton]; rw [connectedComponent_eq_iInter_isClopen]; rw [mem_iInter]
  rintro ⟨U, hU1, hU2⟩
  exact (Quotient.exact' (h (ofIsClopen hU1))).mpr hU2

Depends on / 依赖: Quotient, Quotient.exact, connectedComponent_eq_iInter_isClopen, connectedComponent_eq_singleton, mem_iInter, mem_singleton_iff, ofIsClopen
-/
theorem eq_of_forall_proj_eq [T2Space X] [CompactSpace X] [disc : TotallyDisconnectedSpace X]
    {x y : X} (h : forall Q : DiscreteQuotient X, Q.proj x = Q.proj y) : x = y := by
  rw [← mem_singleton_iff]; rw [← connectedComponent_eq_singleton]; rw [connectedComponent_eq_iInter_isClopen]; rw [mem_iInter]
  rintro ⟨U, hU1, hU2⟩
  exact (Quotient.exact' (h (ofIsClopen hU1))).mpr hU2

/--
theorem `fiber_subset_ofLE` / 定理 `fiber_subset_ofLE`

English:
theorem fiber_subset_ofLE
  given: {A B : DiscreteQuotient X} (h : A <= B) (a : A)
  proof: by
  rcases A.proj_surjective a with ⟨a, rfl⟩
  rw [fiber_eq]; rw [ofLE_proj]; rw [fiber_eq]
  exact fun _ h' => h h'

中文:
定理 fiber_subset_ofLE
  条件: {A B : DiscreteQuotient X} (h : A <= B) (a : A)
  证明: by
  rcases A.proj_surjective a with ⟨a, rfl⟩
  rw [fiber_eq]; rw [ofLE_proj]; rw [fiber_eq]
  exact fun _ h' => h h'

Depends on / 依赖: A.proj_surjective, fiber_eq, ofLE_proj, proj_surjective
-/
theorem fiber_subset_ofLE {A B : DiscreteQuotient X} (h : A <= B) (a : A) :
    A.proj ⁻¹' {a} subseteq B.proj ⁻¹' {ofLE h a} := by
  rcases A.proj_surjective a with ⟨a, rfl⟩
  rw [fiber_eq]; rw [ofLE_proj]; rw [fiber_eq]
  exact fun _ h' => h h'

/--
theorem `exists_of_compat` / 定理 `exists_of_compat`

English:
theorem exists_of_compat
  statement: [CompactSpace X] (Qs : (Q : DiscreteQuotient X) -> Q)
  proof: by
  have H₁ : forall Q₁ Q₂, Q₁ <= Q₂ -> proj Q₁ ⁻¹' {Qs Q₁} subseteq proj Q₂ ⁻¹' {Qs Q₂} := fun _ _ h => by
    rw [← compat _ _ h]
    exact fiber_subset_ofLE _ _
  obtain ⟨x, hx⟩ : Set.Nonempty (⋂ Q, proj Q ⁻¹' {Qs Q}) :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun Q : DiscreteQuotient X => Q.proj ⁻¹' {Qs _}) (directed_of_isDirected_ge H₁)
      (fun Q => (singleton_nonempty _).preimage Q.proj_surjective)
      (fun Q => (Q.isClosed_preimage {Qs _}).isCompact) fun Q => Q.isClosed_preimage _
  exact ⟨x, mem_iInter.1 hx⟩

中文:
定理 存在_of_compat
  结论: [紧空间 X] (Qs : (Q : DiscreteQuotient X) -> Q)
  证明: by
  have H₁ : forall Q₁ Q₂, Q₁ <= Q₂ -> proj Q₁ ⁻¹' {Qs Q₁} subseteq proj Q₂ ⁻¹' {Qs Q₂} := fun _ _ h => by
    rw [← compat _ _ h]
    exact fiber_subset_ofLE _ _
  obtain ⟨x, hx⟩ : Set.Nonempty (⋂ Q, proj Q ⁻¹' {Qs Q}) :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun Q : DiscreteQuotient X => Q.proj ⁻¹' {Qs _}) (directed_of_isDirected_ge H₁)
      (fun Q => (singleton_nonempty _).preimage Q.proj_surjective)
      (fun Q => (Q.isClosed_preimage {Qs _}).isCompact) fun Q => Q.isClosed_preimage _
  exact ⟨x, mem_iInter.1 hx⟩

Depends on / 依赖: DiscreteQuotient, IsCompact, IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed, Nonempty, Q.isClosed_preimage, Q.proj, Q.proj_surjective, Set.Nonempty, compat, directed_of_isDirected_ge, fiber_subset_ofLE, isClosed_preimage, isCompact, nonempty_iInter_of_directed_nonempty_isCompact_isClosed, preimage, proj_surjective, singleton_nonempty, subseteq
-/
theorem exists_of_compat [CompactSpace X] (Qs : (Q : DiscreteQuotient X) -> Q)
    (compat : forall (A B : DiscreteQuotient X) (h : A <= B), ofLE h (Qs _) = Qs _) :
    exists x : X, forall Q : DiscreteQuotient X, Q.proj x = Qs _ := by
  have H₁ : forall Q₁ Q₂, Q₁ <= Q₂ -> proj Q₁ ⁻¹' {Qs Q₁} subseteq proj Q₂ ⁻¹' {Qs Q₂} := fun _ _ h => by
    rw [← compat _ _ h]
    exact fiber_subset_ofLE _ _
  obtain ⟨x, hx⟩ : Set.Nonempty (⋂ Q, proj Q ⁻¹' {Qs Q}) :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun Q : DiscreteQuotient X => Q.proj ⁻¹' {Qs _}) (directed_of_isDirected_ge H₁)
      (fun Q => (singleton_nonempty _).preimage Q.proj_surjective)
      (fun Q => (Q.isClosed_preimage {Qs _}).isCompact) fun Q => Q.isClosed_preimage _
  exact ⟨x, mem_iInter.1 hx⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompactSpace
  signature: X] : Finite S
  body: by
  have : CompactSpace S := Quotient.compactSpace
  rwa [← isCompact_univ_iff, isCompact_iff_finite, finite_univ_iff] at this

中文:
实例 [紧空间
  签名: X] : 有限 S
  定义体: by
  have : CompactSpace S := Quotient.compactSpace
  rwa [← isCompact_univ_iff, isCompact_iff_finite, finite_univ_iff] at this

Depends on / 依赖: CompactSpace, Quotient, Quotient.compactSpace, compactSpace, finite_univ_iff, isCompact_iff_finite, isCompact_univ_iff
-/
instance [CompactSpace X] : Finite S := by
  have : CompactSpace S := Quotient.compactSpace
  rwa [← isCompact_univ_iff, isCompact_iff_finite, finite_univ_iff] at this

variable (X)

open scoped Classical in
/--
Definition of `finsetClopens` / `finsetClopens` 的定义

English:
definition finsetClopens
  signature: [CompactSpace X]
  body: have : Fintype d := Fintype.ofFinite _
  (Set.range (fun (x : d) => ⟨_, d.isClopen_preimage {x}⟩) : Set (Clopens X)).toFinset

中文:
定义 finsetClopens
  签名: [紧空间 X]
  定义体: have : Fintype d := Fintype.ofFinite _
  (Set.range (fun (x : d) => ⟨_, d.isClopen_preimage {x}⟩) : Set (Clopens X)).toFinset

Depends on / 依赖: Fintype, Fintype.ofFinite, ofFinite
-/
noncomputable def finsetClopens [CompactSpace X]
    (d : DiscreteQuotient X) : Finset (Clopens X) := have : Fintype d := Fintype.ofFinite _
  (Set.range (fun (x : d) => ⟨_, d.isClopen_preimage {x}⟩) : Set (Clopens X)).toFinset

/--
lemma `comp_finsetClopens` / 引理 `comp_finsetClopens`

English:
lemma comp_finsetClopens
  given: [CompactSpace X]
  proof: by
  ext d
  simp only [Setoid.classes, Set.mem_ofPred_eq, Function.comp_apply,
    finsetClopens, Set.coe_toFinset, Set.mem_image, Set.mem_range,
    exists_exists_eq_and]
  constructor
  · refine fun ⟨y, h⟩ => ⟨Quotient.out (s := d.toSetoid) y, ?_⟩
    ext
    simpa [← h] using! Quotient.mk_eq_iff_out (s := d.toSetoid)
  · exact fun ⟨y, h⟩ => ⟨d.proj y, by ext; simp [h, proj, Quotient.eq]⟩

中文:
引理 comp_finsetClopens
  条件: [紧空间 X]
  证明: by
  ext d
  simp only [Setoid.classes, Set.mem_ofPred_eq, Function.comp_apply,
    finsetClopens, Set.coe_toFinset, Set.mem_image, Set.mem_range,
    exists_exists_eq_and]
  constructor
  · refine fun ⟨y, h⟩ => ⟨Quotient.out (s := d.toSetoid) y, ?_⟩
    ext
    simpa [← h] using! Quotient.mk_eq_iff_out (s := d.toSetoid)
  · exact fun ⟨y, h⟩ => ⟨d.proj y, by ext; simp [h, proj, Quotient.eq]⟩

Depends on / 依赖: Function, Function.comp_apply, Quotient, Quotient.eq, Quotient.mk_eq_iff_out, Quotient.out, Set.coe_toFinset, Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, Setoid, Setoid.classes, classes, coe_toFinset, comp_apply, d.proj, d.toSetoid, exists_exists_eq_and, finsetClopens, mem_image
-/
lemma comp_finsetClopens [CompactSpace X] :
    (Set.image (fun (t : Clopens X) => t.carrier) ∘ (↑)) ∘
      finsetClopens X = fun ⟨f, _⟩ => f.classes := by
  ext d
  simp only [Setoid.classes, Set.mem_ofPred_eq, Function.comp_apply,
    finsetClopens, Set.coe_toFinset, Set.mem_image, Set.mem_range,
    exists_exists_eq_and]
  constructor
  · refine fun ⟨y, h⟩ => ⟨Quotient.out (s := d.toSetoid) y, ?_⟩
    ext
    simpa [← h] using! Quotient.mk_eq_iff_out (s := d.toSetoid)
  · exact fun ⟨y, h⟩ => ⟨d.proj y, by ext; simp [h, proj, Quotient.eq]⟩

/--
theorem `finsetClopens_inj` / 定理 `finsetClopens_inj`

English:
theorem finsetClopens_inj
  given: [CompactSpace X]
  proof: by
  apply Function.Injective.of_comp (f := Set.image (fun (t : Clopens X) => t.carrier) ∘ (↑))
  rw [comp_finsetClopens]
  intro ⟨_, _⟩ ⟨_, _⟩ h
  congr
  rw [Setoid.classes_inj]
  exact h

中文:
定理 finsetClopens_inj
  条件: [紧空间 X]
  证明: by
  apply Function.Injective.of_comp (f := Set.image (fun (t : Clopens X) => t.carrier) ∘ (↑))
  rw [comp_finsetClopens]
  intro ⟨_, _⟩ ⟨_, _⟩ h
  congr
  rw [Setoid.classes_inj]
  exact h

Depends on / 依赖: Clopens, Function, Function.Injective.of_comp, Injective, Set.image, Setoid, Setoid.classes_inj, carrier, classes_inj, comp_finsetClopens, of_comp, t.carrier
-/
theorem finsetClopens_inj [CompactSpace X] :
    (finsetClopens X).Injective := by
  apply Function.Injective.of_comp (f := Set.image (fun (t : Clopens X) => t.carrier) ∘ (↑))
  rw [comp_finsetClopens]
  intro ⟨_, _⟩ ⟨_, _⟩ h
  congr
  rw [Setoid.classes_inj]
  exact h

/--
The discrete quotients of a compact space are in bijection with a subtype of the type of
`Finset (Clopens X)`.

TODO: show that this is precisely those finsets of clopens which form a partition of `X`.
-/
noncomputable
/--
Definition of `equivFinsetClopens` / `equivFinsetClopens` 的定义

English:
definition equivFinsetClopens
  signature: [CompactSpace X]
  body: Equiv.ofInjective _ (finsetClopens_inj X)

中文:
定义 equivFinsetClopens
  签名: [紧空间 X]
  定义体: Equiv.ofInjective _ (finsetClopens_inj X)

Depends on / 依赖: Equiv.ofInjective, finsetClopens_inj, ofInjective
-/
def equivFinsetClopens [CompactSpace X] := Equiv.ofInjective _ (finsetClopens_inj X)

end DiscreteQuotient

namespace LocallyConstant

variable (f : LocallyConstant X α)

/--
Definition of `discreteQuotient` / `discreteQuotient` 的定义

English:
definition discreteQuotient
  signature: : DiscreteQuotient X where
  body: .comap f ⊥
  isOpen_setOfPred_rel _ := f.isLocallyConstant _

中文:
定义 discreteQuotient
  签名: : DiscreteQuotient X where
  定义体: .comap f ⊥
  isOpen_setOfPred_rel _ := f.isLocallyConstant _
-/
def discreteQuotient : DiscreteQuotient X where
  toSetoid := .comap f ⊥
  isOpen_setOfPred_rel _ := f.isLocallyConstant _

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : LocallyConstant f.discreteQuotient α
  body: ⟨fun a => Quotient.liftOn' a f fun _ _ => id, fun _ => isOpen_discrete _⟩

@[simp]

中文:
定义 lift
  签名: : 局部常数 f.discreteQuotient α
  定义体: ⟨fun a => Quotient.liftOn' a f fun _ _ => id, fun _ => isOpen_discrete _⟩

@[simp]

Depends on / 依赖: Quotient, Quotient.liftOn, isOpen_discrete, liftOn
-/
def lift : LocallyConstant f.discreteQuotient α :=
  ⟨fun a => Quotient.liftOn' a f fun _ _ => id, fun _ => isOpen_discrete _⟩

@[simp]
/--
theorem `lift_comp_proj` / 定理 `lift_comp_proj`

English:
theorem lift_comp_proj
  statement: f.lift ∘ f.discreteQuotient.proj = f
  proof: rfl

中文:
定理 lift_comp_proj
  结论: f.lift ∘ f.discreteQuotient.proj = f
  证明: rfl
-/
theorem lift_comp_proj : f.lift ∘ f.discreteQuotient.proj = f := rfl

end LocallyConstant
