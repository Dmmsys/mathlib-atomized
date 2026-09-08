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
/-
**DiscreteQuotient** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_5) → [TopologicalSpace X] → Type u_5
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of discrete quotients of a topological space.
-/
structure DiscreteQuotient (X : Type*) [TopologicalSpace X] extends Setoid X where
  /-- For every point `x`, the set `{ y | Rel x y }` is an open set. -/
  protected isOpen_setOfPred_rel : ∀ x, IsOpen (Set.ofPred (toSetoid x))

namespace DiscreteQuotient

variable (S : DiscreteQuotient X)

@[deprecated (since := "2026-07-09")]
protected alias isOpen_setOf_rel := DiscreteQuotient.isOpen_setOfPred_rel

/-
**DiscreteQuotient.toSetoid_injective** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotien
t`。
形式化陈述：∀ {X : Type u_2} [inst : TopologicalSpace X], Function.Injective DiscreteQ
uotient.toSetoid
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSetoid_injective : Function.Injective (@toSetoid X _)
  | ⟨_, _⟩, ⟨_, _⟩, _ => by congr

/-- Construct a discrete quotient from a clopen set. -/
/-
**DiscreteQuotient.ofIsClopen** 是 Mathlib 中的一个定义，位于命名空间 `DiscreteQuotient`。
形式化陈述：ofIsClopen {A : Set X} (h : IsClopen A) : DiscreteQuotient X where toSetoi
d
参数：h : IsClopen A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a discrete quotient from a clopen set.
-/
def ofIsClopen {A : Set X} (h : IsClopen A) : DiscreteQuotient X where
  toSetoid := ⟨fun x y => x ∈ A ↔ y ∈ A, fun _ => Iff.rfl, Iff.symm, Iff.trans⟩
  isOpen_setOfPred_rel x := by by_cases hx : x ∈ A <;> simp [hx, h.1, h.2, ← compl_ofPred]
/-
**DiscreteQuotient.refl** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：refl : forall x, S.toSetoid x x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.refl'`：refl' (r : Setoid α) (x) : r x x
-/
theorem refl : ∀ x, S.toSetoid x x := S.refl'
/-
**DiscreteQuotient.symm** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：symm (x y : X) : S.toSetoid x y -> S.toSetoid y x
参数：x y : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.symm'`：symm' (r : Setoid α) : forall {x y}, r x y -> r y x
-/
theorem symm (x y : X) : S.toSetoid x y → S.toSetoid y x := S.symm'
/-
**DiscreteQuotient.trans** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：trans (x y z : X) : S.toSetoid x y -> S.toSetoid y z -> S.toSetoid x z
参数：x y z : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.trans'`：trans' (r : Setoid α) : forall {x y z}, r x y -> r y z ->
 r x z
-/
theorem trans (x y z : X) : S.toSetoid x y → S.toSetoid y z → S.toSetoid x z := S.trans'

/-- The setoid whose quotient yields the discrete quotient. -/
add_decl_doc toSetoid

/-
**DiscreteQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (DiscreteQuotient X) (Type _) :=
  ⟨fun S => Quotient S.toSetoid⟩
/-
**DiscreteQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace S :=
  inferInstanceAs (TopologicalSpace (Quotient S.toSetoid))

/-- The projection from `X` to the given discrete quotient. -/
/-
**DiscreteQuotient.proj** 是 Mathlib 中的一个定义，位于命名空间 `DiscreteQuotient`。
形式化陈述：proj : X -> S
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
The projection from `X` to the given discrete quotient.
-/
def proj : X → S := Quotient.mk''
/-
**DiscreteQuotient.fiber_eq** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：fiber_eq (x : X) : S.proj ⁻¹' {S.proj x} = Set.ofPred (S.toSetoid x)
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b
-/
theorem fiber_eq (x : X) : S.proj ⁻¹' {S.proj x} = Set.ofPred (S.toSetoid x) :=
  Set.ext fun _ => eq_comm.trans Quotient.eq''
/-
**DiscreteQuotient.proj_surjective** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：proj_surjective : Function.Surjective S.proj
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''_surjective`：∀ {α : Sort u_1} {s₁ : Setoid α}, Function.Sur
jective Quotient.mk''
-/
theorem proj_surjective : Function.Surjective S.proj :=
  Quotient.mk''_surjective
/-
**DiscreteQuotient.proj_isQuotientMap** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotien
t`。
形式化陈述：proj_isQuotientMap : IsQuotientMap S.proj
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isQuotientMap_quot_mk`：isQuotientMap_quot_mk : IsQuotientMap (@Quot.mk X
 r)
-/
theorem proj_isQuotientMap : IsQuotientMap S.proj :=
  isQuotientMap_quot_mk
/-
**DiscreteQuotient.proj_continuous** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：proj_continuous : Continuous S.proj
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsQuotientMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : 
X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsQ
uotientMap f → Continuo…
· 使用定理 `DiscreteQuotient.proj_isQuotientMap`：proj_isQuotientMap : IsQuotientMap 
S.proj
-/
theorem proj_continuous : Continuous S.proj :=
  S.proj_isQuotientMap.continuous
/-
**DiscreteQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DiscreteTopology S :=
  discreteTopology_iff_isOpen_singleton.2 <| S.proj_surjective.forall.2 fun x => by
    rw [← S.proj_isQuotientMap.isOpen_preimage, fiber_eq]
    exact S.isOpen_setOfPred_rel _
/-
**DiscreteQuotient.proj_isLocallyConstant** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuo
tient`。
形式化陈述：proj_isLocallyConstant : IsLocallyConstant S.proj
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocallyConstant.iff_continuous`：iff_continuous {_ : TopologicalSpace Y
} [DiscreteTopology Y] (f : X -> Y) : IsLocallyConstant f ↔ Continuous f
· 使用定理 `DiscreteQuotient.instDiscreteTopologyQuotient`：∀ {X : Type u_2} [inst : 
TopologicalSpace X] (S : DiscreteQuotient X), DiscreteTopology (Quotient S.toSet
oid)
· 使用定理 `DiscreteQuotient.proj_continuous`：proj_continuous : Continuous S.proj
-/
theorem proj_isLocallyConstant : IsLocallyConstant S.proj :=
  (IsLocallyConstant.iff_continuous S.proj).2 S.proj_continuous
/-
**DiscreteQuotient.isClopen_preimage** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient
`。
形式化陈述：isClopen_preimage (A : Set S) : IsClopen (S.proj ⁻¹' A)
参数：A : Set S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClopen.preimage`：IsClopen.preimage {s : Set Y} (h : IsClopen s) {f : X
 -> Y} (hf : Continuous f) : IsClopen (f ⁻¹' s)
· 使用定理 `isClopen_discrete`：isClopen_discrete [DiscreteTopology X] (s : Set X) : 
IsClopen s
· 使用定理 `DiscreteQuotient.instDiscreteTopologyQuotient`：∀ {X : Type u_2} [inst : 
TopologicalSpace X] (S : DiscreteQuotient X), DiscreteTopology (Quotient S.toSet
oid)
· 使用定理 `DiscreteQuotient.proj_continuous`：proj_continuous : Continuous S.proj
-/
theorem isClopen_preimage (A : Set S) : IsClopen (S.proj ⁻¹' A) :=
  (isClopen_discrete A).preimage S.proj_continuous
/-
**DiscreteQuotient.isOpen_preimage** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：isOpen_preimage (A : Set S) : IsOpen (S.proj ⁻¹' A)
参数：A : Set S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `DiscreteQuotient.isClopen_preimage`：isClopen_preimage (A : Set S) : IsCl
open (S.proj ⁻¹' A)
-/
theorem isOpen_preimage (A : Set S) : IsOpen (S.proj ⁻¹' A) :=
  (S.isClopen_preimage A).2
/-
**DiscreteQuotient.isClosed_preimage** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient
`。
形式化陈述：isClosed_preimage (A : Set S) : IsClosed (S.proj ⁻¹' A)
参数：A : Set S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `DiscreteQuotient.isClopen_preimage`：isClopen_preimage (A : Set S) : IsCl
open (S.proj ⁻¹' A)
-/
theorem isClosed_preimage (A : Set S) : IsClosed (S.proj ⁻¹' A) :=
  (S.isClopen_preimage A).1
/-
**DiscreteQuotient.isClopen_setOfPred_rel** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuo
tient`。
形式化陈述：isClopen_setOfPred_rel (x : X) : IsClopen (Set.ofPred (S.toSetoid x))
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DiscreteQuotient.fiber_eq`：fiber_eq (x : X) : S.proj ⁻¹' {S.proj x} = Se
t.ofPred (S.toSetoid x)
· 使用定理 `DiscreteQuotient.isClopen_preimage`：isClopen_preimage (A : Set S) : IsCl
open (S.proj ⁻¹' A)
-/
theorem isClopen_setOfPred_rel (x : X) : IsClopen (Set.ofPred (S.toSetoid x)) := by
  rw [← fiber_eq]
  apply isClopen_preimage

@[deprecated (since := "2026-07-09")]
alias isClopen_setOf_rel := isClopen_setOfPred_rel
/-
**DiscreteQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (DiscreteQuotient X) :=
  ⟨fun S₁ S₂ => ⟨S₁.1 ⊓ S₂.1, fun x => (S₁.2 x).inter (S₂.2 x)⟩⟩
/-
**DiscreteQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (DiscreteQuotient X) :=
  PartialOrder.lift _ toSetoid_injective
/-
**DiscreteQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeInf (DiscreteQuotient X) :=
  toSetoid_injective.semilatticeInf _ .rfl .rfl fun _ _ ↦ rfl
/-
**DiscreteQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTop (DiscreteQuotient X) where
  top := ⟨⊤, fun _ => isOpen_univ⟩
  le_top a := by tauto
/-
**DiscreteQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (DiscreteQuotient X) := ⟨⊤⟩
/-
**DiscreteQuotient.inhabitedQuotient** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteQuotient
`。
形式化陈述：inhabitedQuotient [Inhabited X] : Inhabited S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedQuotient [Inhabited X] : Inhabited S := ⟨S.proj default⟩

-- TODO: add instances about `Nonempty (Quot _)`/`Nonempty (Quotient _)`
/-
**DiscreteQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty X] : Nonempty S := Nonempty.map S.proj ‹_›

/-- The quotient by `⊤ : DiscreteQuotient X` is a `Subsingleton`. -/
/-
**DiscreteQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient by `⊤ : DiscreteQuotient X` is a `Subsingleton`.
-/
instance : Subsingleton (⊤ : DiscreteQuotient X) where
  allEq := by rintro ⟨_⟩ ⟨_⟩; exact Quotient.sound trivial

section Comap

variable (g : C(Y, Z)) (f : C(X, Y))

/-- Comap a discrete quotient along a continuous map. -/
/-
**DiscreteQuotient.comap** 是 Mathlib 中的一个定义，位于命名空间 `DiscreteQuotient`。
形式化陈述：comap (S : DiscreteQuotient Y) : DiscreteQuotient X where toSetoid
参数：S : DiscreteQuotient Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Comap a discrete quotient along a continuous map.
-/
def comap (S : DiscreteQuotient Y) : DiscreteQuotient X where
  toSetoid := Setoid.comap f S.1
  isOpen_setOfPred_rel _ := (S.2 _).preimage f.continuous

@[simp]
/-
**DiscreteQuotient.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：comap_id : S.comap (ContinuousMap.id X) = S
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_id : S.comap (ContinuousMap.id X) = S := rfl

@[simp]
/-
**DiscreteQuotient.comap_comp** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：comap_comp (S : DiscreteQuotient Z) : S.comap (g.comp f) = (S.comap g).com
ap f
参数：S : DiscreteQuotient Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comp (S : DiscreteQuotient Z) : S.comap (g.comp f) = (S.comap g).comap f :=
  rfl

@[gcongr, mono]
/-
**DiscreteQuotient.comap_mono** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：comap_mono {A B : DiscreteQuotient Y} (h : A <= B) : A.comap f <= B.comap 
f
参数：h : A <= B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_mono {A B : DiscreteQuotient Y} (h : A ≤ B) : A.comap f ≤ B.comap f := by tauto

end Comap

section OfLE

variable {A B C : DiscreteQuotient X}

/-- The map induced by a refinement of a discrete quotient. -/
/-
**DiscreteQuotient.ofLE** 是 Mathlib 中的一个定义，位于命名空间 `DiscreteQuotient`。
形式化陈述：ofLE (h : A <= B) : A -> B
参数：h : A <= B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)

--- 原说明 ---
The map induced by a refinement of a discrete quotient.
-/
def ofLE (h : A ≤ B) : A → B :=
  Quotient.map' id h

@[simp]
/-
**DiscreteQuotient.ofLE_refl** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：ofLE_refl : ofLE (le_refl A) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem ofLE_refl : ofLE (le_refl A) = id := by
  ext ⟨⟩
  rfl
/-
**DiscreteQuotient.ofLE_refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：ofLE_refl_apply (a : A) : ofLE (le_refl A) a = a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `DiscreteQuotient.ofLE_refl`：ofLE_refl : ofLE (le_refl A) = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofLE_refl_apply (a : A) : ofLE (le_refl A) a = a := by simp

@[simp]
/-
**DiscreteQuotient.ofLE_ofLE** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：ofLE_ofLE (h₁ : A <= B) (h₂ : B <= C) (x : A) : ofLE h₂ (ofLE h₁ x) = ofLE
 (h₁.trans h₂) x
参数：h₁ : A <= B；h₂ : B <= C；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem ofLE_ofLE (h₁ : A ≤ B) (h₂ : B ≤ C) (x : A) :
    ofLE h₂ (ofLE h₁ x) = ofLE (h₁.trans h₂) x := by
  rcases x with ⟨⟩
  rfl

@[simp]
/-
**DiscreteQuotient.ofLE_comp_ofLE** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：ofLE_comp_ofLE (h₁ : A <= B) (h₂ : B <= C) : ofLE h₂ ∘ ofLE h₁ = ofLE (le_
trans h₁ h₂)
参数：h₁ : A <= B；h₂ : B <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `DiscreteQuotient.ofLE_ofLE`：ofLE_ofLE (h₁ : A <= B) (h₂ : B <= C) (x : A
) : ofLE h₂ (ofLE h₁ x) = ofLE (h₁.trans h₂) x
-/
theorem ofLE_comp_ofLE (h₁ : A ≤ B) (h₂ : B ≤ C) : ofLE h₂ ∘ ofLE h₁ = ofLE (le_trans h₁ h₂) :=
  funext <| ofLE_ofLE _ _
/-
**DiscreteQuotient.ofLE_continuous** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：ofLE_continuous (h : A <= B) : Continuous (ofLE h)
参数：h : A <= B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_discreteTopology`：continuous_of_discreteTopology [Topologi
calSpace β] {f : α -> β} : Continuous f
· 使用定理 `DiscreteQuotient.instDiscreteTopologyQuotient`：∀ {X : Type u_2} [inst : 
TopologicalSpace X] (S : DiscreteQuotient X), DiscreteTopology (Quotient S.toSet
oid)
-/
theorem ofLE_continuous (h : A ≤ B) : Continuous (ofLE h) :=
  continuous_of_discreteTopology

@[simp]
/-
**DiscreteQuotient.ofLE_proj** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：ofLE_proj (h : A <= B) (x : X) : ofLE h (A.proj x) = B.proj x
参数：h : A <= B；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
· 使用定理 `DiscreteQuotient.refl`：refl : forall x, S.toSetoid x x
-/
theorem ofLE_proj (h : A ≤ B) (x : X) : ofLE h (A.proj x) = B.proj x :=
  Quotient.sound' (B.refl _)

@[simp]
/-
**DiscreteQuotient.ofLE_comp_proj** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：ofLE_comp_proj (h : A <= B) : ofLE h ∘ A.proj = B.proj
参数：h : A <= B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DiscreteQuotient.ofLE_proj`：ofLE_proj (h : A <= B) (x : X) : ofLE h (A.p
roj x) = B.proj x
-/
theorem ofLE_comp_proj (h : A ≤ B) : ofLE h ∘ A.proj = B.proj :=
  funext <| ofLE_proj _

end OfLE

/-- When `X` is a locally connected space, there is an `OrderBot` instance on
`DiscreteQuotient X`. The bottom element is given by `connectedComponentSetoid X`
-/
/-
**DiscreteQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `X` is a locally connected space, there is an `OrderBot` instance on
`DiscreteQuotient X`. The bottom element is given by `connectedComponentSetoid X
`
-/
instance [LocallyConnectedSpace X] : OrderBot (DiscreteQuotient X) where
  bot :=
    { toSetoid := connectedComponentSetoid X
      isOpen_setOfPred_rel := fun x => by
        convert! isOpen_connectedComponent (x := x)
        ext y
        simpa only [connectedComponentSetoid, ← connectedComponent_eq_iff_mem] using! eq_comm }
  bot_le S := fun x y (h : connectedComponent x = connectedComponent y) =>
    (S.isClopen_setOfPred_rel x).connectedComponent_subset (S.refl _) <|
      h.symm ▸ mem_connectedComponent

@[simp]
/-
**DiscreteQuotient.proj_bot_eq** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：proj_bot_eq [LocallyConnectedSpace X] {x y : X} : proj ⊥ x = proj ⊥ y ↔ co
nnectedComponent x = connectedComponent y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b
-/
theorem proj_bot_eq [LocallyConnectedSpace X] {x y : X} :
    proj ⊥ x = proj ⊥ y ↔ connectedComponent x = connectedComponent y :=
  Quotient.eq''
/-
**DiscreteQuotient.proj_bot_inj** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：proj_bot_inj [DiscreteTopology X] {x y : X} : proj ⊥ x = proj ⊥ y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `DiscreteTopology.toLocallyConnectedSpace`：∀ (α : Type u_3) [inst : Topol
ogicalSpace α] [DiscreteTopology α], LocallyConnectedSpace α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `connectedComponent_eq_singleton`：∀ {α : Type u} [inst : TopologicalSpace
 α] [TotallyDisconnectedSpace α] (x : α), connectedComponent x = {x}
· 使用定理 `TotallySeparatedSpace.totallyDisconnectedSpace`：∀ (α : Type u) [inst : T
opologicalSpace α] [TotallySeparatedSpace α], TotallyDisconnectedSpace α
· 使用定理 `TotallySeparatedSpace.of_discrete`：∀ (α : Type u_3) [inst : TopologicalS
pace α] [DiscreteTopology α], TotallySeparatedSpace α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem proj_bot_inj [DiscreteTopology X] {x y : X} : proj ⊥ x = proj ⊥ y ↔ x = y := by simp
/-
**DiscreteQuotient.proj_bot_injective** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotien
t`。
形式化陈述：proj_bot_injective [DiscreteTopology X] : Injective (⊥ : DiscreteQuotient 
X).proj
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DiscreteTopology.toLocallyConnectedSpace`：∀ (α : Type u_3) [inst : Topol
ogicalSpace α] [DiscreteTopology α], LocallyConnectedSpace α
· 使用定理 `DiscreteQuotient.proj_bot_inj`：proj_bot_inj [DiscreteTopology X] {x y : 
X} : proj ⊥ x = proj ⊥ y ↔ x = y
-/
theorem proj_bot_injective [DiscreteTopology X] : Injective (⊥ : DiscreteQuotient X).proj :=
  fun _ _ => proj_bot_inj.1
/-
**DiscreteQuotient.proj_bot_bijective** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotien
t`。
形式化陈述：proj_bot_bijective [DiscreteTopology X] : Bijective (⊥ : DiscreteQuotient 
X).proj
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiscreteTopology.toLocallyConnectedSpace`：∀ (α : Type u_3) [inst : Topol
ogicalSpace α] [DiscreteTopology α], LocallyConnectedSpace α
· 使用定理 `DiscreteQuotient.proj_bot_injective`：proj_bot_injective [DiscreteTopolog
y X] : Injective (⊥ : DiscreteQuotient X).proj
· 使用定理 `DiscreteQuotient.proj_surjective`：proj_surjective : Function.Surjective 
S.proj
-/
theorem proj_bot_bijective [DiscreteTopology X] : Bijective (⊥ : DiscreteQuotient X).proj :=
  ⟨proj_bot_injective, proj_surjective _⟩

section Map

variable (f : C(X, Y)) (A A' : DiscreteQuotient X) (B B' : DiscreteQuotient Y)

/-- Given `f : C(X, Y)`, `DiscreteQuotient.LEComap f A B` is defined as
`A ≤ B.comap f`. Mathematically this means that `f` descends to a morphism `A → B`. -/
/-
**DiscreteQuotient.LEComap** 是 Mathlib 中的一个定义，位于命名空间 `DiscreteQuotient`。
形式化陈述：LEComap : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : C(X, Y)`, `DiscreteQuotient.LEComap f A B` is defined as
`A ≤ B.comap f`. Mathematically this means that `f` descends to a morphism `A → 
B`.
-/
def LEComap : Prop :=
  A ≤ B.comap f
/-
**DiscreteQuotient.leComap_id** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：leComap_id : LEComap (.id X) A A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem leComap_id : LEComap (.id X) A A := le_rfl

variable {A A' B B'} {f} {g : C(Y, Z)} {C : DiscreteQuotient Z}

@[simp]
/-
**DiscreteQuotient.leComap_id_iff** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：leComap_id_iff : LEComap (ContinuousMap.id X) A A' ↔ A <= A'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem leComap_id_iff : LEComap (ContinuousMap.id X) A A' ↔ A ≤ A' :=
  Iff.rfl
/-
**DiscreteQuotient.LEComap.comp** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient.LECo
map`。
形式化陈述：∀ {X : Type u_2} {Y : Type u_3} {Z : Type u_4} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace Z] {f : C(X, Y)} {A 
: DiscreteQuotient X} {B : DiscreteQuotient Y} {g : C(Y, Z)}   {C : DiscreteQuot
ient Z},   DiscreteQuotient.LEComap g B C → DiscreteQuotient.LEComap f A B → Dis
creteQuotient.LEComap (g.comp f) A C
参数：X, Y；Y, Z；g.comp f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LEComap.comp : LEComap g B C → LEComap f A B → LEComap (g.comp f) A C := by tauto

@[gcongr, mono]
/-
**DiscreteQuotient.LEComap.mono** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient.LECo
map`。
形式化陈述：∀ {X : Type u_2} {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : C(X, Y)}   {A A' : DiscreteQuotient X} {B B' : DiscreteQuot
ient Y},   DiscreteQuotient.LEComap f A B → A' ≤ A → B ≤ B' → DiscreteQuotient.L
EComap f A' B'
参数：X, Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `DiscreteQuotient.comap_mono`：comap_mono {A B : DiscreteQuotient Y} (h : 
A <= B) : A.comap f <= B.comap f
-/
theorem LEComap.mono (h : LEComap f A B) (hA : A' ≤ A) (hB : B ≤ B') : LEComap f A' B' :=
  hA.trans <| h.trans <| comap_mono _ hB

/-- Map a discrete quotient along a continuous map. -/
/-
**DiscreteQuotient.map** 是 Mathlib 中的一个定义，位于命名空间 `DiscreteQuotient`。
形式化陈述：map (f : C(X, Y)) (cond : LEComap f A B) : A -> B
参数：f : C(X, Y)；cond : LEComap f A B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)

--- 原说明 ---
Map a discrete quotient along a continuous map.
-/
def map (f : C(X, Y)) (cond : LEComap f A B) : A → B := Quotient.map' f cond
/-
**DiscreteQuotient.map_continuous** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：map_continuous (cond : LEComap f A B) : Continuous (map f cond)
参数：cond : LEComap f A B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_discreteTopology`：continuous_of_discreteTopology [Topologi
calSpace β] {f : α -> β} : Continuous f
· 使用定理 `DiscreteQuotient.instDiscreteTopologyQuotient`：∀ {X : Type u_2} [inst : 
TopologicalSpace X] (S : DiscreteQuotient X), DiscreteTopology (Quotient S.toSet
oid)
-/
theorem map_continuous (cond : LEComap f A B) : Continuous (map f cond) :=
  continuous_of_discreteTopology

@[simp]
/-
**DiscreteQuotient.map_comp_proj** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：map_comp_proj (cond : LEComap f A B) : map f cond ∘ A.proj = B.proj ∘ f
参数：cond : LEComap f A B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp_proj (cond : LEComap f A B) : map f cond ∘ A.proj = B.proj ∘ f :=
  rfl

@[simp]
/-
**DiscreteQuotient.map_proj** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：map_proj (cond : LEComap f A B) (x : X) : map f cond (A.proj x) = B.proj (
f x)
参数：cond : LEComap f A B；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_proj (cond : LEComap f A B) (x : X) : map f cond (A.proj x) = B.proj (f x) :=
  rfl

@[simp]
/-
**DiscreteQuotient.map_id** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：map_id : map _ (leComap_id A) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DiscreteQuotient.leComap_id`：leComap_id : LEComap (.id X) A A
-/
theorem map_id : map _ (leComap_id A) = id := by ext ⟨⟩; rfl

-- This can't be a `@[simp]` lemma since `h1` and `h2` can't be found by unification in a Prop.
/-
**DiscreteQuotient.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：map_comp (h1 : LEComap g B C) (h2 : LEComap f A B) : map (g.comp f) (h1.co
mp h2) = map g h1 ∘ map f h2
参数：h1 : LEComap g B C；h2 : LEComap f A B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DiscreteQuotient.LEComap.comp`：∀ {X : Type u_2} {Y : Type u_3} {Z : Type
 u_4} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : Topo
logicalSpace Z] {f …
-/
theorem map_comp (h1 : LEComap g B C) (h2 : LEComap f A B) :
    map (g.comp f) (h1.comp h2) = map g h1 ∘ map f h2 := by
  ext ⟨⟩
  rfl

@[simp]
/-
**DiscreteQuotient.ofLE_map** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：ofLE_map (cond : LEComap f A B) (h : B <= B') (a : A) : ofLE h (map f cond
 a) = map f (cond.mono le_rfl h) a
参数：cond : LEComap f A B；h : B <= B'；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiscreteQuotient.LEComap.mono`：∀ {X : Type u_2} {Y : Type u_3} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y] {f : C(X, Y)}   {A A' : Discret
eQuotient X} {B B' …
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem ofLE_map (cond : LEComap f A B) (h : B ≤ B') (a : A) :
    ofLE h (map f cond a) = map f (cond.mono le_rfl h) a := by
  rcases a with ⟨⟩
  rfl

@[simp]
/-
**DiscreteQuotient.ofLE_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：ofLE_comp_map (cond : LEComap f A B) (h : B <= B') : ofLE h ∘ map f cond =
 map f (cond.mono le_rfl h)
参数：cond : LEComap f A B；h : B <= B'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DiscreteQuotient.LEComap.mono`：∀ {X : Type u_2} {Y : Type u_3} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y] {f : C(X, Y)}   {A A' : Discret
eQuotient X} {B B' …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `DiscreteQuotient.ofLE_map`：ofLE_map (cond : LEComap f A B) (h : B <= B')
 (a : A) : ofLE h (map f cond a) = map f (cond.mono le_rfl h) a
-/
theorem ofLE_comp_map (cond : LEComap f A B) (h : B ≤ B') :
    ofLE h ∘ map f cond = map f (cond.mono le_rfl h) :=
  funext <| ofLE_map cond h

@[simp]
/-
**DiscreteQuotient.map_ofLE** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：map_ofLE (cond : LEComap f A B) (h : A' <= A) (c : A') : map f cond (ofLE 
h c) = map f (cond.mono h le_rfl) c
参数：cond : LEComap f A B；h : A' <= A；c : A'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiscreteQuotient.LEComap.mono`：∀ {X : Type u_2} {Y : Type u_3} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y] {f : C(X, Y)}   {A A' : Discret
eQuotient X} {B B' …
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem map_ofLE (cond : LEComap f A B) (h : A' ≤ A) (c : A') :
    map f cond (ofLE h c) = map f (cond.mono h le_rfl) c := by
  rcases c with ⟨⟩
  rfl

@[simp]
/-
**DiscreteQuotient.map_comp_ofLE** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`。
形式化陈述：map_comp_ofLE (cond : LEComap f A B) (h : A' <= A) : map f cond ∘ ofLE h =
 map f (cond.mono h le_rfl)
参数：cond : LEComap f A B；h : A' <= A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DiscreteQuotient.LEComap.mono`：∀ {X : Type u_2} {Y : Type u_3} [inst : T
opologicalSpace X] [inst_1 : TopologicalSpace Y] {f : C(X, Y)}   {A A' : Discret
eQuotient X} {B B' …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `DiscreteQuotient.map_ofLE`：map_ofLE (cond : LEComap f A B) (h : A' <= A)
 (c : A') : map f cond (ofLE h c) = map f (cond.mono h le_rfl) c
-/
theorem map_comp_ofLE (cond : LEComap f A B) (h : A' ≤ A) :
    map f cond ∘ ofLE h = map f (cond.mono h le_rfl) :=
  funext <| map_ofLE cond h

end Map

/-
**DiscreteQuotient.eq_of_forall_proj_eq** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuoti
ent`。
形式化陈述：eq_of_forall_proj_eq [T2Space X] [CompactSpace X] [disc : TotallyDisconnec
tedSpace X] {x y : X} (h : forall Q : DiscreteQuotient X, Q.proj x = Q.proj y) :
 x = y
参数：h : forall Q : DiscreteQuotient X, Q.proj x = Q.proj y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `connectedComponent_eq_singleton`：∀ {α : Type u} [inst : TopologicalSpace
 α] [TotallyDisconnectedSpace α] (x : α), connectedComponent x = {x}
· 使用定理 `connectedComponent_eq_iInter_isClopen`：connectedComponent_eq_iInter_isCl
open [T2Space X] [CompactSpace X] (x : X) : connectedComponent x = ⋂ s : { s : S
et X // IsClopen s ∧ x in s…
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quotient.exact'`：exact' {a b : α} : (Quotient.mk'' a : Quotient s₁) = Qu
otient.mk'' b -> s₁ a b
-/
theorem eq_of_forall_proj_eq [T2Space X] [CompactSpace X] [disc : TotallyDisconnectedSpace X]
    {x y : X} (h : ∀ Q : DiscreteQuotient X, Q.proj x = Q.proj y) : x = y := by
  rw [← mem_singleton_iff, ← connectedComponent_eq_singleton, connectedComponent_eq_iInter_isClopen,
    mem_iInter]
  rintro ⟨U, hU1, hU2⟩
  exact (Quotient.exact' (h (ofIsClopen hU1))).mpr hU2
/-
**DiscreteQuotient.fiber_subset_ofLE** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient
`。
形式化陈述：fiber_subset_ofLE {A B : DiscreteQuotient X} (h : A <= B) (a : A) : A.proj
 ⁻¹' {a} subseteq B.proj ⁻¹' {ofLE h a}
参数：h : A <= B；a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiscreteQuotient.proj_surjective`：proj_surjective : Function.Surjective 
S.proj
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DiscreteQuotient.fiber_eq`：fiber_eq (x : X) : S.proj ⁻¹' {S.proj x} = Se
t.ofPred (S.toSetoid x)
· 使用定理 `DiscreteQuotient.ofLE_proj`：ofLE_proj (h : A <= B) (x : X) : ofLE h (A.p
roj x) = B.proj x
-/
theorem fiber_subset_ofLE {A B : DiscreteQuotient X} (h : A ≤ B) (a : A) :
    A.proj ⁻¹' {a} ⊆ B.proj ⁻¹' {ofLE h a} := by
  rcases A.proj_surjective a with ⟨a, rfl⟩
  rw [fiber_eq, ofLE_proj, fiber_eq]
  exact fun _ h' => h h'
/-
**DiscreteQuotient.exists_of_compat** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient`
。
形式化陈述：exists_of_compat [CompactSpace X] (Qs : (Q : DiscreteQuotient X) -> Q) (co
mpat : forall (A B : DiscreteQuotient X) (h : A <= B), ofLE h (Qs _) = Qs _) : e
xists x : X, forall Q : DiscreteQuotient X, Q.proj x = Qs _
参数：Qs : (Q : DiscreteQuotient X) -> Q；compat : forall (A B : DiscreteQuotient X)
 (h : A <= B), ofLE h (Qs _) = Qs _。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DiscreteQuotient.fiber_subset_ofLE`：fiber_subset_ofLE {A B : DiscreteQuo
tient X} (h : A <= B) (a : A) : A.proj ⁻¹' {a} subseteq B.proj ⁻¹' {ofLE h a}
· 使用定理 `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`：IsCom
pact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed {ι : Type v} [hι : 
Nonempty ι] (t : ι -> Set X) (htd : Directed (· ⊇ ·) t)…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `directed_of_isDirected_ge`：∀ {α : Type u_1} {β : Type u_2} [inst : LE α]
 [IsCodirectedOrder α] {f : α → β} {r : β → β → Prop},   (∀ ⦃j i : α⦄, j ≤ i → r
 (f i) (f j)) →…
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `Set.Nonempty.preimage`：∀ {α : Type u_1} {β : Type u_2} {s : Set β}, s.No
nempty → ∀ {f : α → β}, Function.Surjective f → (f ⁻¹' s).Nonempty
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `DiscreteQuotient.proj_surjective`：proj_surjective : Function.Surjective 
S.proj
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `DiscreteQuotient.isClosed_preimage`：isClosed_preimage (A : Set S) : IsCl
osed (S.proj ⁻¹' A)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
-/
theorem exists_of_compat [CompactSpace X] (Qs : (Q : DiscreteQuotient X) → Q)
    (compat : ∀ (A B : DiscreteQuotient X) (h : A ≤ B), ofLE h (Qs _) = Qs _) :
    ∃ x : X, ∀ Q : DiscreteQuotient X, Q.proj x = Qs _ := by
  have H₁ : ∀ Q₁ Q₂, Q₁ ≤ Q₂ → proj Q₁ ⁻¹' {Qs Q₁} ⊆ proj Q₂ ⁻¹' {Qs Q₂} := fun _ _ h => by
    rw [← compat _ _ h]
    exact fiber_subset_ofLE _ _
  obtain ⟨x, hx⟩ : Set.Nonempty (⋂ Q, proj Q ⁻¹' {Qs Q}) :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun Q : DiscreteQuotient X => Q.proj ⁻¹' {Qs _}) (directed_of_isDirected_ge H₁)
      (fun Q => (singleton_nonempty _).preimage Q.proj_surjective)
      (fun Q => (Q.isClosed_preimage {Qs _}).isCompact) fun Q => Q.isClosed_preimage _
  exact ⟨x, mem_iInter.1 hx⟩

/-- If `X` is a compact space, then any discrete quotient of `X` is finite. -/
/-
**DiscreteQuotient.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteQuotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` is a compact space, then any discrete quotient of `X` is finite.
-/
instance [CompactSpace X] : Finite S := by
  have : CompactSpace S := Quotient.compactSpace
  rwa [← isCompact_univ_iff, isCompact_iff_finite, finite_univ_iff] at this

variable (X)

open scoped Classical in
/--
If `X` is a compact space, then we associate to any discrete quotient on `X` a finite set of
clopen subsets of `X`, given by the fibers of `proj`.

TODO: prove that these form a partition of `X`
-/
/-
**DiscreteQuotient.finsetClopens** 是 Mathlib 中的一个定义，位于命名空间 `DiscreteQuotient`。
形式化陈述：finsetClopens [CompactSpace X] (d : DiscreteQuotient X) : Finset (Clopens 
X)
参数：d : DiscreteQuotient X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DiscreteQuotient.instFiniteQuotientOfCompactSpace`：∀ {X : Type u_2} [ins
t : TopologicalSpace X] (S : DiscreteQuotient X) [CompactSpace X], Finite (Quoti
ent S.toSetoid)

--- 原说明 ---
If `X` is a compact space, then we associate to any discrete quotient on `X` a f
inite set of
clopen subsets of `X`, given by the fibers of `proj`.

TODO: prove that these form a partition of `X`
-/
noncomputable def finsetClopens [CompactSpace X]
    (d : DiscreteQuotient X) : Finset (Clopens X) := have : Fintype d := Fintype.ofFinite _
  (Set.range (fun (x : d) ↦ ⟨_, d.isClopen_preimage {x}⟩) : Set (Clopens X)).toFinset

/-- A helper lemma to prove that `finsetClopens X` is injective, see `finsetClopens_inj`. -/
/-
**DiscreteQuotient.comp_finsetClopens** 是 Mathlib 中的一个引理，位于命名空间 `DiscreteQuotien
t`。
形式化陈述：comp_finsetClopens [CompactSpace X] : (Set.image (fun (t : Clopens X) => t
.carrier) ∘ (↑)) ∘ finsetClopens X = fun ⟨f, _⟩ => f.classes
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DiscreteQuotient.instFiniteQuotientOfCompactSpace`：∀ {X : Type u_2} [ins
t : TopologicalSpace X] (S : DiscreteQuotient X) [CompactSpace X], Finite (Quoti
ent S.toSetoid)
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quotient.mk_eq_iff_out`：Quotient.mk_eq_iff_out {s : Setoid α} {x : α} {y
 : Quotient s} : ⟦x⟧ = y ↔ x ≈ Quotient.out y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A helper lemma to prove that `finsetClopens X` is injective, see `finsetClopens_
inj`.
-/
lemma comp_finsetClopens [CompactSpace X] :
    (Set.image (fun (t : Clopens X) ↦ t.carrier) ∘ (↑)) ∘
      finsetClopens X = fun ⟨f, _⟩ ↦ f.classes := by
  ext d
  simp only [Setoid.classes, Set.mem_ofPred_eq, Function.comp_apply,
    finsetClopens, Set.coe_toFinset, Set.mem_image, Set.mem_range,
    exists_exists_eq_and]
  constructor
  · refine fun ⟨y, h⟩ ↦ ⟨Quotient.out (s := d.toSetoid) y, ?_⟩
    ext
    simpa [← h] using! Quotient.mk_eq_iff_out (s := d.toSetoid)
  · exact fun ⟨y, h⟩ ↦ ⟨d.proj y, by ext; simp [h, proj, Quotient.eq]⟩

/-- `finsetClopens X` is injective. -/
/-
**DiscreteQuotient.finsetClopens_inj** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteQuotient
`。
形式化陈述：finsetClopens_inj [CompactSpace X] : (finsetClopens X).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DiscreteQuotient.comp_finsetClopens`：comp_finsetClopens [CompactSpace X]
 : (Set.image (fun (t : Clopens X) => t.carrier) ∘ (↑)) ∘ finsetClopens X = fun 
⟨f, _⟩ => f.classes
· 使用定理 `Setoid.classes_inj`：classes_inj {r₁ r₂ : Setoid α} : r₁ = r₂ ↔ r₁.classe
s = r₂.classes

--- 原说明 ---
`finsetClopens X` is injective.
-/
theorem finsetClopens_inj [CompactSpace X] :
    (finsetClopens X).Injective := by
  apply Function.Injective.of_comp (f := Set.image (fun (t : Clopens X) ↦ t.carrier) ∘ (↑))
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
/-
**DiscreteQuotient.equivFinsetClopens** 是 Mathlib 中的一个定义，位于命名空间 `DiscreteQuotien
t`。
形式化陈述：equivFinsetClopens [CompactSpace X]
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DiscreteQuotient.finsetClopens_inj`：finsetClopens_inj [CompactSpace X] :
 (finsetClopens X).Injective
-/
def equivFinsetClopens [CompactSpace X] := Equiv.ofInjective _ (finsetClopens_inj X)

end DiscreteQuotient

namespace LocallyConstant

variable (f : LocallyConstant X α)

/-- Any locally constant function induces a discrete quotient. -/
/-
**LocallyConstant.discreteQuotient** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：discreteQuotient : DiscreteQuotient X where toSetoid
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any locally constant function induces a discrete quotient.
-/
def discreteQuotient : DiscreteQuotient X where
  toSetoid := .comap f ⊥
  isOpen_setOfPred_rel _ := f.isLocallyConstant _

/-- The (locally constant) function from the discrete quotient associated to a locally constant
function. -/
/-
**LocallyConstant.lift** 是 Mathlib 中的一个定义，位于命名空间 `LocallyConstant`。
形式化陈述：lift : LocallyConstant f.discreteQuotient α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (locally constant) function from the discrete quotient associated to a local
ly constant
function.
-/
def lift : LocallyConstant f.discreteQuotient α :=
  ⟨fun a => Quotient.liftOn' a f fun _ _ => id, fun _ => isOpen_discrete _⟩

@[simp]
/-
**LocallyConstant.lift_comp_proj** 是 Mathlib 中的一个定理，位于命名空间 `LocallyConstant`。
形式化陈述：lift_comp_proj : f.lift ∘ f.discreteQuotient.proj = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_comp_proj : f.lift ∘ f.discreteQuotient.proj = f := rfl

end LocallyConstant

