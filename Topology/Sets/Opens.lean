/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Order.Hom.CompleteLattice
public import Mathlib.Topology.Compactness.Bases
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.Order.Copy

/-!
# Open sets

## Summary

We define the subtype of open sets in a topological space.

## Main Definitions

### Bundled open sets

- `TopologicalSpace.Opens α` is the type of open subsets of a topological space `α`.
- `TopologicalSpace.Opens.IsBasis` is a predicate saying that a set of `Opens`s form a topological
  basis.
- `TopologicalSpace.Opens.comap`: preimage of an open set under a continuous map as a `FrameHom`.
- `Homeomorph.opensCongr`: order-preserving equivalence between open sets in the domain and the
  codomain of a homeomorphism.

### Bundled open neighborhoods

- `TopologicalSpace.OpenNhdsOf x` is the type of open subsets of a topological space `α` containing
  `x : α`.
- `TopologicalSpace.OpenNhdsOf.comap f x U` is the preimage of open neighborhood `U` of `f x` under
  `f : C(α, β)`.

## Main results

We define order structures on both `Opens α` (`CompleteLattice`, `Frame`) and `OpenNhdsOf x`
(`OrderTop`, `DistribLattice`).

## TODO

- Rename `TopologicalSpace.Opens` to `Open`?
- Port the `auto_cases` tactic version (as a plugin if the ported `auto_cases` will allow plugins).
-/

@[expose] public section

universe u

open Filter Function Order Set

open Topology

variable {ι α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

namespace TopologicalSpace

variable (α) in
/-- The type of open subsets of a topological space. -/
/-
**TopologicalSpace.Opens** 是 Mathlib 中的一个归纳类型，位于命名空间 `TopologicalSpace`。
形式化陈述：(α : Type u_2) → [TopologicalSpace α] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of open subsets of a topological space.
-/
structure Opens where
  /-- The underlying set of a bundled `TopologicalSpace.Opens` object. -/
  carrier : Set α
  /-- The `TopologicalSpace.Opens.carrier _` is an open set. -/
  is_open' : IsOpen carrier

namespace Opens

/-
**TopologicalSpace.Opens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (Opens α) α where
  coe := Opens.carrier
  coe_injective := fun ⟨_, _⟩ ⟨_, _⟩ _ => by congr
/-
**TopologicalSpace.Opens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Opens α) := fast_instance% .ofSetLike (Opens α) α
/-
**TopologicalSpace.Opens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CanLift (Set α) (Opens α) (↑) IsOpen :=
  ⟨fun s h => ⟨⟨s, h⟩, rfl⟩⟩
/-
**TopologicalSpace.Opens.instSecondCountableOpens** 是 Mathlib 中的一个实例，位于命名空间 `Top
ologicalSpace.Opens`。
形式化陈述：instSecondCountableOpens [SecondCountableTopology α] (U : Opens α) : Secon
dCountableTopology U
参数：U : Opens α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSecondCountableOpens [SecondCountableTopology α] (U : Opens α) :
    SecondCountableTopology U := inferInstanceAs (SecondCountableTopology U.1)
/-
**TopologicalSpace.Opens.** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem «forall» {p : Opens α → Prop} : (∀ U, p U) ↔ ∀ (U : Set α) (hU : IsOpen U), p ⟨U, hU⟩ :=
  ⟨fun h _ _ => h _, fun h _ => h _ _⟩
/-
**TopologicalSpace.Opens.carrier_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace.Opens`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] (U : TopologicalSpace.Opens α
), U.carrier = ↑U
参数：U : TopologicalSpace.Opens α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem carrier_eq_coe (U : Opens α) : U.1 = ↑U := rfl

/-- the coercion `Opens α → Set α` applied to a pair is the same as taking the first component -/
@[simp]
/-
**TopologicalSpace.Opens.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Open
s`。
形式化陈述：coe_mk {U : Set α} {hU : IsOpen U} : ↑(⟨U, hU⟩ : Opens α) = U
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the coercion `Opens α → Set α` applied to a pair is the same as taking the first
 component
-/
theorem coe_mk {U : Set α} {hU : IsOpen U} : ↑(⟨U, hU⟩ : Opens α) = U :=
  rfl

@[simp]
/-
**TopologicalSpace.Opens.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Open
s`。
形式化陈述：mem_mk {x : α} {U : Set α} {h : IsOpen U} : x in mk U h ↔ x in U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk {x : α} {U : Set α} {h : IsOpen U} : x ∈ mk U h ↔ x ∈ U := Iff.rfl
/-
**TopologicalSpace.Opens.nonempty_coeSort** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Space.Opens`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] {U : TopologicalSpace.Opens α
}, Nonempty ↥U ↔ (↑U).Nonempty
参数：↑U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.nonempty_coe_sort`：nonempty_coe_sort {s : Set α} : Nonempty ↥s ↔ s.N
onempty
-/
protected theorem nonempty_coeSort {U : Opens α} : Nonempty U ↔ (U : Set α).Nonempty :=
  Set.nonempty_coe_sort

-- TODO: should this theorem be proved for a `SetLike`?
/-
**TopologicalSpace.Opens.nonempty_coe** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpac
e.Opens`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] {U : TopologicalSpace.Opens α
}, (↑U).Nonempty ↔ ∃ x, x ∈ U
参数：↑U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem nonempty_coe {U : Opens α} : (U : Set α).Nonempty ↔ ∃ x, x ∈ U :=
  Iff.rfl

@[ext] -- TODO: replace with `∀ x, x ∈ U ↔ x ∈ V`?
/-
**TopologicalSpace.Opens.ext** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Opens`。
形式化陈述：ext {U V : Opens α} (h : (U : Set α) = V) : U = V
参数：h : (U : Set α) = V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem ext {U V : Opens α} (h : (U : Set α) = V) : U = V :=
  SetLike.coe_injective h
/-
**TopologicalSpace.Opens.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Ope
ns`。
形式化陈述：coe_inj {U V : Opens α} : (U : Set α) = V ↔ U = V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
-/
theorem coe_inj {U V : Opens α} : (U : Set α) = V ↔ U = V :=
  SetLike.ext'_iff.symm

/-- A version of `Set.inclusion` not requiring definitional abuse -/
/-
**TopologicalSpace.Opens.inclusion** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopologicalSpace
.Opens`。
形式化陈述：inclusion {U V : Opens α} (h : U <= V) : U -> V
参数：h : U <= V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Set.inclusion` not requiring definitional abuse
-/
abbrev inclusion {U V : Opens α} (h : U ≤ V) : U → V := Set.inclusion h
/-
**TopologicalSpace.Opens.isOpen** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Open
s`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] (U : TopologicalSpace.Opens α
), IsOpen ↑U
参数：U : TopologicalSpace.Opens α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
-/
protected theorem isOpen (U : Opens α) : IsOpen (U : Set α) :=
  U.is_open'
/-
**TopologicalSpace.Opens.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Open
s`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] (U : TopologicalSpace.Opens α
), { carrier := ↑U, is_open' := ⋯ } = U
参数：U : TopologicalSpace.Opens α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
-/
@[simp] theorem mk_coe (U : Opens α) : mk (↑U) U.isOpen = U := rfl

/-- See Note [custom simps projection]. -/
/-
**TopologicalSpace.Opens.Simps.coe** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.O
pens.Simps`。
形式化陈述：{α : Type u_2} → [inst : TopologicalSpace α] → TopologicalSpace.Opens α → 
Set α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
-/
def Simps.coe (U : Opens α) : Set α := U

initialize_simps_projections Opens (carrier → coe, as_prefix coe)

/-- The interior of a set, as an element of `Opens`. -/
@[simps]
/-
**TopologicalSpace.Opens.interior** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.Op
ens`。
形式化陈述：{α : Type u_2} → [inst : TopologicalSpace α] → Set α → TopologicalSpace.Op
ens α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)

--- 原说明 ---
The interior of a set, as an element of `Opens`.
-/
protected def interior (s : Set α) : Opens α :=
  ⟨interior s, isOpen_interior⟩

@[simp]
/-
**TopologicalSpace.Opens.mem_interior** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpac
e.Opens`。
形式化陈述：mem_interior {s : Set α} {x : α} : x in Opens.interior s ↔ x in _root_.int
erior s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_interior {s : Set α} {x : α} : x ∈ Opens.interior s ↔ x ∈ _root_.interior s := .rfl
/-
**TopologicalSpace.Opens.gc** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Opens`。
形式化陈述：gc : GaloisConnection ((↑) : Opens α -> Set α) Opens.interior
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
theorem gc : GaloisConnection ((↑) : Opens α → Set α) Opens.interior := fun U _ =>
  ⟨fun h => interior_maximal h U.isOpen, fun h => le_trans h interior_subset⟩

/-- The Galois coinsertion between sets and opens. -/
/-
**TopologicalSpace.Opens.gi** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.Opens`。
形式化陈述：gi : GaloisCoinsertion (↑) (@Opens.interior α _) where choice s hs
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.gc`：gc : GaloisConnection ((↑) : Opens α -> Set α
) Opens.interior

--- 原说明 ---
The Galois coinsertion between sets and opens.
-/
def gi : GaloisCoinsertion (↑) (@Opens.interior α _) where
  choice s hs := ⟨s, interior_eq_iff_isOpen.mp <| le_antisymm interior_subset hs⟩
  gc := gc
  u_l_le _ := interior_subset
  choice_eq _s hs := le_antisymm hs interior_subset
/-
**TopologicalSpace.Opens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLattice (Opens α) :=
  fast_instance% CompleteLattice.copy (GaloisCoinsertion.liftCompleteLattice gi)
    -- le
    (fun U V => (U : Set α) ⊆ V) rfl
    -- top
    ⟨univ, isOpen_univ⟩ (ext interior_univ.symm)
    -- bot
    ⟨∅, isOpen_empty⟩ rfl
    -- sup
    (fun U V => ⟨↑U ∪ ↑V, U.2.union V.2⟩) rfl
    -- inf
    (fun U V => ⟨↑U ∩ ↑V, U.2.inter V.2⟩)
    (funext₂ fun U V => ext (U.2.inter V.2).interior_eq.symm)
    -- sSup
    (fun S => ⟨⋃ s ∈ S, ↑s, isOpen_biUnion fun s _ => s.2⟩)
    (funext fun _ => ext sSup_image.symm)
    -- sInf
    _ rfl

@[simp]
/-
**TopologicalSpace.Opens.mk_inf_mk** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.O
pens`。
形式化陈述：mk_inf_mk {U V : Set α} {hU : IsOpen U} {hV : IsOpen V} : (⟨U, hU⟩ ⊓ ⟨V, h
V⟩ : Opens α) = ⟨U ⊓ V, IsOpen.inter hU hV⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_inf_mk {U V : Set α} {hU : IsOpen U} {hV : IsOpen V} :
    (⟨U, hU⟩ ⊓ ⟨V, hV⟩ : Opens α) = ⟨U ⊓ V, IsOpen.inter hU hV⟩ :=
  rfl

@[simp, norm_cast]
/-
**TopologicalSpace.Opens.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Ope
ns`。
形式化陈述：coe_inf (s t : Opens α) : (↑(s ⊓ t) : Set α) = ↑s inter ↑t
参数：s t : Opens α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf (s t : Opens α) : (↑(s ⊓ t) : Set α) = ↑s ∩ ↑t :=
  rfl

@[simp]
/-
**TopologicalSpace.Opens.mem_inf** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpace.Ope
ns`。
形式化陈述：mem_inf {s t : Opens α} {x : α} : x in s ⊓ t ↔ x in s ∧ x in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_inf {s t : Opens α} {x : α} : x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t := Iff.rfl

@[simp, norm_cast]
/-
**TopologicalSpace.Opens.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Ope
ns`。
形式化陈述：coe_sup (s t : Opens α) : (↑(s ⊔ t) : Set α) = ↑s union ↑t
参数：s t : Opens α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup (s t : Opens α) : (↑(s ⊔ t) : Set α) = ↑s ∪ ↑t :=
  rfl

@[simp]
/-
**TopologicalSpace.Opens.mem_sup** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Ope
ns`。
形式化陈述：mem_sup {s t : Opens α} {x : α} : x in (s ⊔ t) ↔ x in s ∨ x in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_sup {s t : Opens α} {x : α} : x ∈ (s ⊔ t) ↔ x ∈ s ∨ x ∈ t :=
  .rfl

@[simp, norm_cast]
/-
**TopologicalSpace.Opens.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Ope
ns`。
形式化陈述：coe_bot : ((⊥ : Opens α) : Set α) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot : ((⊥ : Opens α) : Set α) = ∅ :=
  rfl

@[simp]
/-
**TopologicalSpace.Opens.mem_bot** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpace.Ope
ns`。
形式化陈述：mem_bot {x : α} : x in (⊥ : Opens α) ↔ False
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_bot {x : α} : x ∈ (⊥ : Opens α) ↔ False := Iff.rfl
/-
**TopologicalSpace.Opens.mk_empty** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Op
ens`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α], { carrier := ∅, is_open' := 
⋯ } = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
-/
@[simp] theorem mk_empty : (⟨∅, isOpen_empty⟩ : Opens α) = ⊥ := rfl

@[simp, norm_cast]
/-
**TopologicalSpace.Opens.coe_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpac
e.Opens`。
形式化陈述：coe_eq_empty {U : Opens α} : (U : Set α) = ∅ ↔ U = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem coe_eq_empty {U : Opens α} : (U : Set α) = ∅ ↔ U = ⊥ :=
  SetLike.coe_injective.eq_iff' rfl

@[simp]
/-
**TopologicalSpace.Opens.mem_top** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpace.Ope
ns`。
形式化陈述：mem_top (x : α) : x in (⊤ : Opens α)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
lemma mem_top (x : α) : x ∈ (⊤ : Opens α) := trivial

@[simp, norm_cast]
/-
**TopologicalSpace.Opens.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Ope
ns`。
形式化陈述：coe_top : ((⊤ : Opens α) : Set α) = Set.univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : ((⊤ : Opens α) : Set α) = Set.univ :=
  rfl
/-
**TopologicalSpace.Opens.mk_univ** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Ope
ns`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α], { carrier := Set.univ, is_op
en' := ⋯ } = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
-/
@[simp] theorem mk_univ : (⟨univ, isOpen_univ⟩ : Opens α) = ⊤ := rfl

@[simp, norm_cast]
/-
**TopologicalSpace.Opens.coe_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace
.Opens`。
形式化陈述：coe_eq_univ {U : Opens α} : (U : Set α) = univ ↔ U = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem coe_eq_univ {U : Opens α} : (U : Set α) = univ ↔ U = ⊤ :=
  SetLike.coe_injective.eq_iff' rfl

@[simp, norm_cast]
/-
**TopologicalSpace.Opens.coe_sSup** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Op
ens`。
形式化陈述：coe_sSup {S : Set (Opens α)} : (↑(sSup S) : Set α) = ⋃ i in S, ↑i
参数：Opens α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sSup {S : Set (Opens α)} : (↑(sSup S) : Set α) = ⋃ i ∈ S, ↑i :=
  rfl

@[simp, norm_cast]
/-
**TopologicalSpace.Opens.coe_finset_sup** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace.Opens`。
形式化陈述：coe_finset_sup (f : ι -> Opens α) (s : Finset ι) : (↑(s.sup f) : Set α) = 
s.sup ((↑) ∘ f)
参数：f : ι -> Opens α；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finset_sup`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Type
 u_5} [inst : SemilatticeSup α] [inst_1 : OrderBot α]   [inst_2 : SemilatticeSup
 β] …
· 使用定理 `SupBotHom.instSupBotHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : Ma
x α] [inst_1 : Bot α] [inst_2 : Max β] [inst_3 : Bot β],   SupBotHomClass (SupBo
tHom α β) α β
· 使用定理 `TopologicalSpace.Opens.coe_sup`：coe_sup (s t : Opens α) : (↑(s ⊔ t) : Se
t α) = ↑s union ↑t
· 使用定理 `TopologicalSpace.Opens.coe_bot`：coe_bot : ((⊥ : Opens α) : Set α) = ∅
-/
theorem coe_finset_sup (f : ι → Opens α) (s : Finset ι) : (↑(s.sup f) : Set α) = s.sup ((↑) ∘ f) :=
  map_finset_sup (⟨⟨(↑), coe_sup⟩, coe_bot⟩ : SupBotHom (Opens α) (Set α)) _ _

@[simp, norm_cast]
/-
**TopologicalSpace.Opens.coe_finset_inf** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace.Opens`。
形式化陈述：coe_finset_inf (f : ι -> Opens α) (s : Finset ι) : (↑(s.inf f) : Set α) = 
s.inf ((↑) ∘ f)
参数：f : ι -> Opens α；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finset_inf`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Type
 u_5} [inst : SemilatticeInf α] [inst_1 : OrderTop α]   [inst_2 : SemilatticeInf
 β] …
· 使用定理 `InfTopHom.instInfTopHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : Mi
n α] [inst_1 : Top α] [inst_2 : Min β] [inst_3 : Top β],   InfTopHomClass (InfTo
pHom α β) α β
· 使用定理 `TopologicalSpace.Opens.coe_inf`：coe_inf (s t : Opens α) : (↑(s ⊓ t) : Se
t α) = ↑s inter ↑t
· 使用定理 `TopologicalSpace.Opens.coe_top`：coe_top : ((⊤ : Opens α) : Set α) = Set.
univ
-/
theorem coe_finset_inf (f : ι → Opens α) (s : Finset ι) : (↑(s.inf f) : Set α) = s.inf ((↑) ∘ f) :=
  map_finset_inf (⟨⟨(↑), coe_inf⟩, coe_top⟩ : InfTopHom (Opens α) (Set α)) _ _

@[simp, norm_cast]
/-
**TopologicalSpace.Opens.coe_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpac
e.Opens`。
形式化陈述：coe_disjoint {s t : Opens α} : Disjoint (s : Set α) t ↔ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_disjoint {s t : Opens α} : Disjoint (s : Set α) t ↔ Disjoint s t := by
  simp [disjoint_iff, ← SetLike.coe_set_eq]
/-
**TopologicalSpace.Opens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Opens α) := ⟨⊥⟩
/-
**TopologicalSpace.Opens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty α] : Unique (Opens α) where
  uniq _ := ext <| Subsingleton.elim _ _
/-
**TopologicalSpace.Opens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] : Nontrivial (Opens α) where
  exists_pair_ne := ⟨⊥, ⊤, mt coe_inj.2 empty_ne_univ⟩

@[simp, norm_cast]
/-
**TopologicalSpace.Opens.coe_iSup** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Op
ens`。
形式化陈述：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i, s i : Opens α) : Set α) = ⋃ i, s 
i
参数：s : ι -> Opens α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iUnion_iUnion_eq'`：iUnion_iUnion_eq' {f : ι -> α} {g : α -> Set β} :
 ⋃ (x) (y) (_ : f y = x), g x = ⋃ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_iSup {ι} (s : ι → Opens α) : ((⨆ i, s i : Opens α) : Set α) = ⋃ i, s i := by
  simp [iSup]
/-
**TopologicalSpace.Opens.coe_iInf** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpace.Op
ens`。
形式化陈述：coe_iInf {ι : Type*} [Finite ι] (U : ι -> TopologicalSpace.Opens α) : (((⨅
 i, U i) : Opens α) : Set α) = ⋂ i, U i
参数：U : ι -> TopologicalSpace.Opens α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.induction_empty_option`：Finite.induction_empty_option {P : Type u
 -> Prop} (of_equiv : forall {α β}, α ≃ β -> P α -> P β) (h_empty : P PEmpty) (h
_option : forall {α…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.iInf_comp`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst :
 InfSet α] {g : ι' → α} (e : ι ≃ ι'), ⨅ x, g (e x) = ⨅ y, g y
· 使用定理 `Function.Surjective.iInter_comp`：iInter_comp {f : ι -> ι₂} (hf : Surject
ive f) (g : ι₂ -> Set α) : ⋂ x, g (f x) = ⋂ y, g y
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iInter_of_empty`：iInter_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋂ i,
 s i = univ
· 使用定理 `iInf_option`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] 
(f : Option β → α), ⨅ o, f o = f none ⊓ ⨅ b, f (some b)
· 使用定理 `Set.iInter_option`：iInter_option {ι} (s : Option ι -> Set α) : ⋂ o, s o 
= s none inter ⋂ i, s (some i)
· 使用定理 `TopologicalSpace.Opens.coe_inf`：coe_inf (s t : Opens α) : (↑(s ⊓ t) : Se
t α) = ↑s inter ↑t
-/
lemma coe_iInf {ι : Type*} [Finite ι] (U : ι → TopologicalSpace.Opens α) :
    (((⨅ i, U i) : Opens α) : Set α) = ⋂ i, U i := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih => rw [← e.iInf_comp, ← e.surjective.iInter_comp, ih]
  | h_empty => simp
  | h_option ih => rw [iInf_option, Set.iInter_option, Opens.coe_inf, ih]
/-
**TopologicalSpace.Opens.iSup_def** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Op
ens`。
形式化陈述：iSup_def {ι} (s : ι -> Opens α) : ⨆ i, s i = ⟨⋃ i, s i, isOpen_iUnion fun 
i => (s i).2⟩
参数：s : ι -> Opens α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `TopologicalSpace.Opens.coe_iSup`：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i
, s i : Opens α) : Set α) = ⋃ i, s i
-/
theorem iSup_def {ι} (s : ι → Opens α) : ⨆ i, s i = ⟨⋃ i, s i, isOpen_iUnion fun i => (s i).2⟩ :=
  ext <| coe_iSup s

@[simp]
/-
**TopologicalSpace.Opens.iSup_mk** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Ope
ns`。
形式化陈述：iSup_mk {ι} (s : ι -> Set α) (h : forall i, IsOpen (s i)) : (⨆ i, ⟨s i, h 
i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
参数：s : ι -> Set α；h : forall i, IsOpen (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.iSup_def`：iSup_def {ι} (s : ι -> Opens α) : ⨆ i, 
s i = ⟨⋃ i, s i, isOpen_iUnion fun i => (s i).2⟩
-/
theorem iSup_mk {ι} (s : ι → Set α) (h : ∀ i, IsOpen (s i)) :
    (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩ :=
  iSup_def _

@[simp]
/-
**TopologicalSpace.Opens.mem_iSup** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Op
ens`。
形式化陈述：mem_iSup {ι} {x : α} {s : ι -> Opens α} : x in iSup s ↔ exists i, x in s i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopologicalSpace.Opens.coe_iSup`：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i
, s i : Opens α) : Set α) = ⋃ i, s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_iSup {ι} {x : α} {s : ι → Opens α} : x ∈ iSup s ↔ ∃ i, x ∈ s i := by
  rw [← SetLike.mem_coe]
  simp

@[simp]
/-
**TopologicalSpace.Opens.mem_sSup** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Op
ens`。
形式化陈述：mem_sSup {Us : Set (Opens α)} {x : α} : x in sSup Us ↔ exists u in Us, x i
n u
参数：Opens α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_sSup {Us : Set (Opens α)} {x : α} : x ∈ sSup Us ↔ ∃ u ∈ Us, x ∈ u := by
  simp_rw [sSup_eq_iSup, mem_iSup, exists_prop]
/-
**TopologicalSpace.Opens.instFrame** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.O
pens`。
形式化陈述：instFrame : Frame (Opens α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFrame : Frame (Opens α) := fast_instance% .ofMinimalAxioms {
  inf_sSup_le_iSup_inf a s :=
    (ext <| by simp only [coe_inf, coe_iSup, coe_sSup, Set.inter_iUnion₂]).le }
/-
**TopologicalSpace.Opens.mem_himp** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Op
ens`。
形式化陈述：mem_himp {U V : Opens α} {x : α} : x in U ⇨ V ↔ exists W : Opens α, W ⊓ U 
<= V ∧ x in W
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `himp_eq_sSup`：∀ {α : Type u} [inst : Order.Frame α] {a b : α}, a ⇨ b = s
Sup {w | w ⊓ a ≤ b}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_himp {U V : Opens α} {x : α} : x ∈ U ⇨ V ↔ ∃ W : Opens α, W ⊓ U ≤ V ∧ x ∈ W := by
  simp [himp_eq_sSup]
/-
**TopologicalSpace.Opens.himp_def** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Op
ens`。
形式化陈述：himp_def {U V : Opens α} : U ⇨ V = Opens.interior ((U : Set α) ⇨ V)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BooleanAlgebra.himp_eq`：∀ {α : Type u} [self : BooleanAlgebra α] (x y : 
α), x ⇨ y = y ⊔ xᶜ
· 使用定理 `TopologicalSpace.Opens.coe_interior`：∀ {α : Type u_2} [inst : Topologica
lSpace α] (s : Set α), ↑(TopologicalSpace.Opens.interior s) = interior s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
-/
theorem himp_def {U V : Opens α} : U ⇨ V = Opens.interior ((U : Set α) ⇨ V) := by
  ext x
  simp_rw [BooleanAlgebra.himp_eq, sup_eq_union, coe_interior, _root_.mem_interior,
    SetLike.mem_coe, mem_himp, ← SetLike.coe_subset_coe, coe_inf, inter_subset]
  exact ⟨fun ⟨⟨W, hW⟩, hsub, hx⟩ => ⟨W, union_comm _ _ ▸ hsub, hW, hx⟩,
    fun ⟨W, hsub, hW, hx⟩ => ⟨⟨W, hW⟩, union_comm _ _ ▸ hsub, hx⟩⟩
/-
**TopologicalSpace.Opens.coe_himp** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Op
ens`。
形式化陈述：coe_himp {U V : Opens α} : ↑(U ⇨ V) = interior ((U : Set α) ⇨ V)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.himp_def`：himp_def {U V : Opens α} : U ⇨ V = Open
s.interior ((U : Set α) ⇨ V)
· 使用定理 `TopologicalSpace.Opens.coe_interior`：∀ {α : Type u_2} [inst : Topologica
lSpace α] (s : Set α), ↑(TopologicalSpace.Opens.interior s) = interior s
-/
theorem coe_himp {U V : Opens α} : ↑(U ⇨ V) = interior ((U : Set α) ⇨ V) := by
  rw [himp_def, coe_interior]
/-
**TopologicalSpace.Opens.mem_compl** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.O
pens`。
形式化陈述：mem_compl {U : Opens α} {x : α} : x in Uᶜ ↔ exists V : Opens α, Disjoint V
 U ∧ x in V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_eq_sSup_disjoint`：∀ {α : Type u} [inst : Order.Frame α] {a : α}, a
ᶜ = sSup {w | Disjoint w a}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_compl {U : Opens α} {x : α} : x ∈ Uᶜ ↔ ∃ V : Opens α, Disjoint V U ∧ x ∈ V := by
  simp [compl_eq_sSup_disjoint]
/-
**TopologicalSpace.Opens.interior_compl** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace.Opens`。
形式化陈述：interior_compl {U : Opens α} : Opens.interior (U : Set α)ᶜ = Uᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.himp_def`：himp_def {U V : Opens α} : U ⇨ V = Open
s.interior ((U : Set α) ⇨ V)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem interior_compl {U : Opens α} : Opens.interior (U : Set α)ᶜ = Uᶜ := by
  simp [← himp_bot, himp_def]
/-
**TopologicalSpace.Opens.coe_compl_eq_interior_compl** 是 Mathlib 中的一个定理，位于命名空间 `
TopologicalSpace.Opens`。
形式化陈述：coe_compl_eq_interior_compl {U : Opens α} : ↑(Uᶜ) = interior (U : Set α)ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.Opens.interior_compl`：interior_compl {U : Opens α} : Op
ens.interior (U : Set α)ᶜ = Uᶜ
· 使用定理 `TopologicalSpace.Opens.coe_interior`：∀ {α : Type u_2} [inst : Topologica
lSpace α] (s : Set α), ↑(TopologicalSpace.Opens.interior s) = interior s
-/
theorem coe_compl_eq_interior_compl {U : Opens α} : ↑(Uᶜ) = interior (U : Set α)ᶜ := by
  rw [← interior_compl, coe_interior]

/-- The coercion from open sets to sets as a `FrameHom`. -/
/-
**TopologicalSpace.Opens.frameHom** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.Op
ens`。
形式化陈述：{α : Type u_2} → [inst : TopologicalSpace α] → FrameHom (TopologicalSpace.
Opens α) (Set α)
参数：TopologicalSpace.Opens α；Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion from open sets to sets as a `FrameHom`.
-/
@[simps] protected def frameHom : FrameHom (Opens α) (Set α) where
  toFun := (·)
  map_inf' _ _ := rfl
  map_top' := rfl
  map_sSup' _ := by simp
/-
**TopologicalSpace.Opens.isOpenEmbedding'** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Space.Opens`。
形式化陈述：isOpenEmbedding' (U : Opens α) : IsOpenEmbedding (Subtype.val : U -> α)
参数：U : Opens α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
-/
theorem isOpenEmbedding' (U : Opens α) : IsOpenEmbedding (Subtype.val : U → α) :=
  U.isOpen.isOpenEmbedding_subtypeVal
/-
**TopologicalSpace.Opens.isOpenEmbedding_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Topolo
gicalSpace.Opens`。
形式化陈述：isOpenEmbedding_of_le {U V : Opens α} (i : U <= V) : IsOpenEmbedding (Set.
inclusion <| SetLike.coe_subset_coe.2 i) where toIsEmbedding
参数：i : U <= V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Topology.IsEmbedding.inclusion`：∀ {X : Type u} [inst : TopologicalSpace 
X] {s t : Set X} (h : s ⊆ t), Topology.IsEmbedding (Set.inclusion h)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_inclusion`：range_inclusion (h : s subseteq t) : range (inclusi
on h) = { x : t | (x : α) in s }
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
-/
theorem isOpenEmbedding_of_le {U V : Opens α} (i : U ≤ V) :
    IsOpenEmbedding (Set.inclusion <| SetLike.coe_subset_coe.2 i) where
  toIsEmbedding := .inclusion i
  isOpen_range := by
    rw [Set.range_inclusion i]
    exact U.isOpen.preimage continuous_subtype_val
/-
**TopologicalSpace.Opens.not_nonempty_iff_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logicalSpace.Opens`。
形式化陈述：not_nonempty_iff_eq_bot (U : Opens α) : ¬Set.Nonempty (U : Set α) ↔ U = ⊥
参数：U : Opens α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.Opens.coe_inj`：coe_inj {U V : Opens α} : (U : Set α) = 
V ↔ U = V
· 使用定理 `TopologicalSpace.Opens.coe_bot`：coe_bot : ((⊥ : Opens α) : Set α) = ∅
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_nonempty_iff_eq_bot (U : Opens α) : ¬Set.Nonempty (U : Set α) ↔ U = ⊥ := by
  rw [← coe_inj, coe_bot, ← Set.not_nonempty_iff_eq_empty]
/-
**TopologicalSpace.Opens.ne_bot_iff_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Topologi
calSpace.Opens`。
形式化陈述：ne_bot_iff_nonempty (U : Opens α) : U != ⊥ ↔ Set.Nonempty (U : Set α)
参数：U : Opens α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.Opens.not_nonempty_iff_eq_bot`：not_nonempty_iff_eq_bot 
(U : Opens α) : ¬Set.Nonempty (U : Set α) ↔ U = ⊥
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ne_bot_iff_nonempty (U : Opens α) : U ≠ ⊥ ↔ Set.Nonempty (U : Set α) := by
  rw [Ne, ← not_nonempty_iff_eq_bot, not_not]
/-
**TopologicalSpace.Opens.eq_bot_or_top** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpa
ce.Opens`。
形式化陈述：eq_bot_or_top [IndiscreteTopology α] (U : Opens α) : U = ⊥ ∨ U = ⊤
参数：U : Opens α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.Opens.coe_eq_empty`：coe_eq_empty {U : Opens α} : (U : S
et α) = ∅ ↔ U = ⊥
· 使用定理 `TopologicalSpace.Opens.coe_eq_univ`：coe_eq_univ {U : Opens α} : (U : Set
 α) = univ ↔ U = ⊤
· 使用定理 `IndiscreteTopology.isOpen_iff`：IndiscreteTopology.isOpen_iff [Indiscrete
Topology α] (U : Set α) : IsOpen U ↔ U = ∅ ∨ U = univ
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
-/
theorem eq_bot_or_top [IndiscreteTopology α] (U : Opens α) :
    U = ⊥ ∨ U = ⊤ := by
  rw [← coe_eq_empty, ← coe_eq_univ, ← IndiscreteTopology.isOpen_iff]
  exact U.2
/-
**TopologicalSpace.Opens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] [IndiscreteTopology α] : IsSimpleOrder (Opens α) where
  eq_bot_or_eq_top := eq_bot_or_top

/-- A set of `opens α` is a basis if the set of corresponding sets is a topological basis. -/
/-
**TopologicalSpace.Opens.IsBasis** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.Ope
ns`。
形式化陈述：IsBasis (B : Set (Opens α)) : Prop
参数：B : Set (Opens α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set of `opens α` is a basis if the set of corresponding sets is a topological 
basis.
-/
def IsBasis (B : Set (Opens α)) : Prop :=
  IsTopologicalBasis (((↑) : _ → Set α) '' B)
/-
**TopologicalSpace.Opens.isBasis_iff_nbhd** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Space.Opens`。
形式化陈述：isBasis_iff_nbhd {B : Set (Opens α)} : IsBasis B ↔ forall {U : Opens α} {x
}, x in U -> exists U' in B, x in U' ∧ U' <= U
参数：Opens α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.IsTopologicalBasis.mem_nhds_iff`：∀ {α : Type u} [t : To
pologicalSpace α] {a : α} {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTo
pologicalBasis b → (s ∈ nhds a ↔ ∃ t ∈…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds`：isTopologicalBasi
s_of_isOpen_of_nhds {s : Set (Set α)} (h_open : forall u in s, IsOpen u) (h_nhds
 : forall (a : α) (u : Set α), a in u -> Is…
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
-/
theorem isBasis_iff_nbhd {B : Set (Opens α)} :
    IsBasis B ↔ ∀ {U : Opens α} {x}, x ∈ U → ∃ U' ∈ B, x ∈ U' ∧ U' ≤ U := by
  constructor <;> intro h
  · rintro ⟨sU, hU⟩ x hx
    rcases h.mem_nhds_iff.mp (IsOpen.mem_nhds hU hx) with ⟨sV, ⟨⟨V, H₁, H₂⟩, hsV⟩⟩
    refine ⟨V, H₁, ?_⟩
    cases V
    dsimp at H₂
    subst H₂
    exact hsV
  · refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro sU ⟨U, -, rfl⟩
      exact U.2
    · intro x sU hx hsU
      rcases @h ⟨sU, hsU⟩ x hx with ⟨V, hV, H⟩
      exact ⟨V, ⟨V, hV, rfl⟩, H⟩
/-
**TopologicalSpace.Opens.isBasis_iff_cover** 是 Mathlib 中的一个定理，位于命名空间 `Topologica
lSpace.Opens`。
形式化陈述：isBasis_iff_cover {B : Set (Opens α)} : IsBasis B ↔ forall U : Opens α, ex
ists Us, Us subseteq B ∧ U = sSup Us
参数：Opens α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.coe_sSup`：coe_sSup {S : Set (Opens α)} : (↑(sSup 
S) : Set α) = ⋃ i in S, ↑i
· 使用定理 `TopologicalSpace.IsTopologicalBasis.open_eq_sUnion'`：∀ {α : Type u} [t :
 TopologicalSpace α] {B : Set (Set α)},   TopologicalSpace.IsTopologicalBasis B 
→ ∀ {u : Set α}, IsOpen u → u = ⋃₀ {s | s…
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_and`：iSup_and {p q : Prop} {s : p ∧ q -> α} : iSup s = ⨆ (h₁) (h₂),
 s ⟨h₁, h₂⟩
· 使用定理 `iSup_image`：iSup_image {γ} {f : β -> γ} {g : γ -> α} {t : Set β} : ⨆ c i
n f '' t, g c = ⨆ b in t, g (f b)
· 使用定理 `TopologicalSpace.Opens.isBasis_iff_nbhd`：isBasis_iff_nbhd {B : Set (Open
s α)} : IsBasis B ↔ forall {U : Opens α} {x}, x in U -> exists U' in B, x in U' 
∧ U' <= U
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.Opens.mem_sSup`：mem_sSup {Us : Set (Opens α)} {x : α} :
 x in sSup Us ↔ exists u in Us, x in u
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isBasis_iff_cover {B : Set (Opens α)} :
    IsBasis B ↔ ∀ U : Opens α, ∃ Us, Us ⊆ B ∧ U = sSup Us := by
  constructor
  · intro hB U
    refine ⟨{ V : Opens α | V ∈ B ∧ V ≤ U }, fun U hU => hU.left, ext ?_⟩
    rw [coe_sSup, hB.open_eq_sUnion' U.isOpen]
    simp_rw [sUnion_eq_biUnion, iUnion, mem_ofPred_eq, iSup_and, iSup_image]
    rfl
  · intro h
    rw [isBasis_iff_nbhd]
    intro U x hx
    rcases h U with ⟨Us, hUs, rfl⟩
    rcases mem_sSup.1 hx with ⟨U, Us, xU⟩
    exact ⟨U, hUs Us, xU, le_sSup Us⟩
/-
**TopologicalSpace.Opens.IsBasis.exists_iSup_eq** 是 Mathlib 中的一个定理，位于命名空间 `Topol
ogicalSpace.Opens.IsBasis`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {ι : Type u_5} {U : ι → Topolog
icalSpace.Opens X},   TopologicalSpace.Opens.IsBasis (Set.range U) → ∀ (W : Topo
logicalSpace.Opens X), ∃ κ a, W = ⨆ k, U (a k)
参数：Set.range U；W : TopologicalSpace.Opens X；a k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.Opens.isBasis_iff_cover`：isBasis_iff_cover {B : Set (Op
ens α)} : IsBasis B ↔ forall U : Opens α, exists Us, Us subseteq B ∧ U = sSup Us
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sSup_eq_iSup'`：sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α)
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma IsBasis.exists_iSup_eq {X : Type u} [TopologicalSpace X] {ι : Type*}
    {U : ι → TopologicalSpace.Opens X} (hU : TopologicalSpace.Opens.IsBasis (Set.range U))
    (W : TopologicalSpace.Opens X) : ∃ (κ : Type u) (a : κ → ι), W = ⨆ (k : κ), U (a k) := by
  obtain ⟨Us, hsub, hUs⟩ := Opens.isBasis_iff_cover.mp hU W
  choose a ha using hsub
  use Us, fun i ↦ a i.2
  simp [hUs, ha, sSup_eq_iSup' Us]
/-
**TopologicalSpace.Opens.IsBasis.exists_iSup_eq_of_isCompact** 是 Mathlib 中的一个定理，
位于命名空间 `TopologicalSpace.Opens.IsBasis`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {ι : Type u_5} {U : ι → Topolog
icalSpace.Opens X},   TopologicalSpace.Opens.IsBasis (Set.range U) →     ∀ (W : 
TopologicalSpace.Opens X), IsCompact W.carrier → ∃ κ, ∃ (_ : Finite κ), ∃ a, W =
 ⨆ k, U (a k)
参数：Set.range U；W : TopologicalSpace.Opens X；_ : Finite κ；a k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.IsBasis.exists_iSup_eq`：∀ {X : Type u} [inst : To
pologicalSpace X] {ι : Type u_5} {U : ι → TopologicalSpace.Opens X},   Topologic
alSpace.Opens.IsBasis (Set.range U)…
· 使用定理 `IsCompact.elim_finite_subcover`：IsCompact.elim_finite_subcover {ι : Type
 v} (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s 
subseteq ⋃ i, U i) :…
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Set.iUnion_subtype`：iUnion_subtype (p : α -> Prop) (s : { x // p x } -> 
Set β) : ⋃ x : { x // p x }, s x = ⋃ (x) (hx : p x), s ⟨x, hx⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma IsBasis.exists_iSup_eq_of_isCompact {X : Type u} [TopologicalSpace X] {ι : Type*}
    {U : ι → TopologicalSpace.Opens X} (hU : TopologicalSpace.Opens.IsBasis (Set.range U))
    (W : TopologicalSpace.Opens X) (hW : IsCompact W.1) :
    ∃ (κ : Type u) (_ : Finite κ) (a : κ → ι), W = ⨆ (k : κ), U (a k) := by
  obtain ⟨κ, a, heq⟩ := hU.exists_iSup_eq W
  obtain ⟨s, hs⟩ := hW.elim_finite_subcover _ (fun k : κ ↦ (U (a k)).2) (by simp [heq])
  use s, s.finite_toSet, a ∘ Subtype.val
  refine le_antisymm ?_ ?_
  · simpa [← SetLike.coe_subset_coe, Set.iUnion_subtype]
  · rw [heq, iSup_le_iff]
    intro i
    exact le_iSup_of_le _ le_rfl

/-- If `α` has a basis consisting of compact opens, then an open set in `α` is compact open iff
  it is a finite union of some elements in the basis -/
/-
**TopologicalSpace.Opens.IsBasis.isCompact_open_iff_eq_finite_iUnion** 是 Mathlib
 中的一个定理，位于命名空间 `TopologicalSpace.Opens.IsBasis`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] {ι : Type u_5} (b : ι → Topol
ogicalSpace.Opens α),   TopologicalSpace.Opens.IsBasis (Set.range b) →     (∀ (i
 : ι), IsCompact ↑(b i)) → ∀ (U : Set α), IsCompact U ∧ IsOpen U ↔ ∃ s, s.Finite
 ∧ U = ⋃ i ∈ s, ↑(b i)
参数：b : ι → TopologicalSpace.Opens α；Set.range b；∀ (i : ι), IsCompact ↑(b i)；U : 
Set α；b i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis`：isCompact_ope
n_iff_eq_finite_iUnion_of_isTopologicalBasis (b : ι -> Set X) (hb : IsTopologica
lBasis (Set.range b)) (hb' : forall i, IsCompac…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `α` has a basis consisting of compact opens, then an open set in `α` is compa
ct open iff
  it is a finite union of some elements in the basis
-/
theorem IsBasis.isCompact_open_iff_eq_finite_iUnion {ι : Type*} (b : ι → Opens α)
    (hb : IsBasis (Set.range b)) (hb' : ∀ i, IsCompact (b i : Set α)) (U : Set α) :
    IsCompact U ∧ IsOpen U ↔ ∃ s : Set ι, s.Finite ∧ U = ⋃ i ∈ s, b i := by
  apply isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis fun i : ι => (b i).1
  · convert! (config := { transparency := .default }) hb
    ext
    simp
  · exact hb'
/-
**TopologicalSpace.Opens.IsBasis.exists_finite_of_isCompact** 是 Mathlib 中的一个定理，位
于命名空间 `TopologicalSpace.Opens.IsBasis`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] {B : Set (TopologicalSpace.Op
ens α)},   TopologicalSpace.Opens.IsBasis B →     ∀ {U : TopologicalSpace.Opens 
α}, IsCompact U.carrier → ∃ Us ⊆ B, Us.Finite ∧ U = sSup Us
参数：TopologicalSpace.Opens α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.Opens.isBasis_iff_cover`：isBasis_iff_cover {B : Set (Op
ens α)} : IsBasis B ↔ forall U : Opens α, exists Us, Us subseteq B ∧ U = sSup Us
· 使用定理 `IsCompact.elim_finite_subcover`：IsCompact.elim_finite_subcover {ι : Type
 v} (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s 
subseteq ⋃ i, U i) :…
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `sSup_le_sSup`：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
lemma IsBasis.exists_finite_of_isCompact {B : Set (Opens α)} (hB : IsBasis B) {U : Opens α}
    (hU : IsCompact U.1) : ∃ Us ⊆ B, Us.Finite ∧ U = sSup Us := by
  classical
  obtain ⟨Us', hsub, hsup⟩ := isBasis_iff_cover.mp hB U
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun s : Us' ↦ s.1) (fun s ↦ s.1.2) (by simp [hsup])
  refine ⟨Finset.image Subtype.val t, subset_trans (by simp) hsub, Finset.finite_toSet _, ?_⟩
  exact le_antisymm (subset_trans (a := U.carrier) ht (by simp))
    (le_trans (sSup_le_sSup (by simp)) hsup.ge)
/-
**TopologicalSpace.Opens.IsBasis.le_iff** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSp
ace.Opens.IsBasis`。
形式化陈述：∀ {α : Type u_5} {t₁ t₂ : TopologicalSpace α} {Us : Set (TopologicalSpace.
Opens α)},   TopologicalSpace.Opens.IsBasis Us → (t₁ ≤ t₂ ↔ ∀ U ∈ Us, IsOpen ↑U)
参数：TopologicalSpace.Opens α；t₁ ≤ t₂ ↔ ∀ U ∈ Us, IsOpen ↑U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.IsTopologicalBasis.eq_generateFrom`：∀ {α : Type u} [t :
 TopologicalSpace α] {s : Set (Set α)},   TopologicalSpace.IsTopologicalBasis s 
→ t = TopologicalSpace.generateFrom s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IsBasis.le_iff {α} {t₁ t₂ : TopologicalSpace α}
    {Us : Set (Opens α)} (hUs : @IsBasis α t₂ Us) :
    t₁ ≤ t₂ ↔ ∀ U ∈ Us, IsOpen[t₁] U := by
  conv_lhs => rw [hUs.eq_generateFrom]
  simp [Set.subset_def, le_generateFrom_iff_subset_isOpen]
/-
**TopologicalSpace.Opens.isBasis_sigma** 是 Mathlib 中的一个引理，位于命名空间 `TopologicalSpa
ce.Opens`。
形式化陈述：isBasis_sigma {ι : Type*} {α : ι -> Type*} [forall i, TopologicalSpace (α 
i)] {B : forall i, Set (Opens (α i))} (hB : forall i, IsBasis (B i)) : IsBasis (
⋃ i : ι, (fun U => ⟨Sigma.mk i '' U.1, isOpenMap_sigmaMk _ U.2⟩) '' B i)
参数：α i；Opens (α i)；hB : forall i, IsBasis (B i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpenMap_sigmaMk`：isOpenMap_sigmaMk {i : ι} : IsOpenMap (@Sigma.mk ι σ 
i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `TopologicalSpace.IsTopologicalBasis.sigma`：∀ {ι : Type u_1} {E : ι → Typ
e u_2} [inst : (i : ι) → TopologicalSpace (E i)] {s : (i : ι) → Set (Set (E i))}
,   (∀ (i : ι), TopologicalSpac…
-/
lemma isBasis_sigma {ι : Type*} {α : ι → Type*} [∀ i, TopologicalSpace (α i)]
    {B : ∀ i, Set (Opens (α i))} (hB : ∀ i, IsBasis (B i)) :
    IsBasis (⋃ i : ι, (fun U ↦ ⟨Sigma.mk i '' U.1, isOpenMap_sigmaMk _ U.2⟩) '' B i) := by
  convert! TopologicalSpace.IsTopologicalBasis.sigma hB
  simp only [IsBasis, Set.image_iUnion, ← Set.image_comp]
  simp
/-
**TopologicalSpace.Opens.IsBasis.of_isInducing** 是 Mathlib 中的一个定理，位于命名空间 `Topolo
gicalSpace.Opens.IsBasis`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β]   {B : Set (TopologicalSpace.Opens β)},   TopologicalSpace.Opens
.IsBasis B →     ∀ {f : α → β} (h : Topology.IsInducing f),       TopologicalSpa
ce.Opens.IsBasis {x | ∃ U ∈ B, { carrier := f ⁻¹' ↑U, is_open' := ⋯ } = x}
参数：TopologicalSpace.Opens β；h : Topology.IsInducing f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `TopologicalSpace.IsTopologicalBasis.isInducing`：∀ {α : Type u} {β : Type
 u_1} [t : TopologicalSpace α] [inst : TopologicalSpace β] {f : α → β} {T : Set 
(Set β)},   Topology.IsInducing f → …
-/
lemma IsBasis.of_isInducing {B : Set (Opens β)} (H : IsBasis B) {f : α → β} (h : IsInducing f) :
    IsBasis { ⟨f ⁻¹' U, U.2.preimage h.continuous⟩ | U ∈ B } := by
  simp only [IsBasis] at H ⊢
  convert! H.isInducing h
  ext; simp

@[simp]
/-
**TopologicalSpace.Opens.isCompactElement_iff** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
icalSpace.Opens`。
形式化陈述：isCompactElement_iff (s : Opens α) : IsCompactElement s ↔ IsCompact (s : S
et α)
参数：s : Opens α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCompact_iff_finite_subcover`：isCompact_iff_finite_subcover : IsCompact
 s ↔ forall {ι : Type u} (U : ι -> Set X), (forall i, IsOpen (U i)) -> (s subset
eq ⋃ i, U i) -> exi…
· 使用定理 `CompleteLattice.isCompactElement_iff_exists_le_iSup_of_le_iSup`：isCompac
tElement_iff_exists_le_iSup_of_le_iSup.{u} {α : Type u} [CompleteLattice α] (k :
 α) : IsCompactElement k ↔ forall (ι : Type u) (s : …
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `TopologicalSpace.Opens.coe_finset_sup`：coe_finset_sup (f : ι -> Opens α)
 (s : Finset ι) : (↑(s.sup f) : Set α) = s.sup ((↑) ∘ f)
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `TopologicalSpace.Opens.coe_iSup`：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i
, s i : Opens α) : Set α) = ⋃ i, s i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem isCompactElement_iff (s : Opens α) :
    IsCompactElement s ↔ IsCompact (s : Set α) := by
  rw [isCompact_iff_finite_subcover, CompleteLattice.isCompactElement_iff_exists_le_iSup_of_le_iSup]
  refine ⟨?_, fun H ι U hU => ?_⟩
  · introv H hU hU'
    obtain ⟨t, ht⟩ := H ι (fun i => ⟨U i, hU i⟩) (by simpa)
    refine ⟨t, Set.Subset.trans ht ?_⟩
    rw [coe_finset_sup, Finset.sup_eq_iSup]
    rfl
  · obtain ⟨t, ht⟩ :=
      H (fun i => U i) (fun i => (U i).isOpen) (by simpa using show (s : Set α) ⊆ ↑(iSup U) from hU)
    refine ⟨t, Set.Subset.trans ht ?_⟩
    simp only [Set.iUnion_subset_iff]
    change ∀ i ∈ t, U i ≤ t.sup U
    exact fun i => Finset.le_sup

/-- The preimage of an open set, as an open set. -/
/-
**TopologicalSpace.Opens.comap** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.Opens
`。
形式化陈述：comap (f : C(α, β)) : FrameHom (Opens β) (Opens α) where toFun s
参数：f : C(α, β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of an open set, as an open set.
-/
def comap (f : C(α, β)) : FrameHom (Opens β) (Opens α) where
  toFun s := ⟨f ⁻¹' s, s.2.preimage f.continuous⟩
  map_sSup' s := ext <| by simp only [coe_sSup, preimage_iUnion, biUnion_image, coe_mk]
  map_inf' _ _ := rfl
  map_top' := rfl

@[simp]
/-
**TopologicalSpace.Opens.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Op
ens`。
形式化陈述：comap_id : comap (ContinuousMap.id α) = FrameHom.id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FrameHom.ext`：ext {f g : FrameHom α β} (h : forall a, f a = g a) : f = g
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
-/
theorem comap_id : comap (ContinuousMap.id α) = FrameHom.id _ :=
  FrameHom.ext fun _ => ext rfl

@[gcongr]
/-
**TopologicalSpace.Opens.comap_mono** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
Opens`。
形式化陈述：comap_mono (f : C(α, β)) {s t : Opens β} (h : s <= t) : comap f s <= comap
 f t
参数：f : C(α, β)；h : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHomClass.mono`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomClass F
 α β] (f…
· 使用定理 `BoundedOrderHomClass.toRelHomClass`：∀ {F : Type u_6} {α : Type u_7} {β :
 Type u_8} {inst : LE α} {inst_1 : LE β} {inst_2 : BoundedOrder α}   {inst_3 : B
oundedOrder β} {inst_4 :…
· 使用定理 `BoundedLatticeHomClass.toBoundedOrderHomClass`：∀ {F : Type u_1} {α : Typ
e u_2} {β : Type u_3} [inst : FunLike F α β] [inst_1 : Lattice α] [inst_2 : Latt
ice β]   [inst_3 : BoundedOrder α] …
· 使用定理 `FrameHomClass.toBoundedLatticeHomClass`：∀ {F : Type u_1} {α : Type u_2} 
{β : Type u_3} [inst : FunLike F α β] [inst_1 : CompleteLattice α]   [inst_2 : C
ompleteLattice β] [FrameHomC…
· 使用定理 `FrameHom.instFrameHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : Comp
leteLattice α] [inst_1 : CompleteLattice β],   FrameHomClass (FrameHom α β) α β
-/
theorem comap_mono (f : C(α, β)) {s t : Opens β} (h : s ≤ t) : comap f s ≤ comap f t :=
  OrderHomClass.mono (comap f) h

@[simp]
/-
**TopologicalSpace.Opens.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.O
pens`。
形式化陈述：coe_comap (f : C(α, β)) (U : Opens β) : ↑(comap f U) = f ⁻¹' U
参数：f : C(α, β)；U : Opens β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comap (f : C(α, β)) (U : Opens β) : ↑(comap f U) = f ⁻¹' U :=
  rfl

@[simp]
/-
**TopologicalSpace.Opens.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.O
pens`。
形式化陈述：mem_comap {f : C(α, β)} {U : Opens β} {x : α} : x in comap f U ↔ f x in U
参数：α, β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap {f : C(α, β)} {U : Opens β} {x : α} : x ∈ comap f U ↔ f x ∈ U := .rfl
/-
**TopologicalSpace.Opens.comap_comp** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.
Opens`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : TopologicalSpace α]
 [inst_1 : TopologicalSpace β]   [inst_2 : TopologicalSpace γ] (g : C(β, γ)) (f 
: C(α, β)),   TopologicalSpace.Opens.comap (g.comp f) = (TopologicalSpace.Opens.
comap f).comp (TopologicalSpace.Opens.comap g)
参数：g : C(β, γ)；f : C(α, β)；g.comp f；TopologicalSpace.Opens.comap f；TopologicalSp
ace.Opens.comap g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem comap_comp (g : C(β, γ)) (f : C(α, β)) :
    comap (g.comp f) = (comap f).comp (comap g) :=
  rfl
/-
**TopologicalSpace.Opens.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace
.Opens`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : TopologicalSpace α]
 [inst_1 : TopologicalSpace β]   [inst_2 : TopologicalSpace γ] (g : C(β, γ)) (f 
: C(α, β)) (U : TopologicalSpace.Opens γ),   (TopologicalSpace.Opens.comap f) ((
TopologicalSpace.Opens.comap g) U) = (TopologicalSpace.Opens.comap (g.comp f)) U
参数：g : C(β, γ)；f : C(α, β)；U : TopologicalSpace.Opens γ；TopologicalSpace.Opens.c
omap f；(TopologicalSpace.Opens.comap g) U；TopologicalSpace.Opens.comap (g.comp f
)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem comap_comap (g : C(β, γ)) (f : C(α, β)) (U : Opens γ) :
    comap f (comap g U) = comap (g.comp f) U :=
  rfl
/-
**TopologicalSpace.Opens.comap_injective** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalS
pace.Opens`。
形式化陈述：comap_injective [T0Space β] : Injective (comap : C(α, β) -> FrameHom (Open
s β) (Opens α))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `Inseparable.eq`：Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x 
y) : x = y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inseparable_iff_forall_isOpen`：inseparable_iff_forall_isOpen : (x ~ᵢ y) 
↔ forall s : Set X, IsOpen s -> (x in s ↔ y in s)
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `TopologicalSpace.Opens.coe_inj`：coe_inj {U V : Opens α} : (U : Set α) = 
V ↔ U = V
-/
theorem comap_injective [T0Space β] : Injective (comap : C(α, β) → FrameHom (Opens β) (Opens α)) :=
  fun f g h =>
  ContinuousMap.ext fun a =>
    Inseparable.eq <|
      inseparable_iff_forall_isOpen.2 fun s hs =>
        have : comap f ⟨s, hs⟩ = comap g ⟨s, hs⟩ := DFunLike.congr_fun h ⟨_, hs⟩
        show a ∈ f ⁻¹' s ↔ a ∈ g ⁻¹' s from Set.ext_iff.1 (coe_inj.2 this) a

/-- A homeomorphism induces an order-preserving equivalence on open sets, by taking comaps. -/
@[simps -fullyApplied apply]
/-
**TopologicalSpace.Opens._root_.Homeomorph.opensCongr** 是 Mathlib 中的一个定义，位于命名空间 
`TopologicalSpace.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homeomorphism induces an order-preserving equivalence on open sets, by taking 
comaps.
-/
def _root_.Homeomorph.opensCongr (f : α ≃ₜ β) : Opens α ≃o Opens β where
  toFun := Opens.comap (f.symm : C(β, α))
  invFun := Opens.comap (f : C(α, β))
  left_inv _ := ext <| f.toEquiv.preimage_symm_preimage _
  right_inv _ := ext <| f.toEquiv.symm_preimage_preimage _
  map_rel_iff' := by
    simp only [← SetLike.coe_subset_coe]; exact f.symm.surjective.preimage_subset_preimage_iff

@[simp]
/-
**TopologicalSpace.Opens._root_.Homeomorph.opensCongr_symm** 是 Mathlib 中的一个定理，位于
命名空间 `TopologicalSpace.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Homeomorph.opensCongr_symm (f : α ≃ₜ β) : f.opensCongr.symm = f.symm.opensCongr :=
  rfl
/-
**TopologicalSpace.Opens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite α] : Finite (Opens α) :=
  Finite.of_injective _ SetLike.coe_injective

end Opens

/-- The open neighborhoods of a point. See also `Opens` or `nhds`. -/
/-
**TopologicalSpace.OpenNhdsOf** 是 Mathlib 中的一个归纳类型，位于命名空间 `TopologicalSpace`。
形式化陈述：{α : Type u_2} → [TopologicalSpace α] → α → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The open neighborhoods of a point. See also `Opens` or `nhds`.
-/
structure OpenNhdsOf (x : α) extends Opens α where
  /-- The point `x` belongs to every `U : TopologicalSpace.OpenNhdsOf x`. -/
  mem' : x ∈ carrier

namespace OpenNhdsOf

variable {x : α}

/-
**TopologicalSpace.OpenNhdsOf.toOpens_injective** 是 Mathlib 中的一个定理，位于命名空间 `Topol
ogicalSpace.OpenNhdsOf`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] {x : α}, Function.Injective T
opologicalSpace.OpenNhdsOf.toOpens
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOpens_injective : Injective (toOpens : OpenNhdsOf x → Opens α)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
/-
**TopologicalSpace.OpenNhdsOf.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.OpenN
hdsOf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (OpenNhdsOf x) α where
  coe U := U.1
  coe_injective := SetLike.coe_injective.comp toOpens_injective
/-
**TopologicalSpace.OpenNhdsOf.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.OpenN
hdsOf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (OpenNhdsOf x) := fast_instance% .ofSetLike (OpenNhdsOf x) α
/-
**TopologicalSpace.OpenNhdsOf.canLiftSet** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalS
pace.OpenNhdsOf`。
形式化陈述：canLiftSet : CanLift (Set α) (OpenNhdsOf x) (↑) fun s => IsOpen s ∧ x in s
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance canLiftSet : CanLift (Set α) (OpenNhdsOf x) (↑) fun s => IsOpen s ∧ x ∈ s :=
  ⟨fun s hs => ⟨⟨⟨s, hs.1⟩, hs.2⟩, rfl⟩⟩
/-
**TopologicalSpace.OpenNhdsOf.mem** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace.Op
enNhdsOf`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] {x : α} (U : TopologicalSpace
.OpenNhdsOf x), x ∈ U
参数：U : TopologicalSpace.OpenNhdsOf x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.OpenNhdsOf.mem'`：∀ {α : Type u_2} [inst : TopologicalSp
ace α] {x : α} (self : TopologicalSpace.OpenNhdsOf x), x ∈ self.carrier
-/
protected theorem mem (U : OpenNhdsOf x) : x ∈ U :=
  U.mem'
/-
**TopologicalSpace.OpenNhdsOf.isOpen** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalSpace
.OpenNhdsOf`。
形式化陈述：∀ {α : Type u_2} [inst : TopologicalSpace α] {x : α} (U : TopologicalSpace
.OpenNhdsOf x), IsOpen ↑U
参数：U : TopologicalSpace.OpenNhdsOf x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
-/
protected theorem isOpen (U : OpenNhdsOf x) : IsOpen (U : Set α) :=
  U.is_open'
/-
**TopologicalSpace.OpenNhdsOf.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.OpenN
hdsOf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTop (OpenNhdsOf x) where
  top := ⟨⊤, Set.mem_univ _⟩
  le_top _ := subset_univ _
/-
**TopologicalSpace.OpenNhdsOf.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.OpenN
hdsOf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (OpenNhdsOf x) := ⟨⊤⟩
/-
**TopologicalSpace.OpenNhdsOf.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.OpenN
hdsOf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (OpenNhdsOf x) := ⟨fun U V => ⟨U.1 ⊓ V.1, U.2, V.2⟩⟩
/-
**TopologicalSpace.OpenNhdsOf.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.OpenN
hdsOf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (OpenNhdsOf x) := ⟨fun U V => ⟨U.1 ⊔ V.1, Or.inl U.2⟩⟩
/-
**TopologicalSpace.OpenNhdsOf.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.OpenN
hdsOf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton α] : Unique (OpenNhdsOf x) where
  uniq U := SetLike.ext' <| Subsingleton.eq_univ_of_nonempty ⟨x, U.mem⟩
/-
**TopologicalSpace.OpenNhdsOf.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.OpenN
hdsOf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DistribLattice (OpenNhdsOf x) := fast_instance%
  toOpens_injective.distribLattice _ .rfl .rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl
/-
**TopologicalSpace.OpenNhdsOf.basis_nhds** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalS
pace.OpenNhdsOf`。
形式化陈述：basis_nhds : (𝓝 x).HasBasis (fun _ : OpenNhdsOf x => True) (↑)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `trivial`：True
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `TopologicalSpace.OpenNhdsOf.mem`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] {x : α} (U : TopologicalSpace.OpenNhdsOf x), x ∈ U
· 使用定理 `TopologicalSpace.OpenNhdsOf.isOpen`：∀ {α : Type u_2} [inst : Topological
Space α] {x : α} (U : TopologicalSpace.OpenNhdsOf x), IsOpen ↑U
-/
theorem basis_nhds : (𝓝 x).HasBasis (fun _ : OpenNhdsOf x => True) (↑) :=
  (nhds_basis_opens x).to_hasBasis (fun U hU => ⟨⟨⟨U, hU.2⟩, hU.1⟩, trivial, Subset.rfl⟩) fun U _ =>
    ⟨U, ⟨⟨U.mem, U.isOpen⟩, Subset.rfl⟩⟩

/-- Preimage of an open neighborhood of `f x` under a continuous map `f` as a `LatticeHom`. -/
/-
**TopologicalSpace.OpenNhdsOf.comap** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSpace.
OpenNhdsOf`。
形式化陈述：comap (f : C(α, β)) (x : α) : LatticeHom (OpenNhdsOf (f x)) (OpenNhdsOf x)
 where toFun U
参数：f : C(α, β)；x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Preimage of an open neighborhood of `f x` under a continuous map `f` as a `Latti
ceHom`.
-/
def comap (f : C(α, β)) (x : α) : LatticeHom (OpenNhdsOf (f x)) (OpenNhdsOf x) where
  toFun U := ⟨Opens.comap f U.1, U.mem⟩
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

end OpenNhdsOf

end TopologicalSpace

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: once we port `auto_cases`, port this
-- namespace Tactic

-- namespace AutoCases

-- /-- Find an `auto_cases_tac` which matches `TopologicalSpace.Opens`. -/
-- unsafe def opens_find_tac : expr → Option auto_cases_tac
--   | q(TopologicalSpace.Opens _) => tac_cases
--   | _ => none

-- end AutoCases

-- /-- A version of `tactic.auto_cases` that works for `TopologicalSpace.Opens`. -/
-- @[hint_tactic]
-- unsafe def auto_cases_opens : tactic String :=
--   auto_cases tactic.auto_cases.opens_find_tac

-- end Tactic

