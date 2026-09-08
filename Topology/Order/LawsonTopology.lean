/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Topology.Order.LowerUpperTopology
public import Mathlib.Topology.Order.ScottTopology

/-!
# Lawson topology

This file introduces the Lawson topology on a preorder.

## Main definitions

- `Topology.lawson` - the Lawson topology is defined as the meet of the lower topology and the
  Scott topology.
- `Topology.IsLawson.lawsonBasis` - The complements of the upper closures of finite sets
  intersected with Scott open sets.

## Main statements

- `Topology.IsLawson.isTopologicalBasis` - `Topology.IsLawson.lawsonBasis` is a basis for
  `Topology.IsLawson`
- `Topology.lawsonOpen_iff_scottOpen_of_isUpperSet'` - An upper set is Lawson open if and only if it
  is Scott open
- `Topology.lawsonClosed_iff_dirSupClosed_of_isLowerSet` - A lower set is Lawson closed if and only
  if it is closed under sups of directed sets
- `Topology.IsLawson.t0Space` - The Lawson topology is T₀

## Implementation notes

A type synonym `Topology.WithLawson` is introduced and for a preorder `α`, `Topology.WithLawson α`
is made an instance of `TopologicalSpace` by `Topology.lawson`.

We define a mixin class `Topology.IsLawson` for the class of types which are both a preorder and a
topology and where the topology is `Topology.lawson`.
It is shown that `Topology.WithLawson α` is an instance of `Topology.IsLawson`.

## References

* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]

## Tags

Lawson topology, preorder
-/

@[expose] public section

open Set TopologicalSpace

variable {α : Type*}

namespace Topology

/-! ### Lawson topology -/

section Lawson
section Preorder

/--
The Lawson topology is defined as the meet of `Topology.lower` and the `Topology.scott`.
-/
@[instance_reducible]
/-
**Topology.lawson** 是 Mathlib 中的一个定义，位于命名空间 `Topology`。
形式化陈述：lawson (α : Type*) [Preorder α] : TopologicalSpace α
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Lawson topology is defined as the meet of `Topology.lower` and the `Topology
.scott`.
-/
def lawson (α : Type*) [Preorder α] : TopologicalSpace α := lower α ⊓ scott α univ

variable (α) [Preorder α] [TopologicalSpace α]

/-- Predicate for an ordered topological space to be equipped with its Lawson topology.

The Lawson topology is defined as the meet of `Topology.lower` and the `Topology.scott`.
-/
/-
**Topology.IsLawson** 是 Mathlib 中的一个归纳类型，位于命名空间 `Topology`。
形式化陈述：(α : Type u_1) → [Preorder α] → [TopologicalSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate for an ordered topological space to be equipped with its Lawson topolo
gy.

The Lawson topology is defined as the meet of `Topology.lower` and the `Topology
.scott`.
-/
class IsLawson : Prop where
  topology_eq_lawson : ‹TopologicalSpace α› = lawson α

end Preorder

namespace IsLawson
section Preorder
variable (α) [Preorder α] [TopologicalSpace α] [IsLawson α]

/-- The complements of the upper closures of finite sets intersected with Scott open sets form
a basis for the lawson topology. -/
/-
**Topology.IsLawson.lawsonBasis** 是 Mathlib 中的一个定义，位于命名空间 `Topology.IsLawson`。
形式化陈述：lawsonBasis
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complements of the upper closures of finite sets intersected with Scott open
 sets form
a basis for the lawson topology.
-/
def lawsonBasis := { s : Set α | ∃ t : Set α, t.Finite ∧ ∃ u : Set α, IsOpen[scott α univ] u ∧
      u \ upperClosure t = s }
/-
**Topology.IsLawson.isTopologicalBasis** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsLaw
son`。
形式化陈述：∀ (α : Type u_1) [inst : Preorder α] [inst_1 : TopologicalSpace α] [Topolo
gy.IsLawson α],   TopologicalSpace.IsTopologicalBasis (Topology.IsLawson.lawsonB
asis α)
参数：α : Type u_1；Topology.IsLawson.lawsonBasis α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsLawson.lawsonBasis.eq_1`：∀ (α : Type u_1) [inst : Preorder α]
,   Topology.IsLawson.lawsonBasis α = {s | ∃ t, t.Finite ∧ ∃ u, IsOpen u ∧ u \ ↑
(upperClosure t) = s}
· 使用定理 `Set.image2.eq_1`：∀ {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ
) (s : Set α) (t : Set β),   Set.image2 f s t = {c | ∃ a ∈ s, ∃ b ∈ t, f a b = c
}
· 使用定理 `Topology.IsLower.lowerBasis.eq_1`：∀ (α : Type u_3) [inst : Preorder α], 
Topology.IsLower.lowerBasis α = {s | ∃ t, t.Finite ∧ (↑(upperClosure t))ᶜ = s}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.sdiff_eq_compl_inter`：sdiff_eq_compl_inter {s t : Set α} : s \ t = t
ᶜ inter s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsLawson.topology_eq_lawson`：∀ {α : Type u_1} {inst : Preorder 
α} {inst_1 : TopologicalSpace α} [self : Topology.IsLawson α],   inst_1 = Topolo
gy.lawson α
· 使用定理 `Topology.lawson.eq_1`：∀ (α : Type u_2) [inst : Preorder α], Topology.law
son α = Topology.lower α ⊓ Topology.scott α Set.univ
· 使用定理 `congrArg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → γ
) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…
· 使用引理 `Homeomorph.isInducing`：isInducing (h : X ≃ₜ Y) : IsInducing h
· 使用定理 `TopologicalSpace.IsTopologicalBasis.inf_induced`：∀ {α : Type u} {β : Typ
e u_1} [t : TopologicalSpace α] {γ : Type u_2} [s : TopologicalSpace β] {B₁ : Se
t (Set α)}   {B₂ : Set (Set β)},   To…
· 使用定理 `Topology.IsLower.isTopologicalBasis`：∀ {α : Type u_1} [inst : Preorder α
] [inst_1 : TopologicalSpace α] [Topology.IsLower α],   TopologicalSpace.IsTopol
ogicalBasis (Topology.IsL…
· 使用定理 `Topology.instIsLowerWithLower`：∀ {α : Type u_1} [inst : Preorder α], Top
ology.IsLower (Topology.WithLower α)
· 使用定理 `TopologicalSpace.isTopologicalBasis_opens`：isTopologicalBasis_opens : Is
TopologicalBasis { U : Set α | IsOpen U }
-/
protected theorem isTopologicalBasis : TopologicalSpace.IsTopologicalBasis (lawsonBasis α) := by
  have lawsonBasis_image2 : lawsonBasis α =
      (image2 (fun x x_1 ↦ ⇑WithLower.toLower ⁻¹' x ∩ ⇑WithScott.toScott ⁻¹' x_1)
        (IsLower.lowerBasis (WithLower α)) {U | IsOpen[scott α univ] U}) := by
    rw [lawsonBasis, image2, IsLower.lowerBasis]
    simp_rw [sdiff_eq_compl_inter]
    aesop
  rw [lawsonBasis_image2]
  convert!
    IsTopologicalBasis.inf_induced IsLower.isTopologicalBasis
      (isTopologicalBasis_opens (α := WithScott α)) WithLower.toLower WithScott.toScott
  rw [@topology_eq_lawson α _ _ _, lawson]
  apply (congrArg₂ min _) _
  · let _ := lower α
    exact (@IsLower.withLowerHomeomorph α ‹_› (lower α) ⟨rfl⟩).isInducing.eq_induced
  · let _ := scott α univ
    exact (@IsScott.withScottHomeomorph α _ (scott α univ) ⟨rfl⟩).isInducing.eq_induced

end Preorder
end IsLawson

/--
Type synonym for a preorder equipped with the Lawson topology.
-/
/-
**Topology.WithLawson** 是 Mathlib 中的一个定义，位于命名空间 `Topology`。
形式化陈述：WithLawson (α : Type*)
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type synonym for a preorder equipped with the Lawson topology.
-/
def WithLawson (α : Type*) := α

namespace WithLawson

/-- `toLawson` is the identity function to the `WithLawson` of a type. -/
/-
**Topology.WithLawson.toLawson** 是 Mathlib 中的一个定义，位于命名空间 `Topology.WithLawson`。
形式化陈述：{α : Type u_1} → α ≃ Topology.WithLawson α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`toLawson` is the identity function to the `WithLawson` of a type.
-/
@[match_pattern] def toLawson : α ≃ WithLawson α := Equiv.refl _

/-- `ofLawson` is the identity function from the `WithLawson` of a type. -/
/-
**Topology.WithLawson.ofLawson** 是 Mathlib 中的一个定义，位于命名空间 `Topology.WithLawson`。
形式化陈述：{α : Type u_1} → Topology.WithLawson α ≃ α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`ofLawson` is the identity function from the `WithLawson` of a type.
-/
@[match_pattern] def ofLawson : WithLawson α ≃ α := Equiv.refl _
/-
**Topology.WithLawson.to_Lawson_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Topology.With
Lawson`。
形式化陈述：∀ {α : Type u_1}, Topology.WithLawson.toLawson.symm = Topology.WithLawson.
ofLawson
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`ofLawson` is the identity function from the `WithLawson` of a type.
-/
@[simp] lemma to_Lawson_symm_eq : (@toLawson α).symm = ofLawson := rfl
/-
**Topology.WithLawson.of_Lawson_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Topology.With
Lawson`。
形式化陈述：∀ {α : Type u_1}, Topology.WithLawson.ofLawson.symm = Topology.WithLawson.
toLawson
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`ofLawson` is the identity function from the `WithLawson` of a type.
-/
@[simp] lemma of_Lawson_symm_eq : (@ofLawson α).symm = toLawson := rfl
/-
**Topology.WithLawson.toLawson_ofLawson** 是 Mathlib 中的一个定理，位于命名空间 `Topology.With
Lawson`。
形式化陈述：∀ {α : Type u_1} (a : Topology.WithLawson α), Topology.WithLawson.toLawson
 (Topology.WithLawson.ofLawson a) = a
参数：a : Topology.WithLawson α；Topology.WithLawson.ofLawson a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofLawson` is the identity function from the `WithLawson` of a type.
-/
@[simp] lemma toLawson_ofLawson (a : WithLawson α) : toLawson (ofLawson a) = a := rfl
/-
**Topology.WithLawson.ofLawson_toLawson** 是 Mathlib 中的一个定理，位于命名空间 `Topology.With
Lawson`。
形式化陈述：∀ {α : Type u_1} (a : α), Topology.WithLawson.ofLawson (Topology.WithLawso
n.toLawson a) = a
参数：a : α；Topology.WithLawson.toLawson a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofLawson` is the identity function from the `WithLawson` of a type.
-/
@[simp] lemma ofLawson_toLawson (a : α) : ofLawson (toLawson a) = a := rfl
/-
**Topology.WithLawson.toLawson_inj** 是 Mathlib 中的一个引理，位于命名空间 `Topology.WithLawso
n`。
形式化陈述：toLawson_inj {a b : α} : toLawson a = toLawson b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`ofLawson` is the identity function from the `WithLawson` of a type.
-/
lemma toLawson_inj {a b : α} : toLawson a = toLawson b ↔ a = b := Iff.rfl
/-
**Topology.WithLawson.ofLawson_inj** 是 Mathlib 中的一个引理，位于命名空间 `Topology.WithLawso
n`。
形式化陈述：ofLawson_inj {a b : WithLawson α} : ofLawson a = ofLawson b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ofLawson_inj {a b : WithLawson α} : ofLawson a = ofLawson b ↔ a = b := Iff.rfl

/-- A recursor for `WithLawson`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/-
**Topology.WithLawson.rec** 是 Mathlib 中的一个定义，位于命名空间 `Topology.WithLawson`。
形式化陈述：{α : Type u_1} →   {β : Topology.WithLawson α → Sort u_2} →     ((a : α) →
 β (Topology.WithLawson.toLawson a)) → (a : Topology.WithLawson α) → β a
参数：(a : α) → β (Topology.WithLawson.toLawson a)；a : Topology.WithLawson α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursor for `WithLawson`. Use as `induction x`.
-/
protected def rec {β : WithLawson α → Sort*}
    (h : ∀ a, β (toLawson a)) : ∀ a, β a := fun a => h (ofLawson a)
/-
**Topology.WithLawson.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.WithLawson`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] : Nonempty (WithLawson α) := ‹Nonempty α›
/-
**Topology.WithLawson.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.WithLawson`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (WithLawson α) := ‹Inhabited α›

variable [Preorder α]
/-
**Topology.WithLawson.instPreorder** 是 Mathlib 中的一个实例，位于命名空间 `Topology.WithLawso
n`。
形式化陈述：instPreorder : Preorder (WithLawson α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPreorder : Preorder (WithLawson α) := ‹Preorder α›
/-
**Topology.WithLawson.instTopologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `Topology.W
ithLawson`。
形式化陈述：instTopologicalSpace : TopologicalSpace (WithLawson α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTopologicalSpace : TopologicalSpace (WithLawson α) :=
  -- fast_instance% lawson α fails
  letI : TopologicalSpace α := lawson α
  inferInstanceAs <| TopologicalSpace α
/-
**Topology.WithLawson.instIsLawson** 是 Mathlib 中的一个实例，位于命名空间 `Topology.WithLawso
n`。
形式化陈述：instIsLawson : IsLawson (WithLawson α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsLawson : IsLawson (WithLawson α) := ⟨rfl⟩

/-- If `α` is equipped with the Lawson topology, then it is homeomorphic to `WithLawson α`.
-/
/-
**Topology.WithLawson.homeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Topology.WithLawson`
。
形式化陈述：homeomorph [TopologicalSpace α] [IsLawson α] : WithLawson α ≃ₜ α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is equipped with the Lawson topology, then it is homeomorphic to `WithLaw
son α`.
-/
def homeomorph [TopologicalSpace α] [IsLawson α] : WithLawson α ≃ₜ α :=
  ofLawson.toHomeomorphOfIsInducing ⟨IsLawson.topology_eq_lawson (α := α) ▸ induced_id.symm⟩
/-
**Topology.WithLawson.isOpen_preimage_ofLawson** 是 Mathlib 中的一个定理，位于命名空间 `Topolo
gy.WithLawson`。
形式化陈述：isOpen_preimage_ofLawson {S : Set α} : IsOpen (ofLawson ⁻¹' S) ↔ (lawson α
).IsOpen S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOpen_preimage_ofLawson {S : Set α} :
    IsOpen (ofLawson ⁻¹' S) ↔ (lawson α).IsOpen S := Iff.rfl
/-
**Topology.WithLawson.isClosed_preimage_ofLawson** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logy.WithLawson`。
形式化陈述：isClosed_preimage_ofLawson {S : Set α} : IsClosed (ofLawson ⁻¹' S) ↔ IsClo
sed[lawson α] S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isClosed_preimage_ofLawson {S : Set α} :
    IsClosed (ofLawson ⁻¹' S) ↔ IsClosed[lawson α] S := Iff.rfl
/-
**Topology.WithLawson.isOpen_def** 是 Mathlib 中的一个定理，位于命名空间 `Topology.WithLawson`
。
形式化陈述：isOpen_def {T : Set (WithLawson α)} : IsOpen T ↔ (lawson α).IsOpen (toLaws
on ⁻¹' T)
参数：WithLawson α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOpen_def {T : Set (WithLawson α)} :
    IsOpen T ↔ (lawson α).IsOpen (toLawson ⁻¹' T) := Iff.rfl

end WithLawson
end Lawson

section Preorder

variable [Preorder α]

/-
**Topology.lawson_le_scott** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
形式化陈述：lawson_le_scott : lawson α <= scott α univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
lemma lawson_le_scott : lawson α ≤ scott α univ := inf_le_right
/-
**Topology.lawson_le_lower** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
形式化陈述：lawson_le_lower : lawson α <= lower α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
lemma lawson_le_lower : lawson α ≤ lower α := inf_le_left
/-
**Topology.scottHausdorff_le_lawson** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
形式化陈述：scottHausdorff_le_lawson : scottHausdorff α univ <= lawson α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用引理 `Topology.scottHausdorff_le_lower`：scottHausdorff_le_lower : scottHausdor
ff α univ <= lower α
· 使用引理 `Topology.scottHausdorff_le_scott`：scottHausdorff_le_scott [Preorder α] :
 scottHausdorff α univ <= scott α univ
-/
lemma scottHausdorff_le_lawson : scottHausdorff α univ ≤ lawson α :=
  le_inf scottHausdorff_le_lower scottHausdorff_le_scott
/-
**Topology.lawsonClosed_of_scottClosed** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
形式化陈述：lawsonClosed_of_scottClosed (s : Set α) (h : IsClosed (WithScott.ofScott ⁻
¹' s)) : IsClosed (WithLawson.ofLawson ⁻¹' s)
参数：s : Set α；h : IsClosed (WithScott.ofScott ⁻¹' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.mono`：IsClosed.mono (hs : IsClosed[t₂] s) (h : t₁ <= t₂) : IsCl
osed[t₁] s
· 使用引理 `Topology.lawson_le_scott`：lawson_le_scott : lawson α <= scott α univ
-/
lemma lawsonClosed_of_scottClosed (s : Set α) (h : IsClosed (WithScott.ofScott ⁻¹' s)) :
    IsClosed (WithLawson.ofLawson ⁻¹' s) := h.mono lawson_le_scott
/-
**Topology.lawsonClosed_of_lowerClosed** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
形式化陈述：lawsonClosed_of_lowerClosed (s : Set α) (h : IsClosed (WithLower.ofLower ⁻
¹' s)) : IsClosed (WithLawson.ofLawson ⁻¹' s)
参数：s : Set α；h : IsClosed (WithLower.ofLower ⁻¹' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.mono`：IsClosed.mono (hs : IsClosed[t₂] s) (h : t₁ <= t₂) : IsCl
osed[t₁] s
· 使用引理 `Topology.lawson_le_lower`：lawson_le_lower : lawson α <= lower α
-/
lemma lawsonClosed_of_lowerClosed (s : Set α) (h : IsClosed (WithLower.ofLower ⁻¹' s)) :
    IsClosed (WithLawson.ofLawson ⁻¹' s) := h.mono lawson_le_lower

/-- An upper set is Lawson open if and only if it is Scott open -/
/-
**Topology.lawsonOpen_iff_scottOpen_of_isUpperSet** 是 Mathlib 中的一个引理，位于命名空间 `Top
ology`。
形式化陈述：lawsonOpen_iff_scottOpen_of_isUpperSet {s : Set α} (h : IsUpperSet s) : Is
Open (WithLawson.ofLawson ⁻¹' s) ↔ IsOpen (WithScott.ofScott ⁻¹' s)
参数：h : IsUpperSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Topology.IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open`：isOpen_i
ff_isUpperSet_and_scottHausdorff_open [IsScott α D] : IsOpen s ↔ IsUpperSet s ∧ 
IsOpen[scottHausdorff α D] s
· 使用定理 `Topology.WithScott.instIsScottUnivSet`：∀ {α : Type u_1} [inst : Preorder
 α], Topology.IsScott (Topology.WithScott α) Set.univ
· 使用引理 `Topology.scottHausdorff_le_lawson`：scottHausdorff_le_lawson : scottHausd
orff α univ <= lawson α
· 使用引理 `Topology.lawson_le_scott`：lawson_le_scott : lawson α <= scott α univ

--- 原说明 ---
An upper set is Lawson open if and only if it is Scott open
-/
lemma lawsonOpen_iff_scottOpen_of_isUpperSet {s : Set α} (h : IsUpperSet s) :
    IsOpen (WithLawson.ofLawson ⁻¹' s) ↔ IsOpen (WithScott.ofScott ⁻¹' s) :=
  ⟨fun hs => IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open (D := univ).mpr
    ⟨h, (scottHausdorff_le_lawson s) hs⟩, lawson_le_scott _⟩

variable (L : TopologicalSpace α) (S : TopologicalSpace α)
variable [@IsLawson α _ L] [@IsScott α univ _ S]
/-
**Topology.isLawson_le_isScott** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
形式化陈述：isLawson_le_isScott : L <= S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsScott.topology_eq`：topology_eq [IsScott α D] : ‹_› = scott α 
D
· 使用定理 `Topology.IsLawson.topology_eq_lawson`：∀ {α : Type u_1} {inst : Preorder 
α} {inst_1 : TopologicalSpace α} [self : Topology.IsLawson α],   inst_1 = Topolo
gy.lawson α
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
lemma isLawson_le_isScott : L ≤ S := by
  rw [@IsScott.topology_eq α univ _ S _, @IsLawson.topology_eq_lawson α _ L _]
  exact inf_le_right
/-
**Topology.scottHausdorff_le_isLawson** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
形式化陈述：scottHausdorff_le_isLawson : scottHausdorff α univ <= L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsLawson.topology_eq_lawson`：∀ {α : Type u_1} {inst : Preorder 
α} {inst_1 : TopologicalSpace α} [self : Topology.IsLawson α],   inst_1 = Topolo
gy.lawson α
· 使用引理 `Topology.scottHausdorff_le_lawson`：scottHausdorff_le_lawson : scottHausd
orff α univ <= lawson α
-/
lemma scottHausdorff_le_isLawson : scottHausdorff α univ ≤ L := by
  rw [@IsLawson.topology_eq_lawson α _ L _]
  exact scottHausdorff_le_lawson

/-- An upper set is Lawson open if and only if it is Scott open -/
/-
**Topology.lawsonOpen_iff_scottOpen_of_isUpperSet'** 是 Mathlib 中的一个引理，位于命名空间 `To
pology`。
形式化陈述：lawsonOpen_iff_scottOpen_of_isUpperSet' (s : Set α) (h : IsUpperSet s) : I
sOpen[L] s ↔ IsOpen[S] s
参数：s : Set α；h : IsUpperSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Topology.IsLawson.topology_eq_lawson`：∀ {α : Type u_1} {inst : Preorder 
α} {inst_1 : TopologicalSpace α} [self : Topology.IsLawson α],   inst_1 = Topolo
gy.lawson α
· 使用引理 `Topology.IsScott.topology_eq`：topology_eq [IsScott α D] : ‹_› = scott α 
D
· 使用引理 `Topology.lawsonOpen_iff_scottOpen_of_isUpperSet`：lawsonOpen_iff_scottOpe
n_of_isUpperSet {s : Set α} (h : IsUpperSet s) : IsOpen (WithLawson.ofLawson ⁻¹'
 s) ↔ IsOpen (WithScott.ofScott ⁻¹' s…

--- 原说明 ---
An upper set is Lawson open if and only if it is Scott open
-/
lemma lawsonOpen_iff_scottOpen_of_isUpperSet' (s : Set α) (h : IsUpperSet s) :
    IsOpen[L] s ↔ IsOpen[S] s := by
  rw [@IsLawson.topology_eq_lawson α _ L _, @IsScott.topology_eq α univ _ S _]
  exact lawsonOpen_iff_scottOpen_of_isUpperSet h
/-
**Topology.lawsonClosed_iff_scottClosed_of_isLowerSet** 是 Mathlib 中的一个引理，位于命名空间 
`Topology`。
形式化陈述：lawsonClosed_iff_scottClosed_of_isLowerSet (s : Set α) (h : IsLowerSet s) 
: IsClosed[L] s ↔ IsClosed[S] s
参数：s : Set α；h : IsLowerSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用引理 `Topology.lawsonOpen_iff_scottOpen_of_isUpperSet'`：lawsonOpen_iff_scottOp
en_of_isUpperSet' (s : Set α) (h : IsUpperSet s) : IsOpen[L] s ↔ IsOpen[S] s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUpperSet_compl`：isUpperSet_compl : IsUpperSet sᶜ ↔ IsLowerSet s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma lawsonClosed_iff_scottClosed_of_isLowerSet (s : Set α) (h : IsLowerSet s) :
    IsClosed[L] s ↔ IsClosed[S] s := by
  rw [← @isOpen_compl_iff, ← isOpen_compl_iff,
    (lawsonOpen_iff_scottOpen_of_isUpperSet' L S _ (isUpperSet_compl.mpr h))]

include S in
/-- A lower set is Lawson closed if and only if it is closed under sups of directed sets -/
/-
**Topology.lawsonClosed_iff_dirSupClosed_of_isLowerSet** 是 Mathlib 中的一个引理，位于命名空间
 `Topology`。
形式化陈述：lawsonClosed_iff_dirSupClosed_of_isLowerSet (s : Set α) (h : IsLowerSet s)
 : IsClosed[L] s ↔ DirSupClosed s
参数：s : Set α；h : IsLowerSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.lawsonClosed_iff_scottClosed_of_isLowerSet`：lawsonClosed_iff_sc
ottClosed_of_isLowerSet (s : Set α) (h : IsLowerSet s) : IsClosed[L] s ↔ IsClose
d[S] s
· 使用引理 `Topology.IsScott.isClosed_iff_isLowerSet_and_dirSupClosed`：isClosed_iff_
isLowerSet_and_dirSupClosed [IsScott α univ] : IsClosed s ↔ IsLowerSet s ∧ DirSu
pClosed s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A lower set is Lawson closed if and only if it is closed under sups of directed 
sets
-/
lemma lawsonClosed_iff_dirSupClosed_of_isLowerSet (s : Set α) (h : IsLowerSet s) :
    IsClosed[L] s ↔ DirSupClosed s := by
  rw [lawsonClosed_iff_scottClosed_of_isLowerSet L S _ h,
    @IsScott.isClosed_iff_isLowerSet_and_dirSupClosed]
  simp_all

end Preorder

namespace IsLawson
variable [PartialOrder α] [TopologicalSpace α] [IsLawson α]

set_option backward.isDefEq.respectTransparency false in
/-- The Lawson topology on a partial order is T₁. -/
-- see Note [lower instance priority]
/-
**Topology.IsLawson.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.IsLawson`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 90) toT1Space : T1Space α where
  t1 a := by
    simp +instances only [IsLawson.topology_eq_lawson]
    rw [← (Set.OrdConnected.upperClosure_inter_lowerClosure ordConnected_singleton),
      ← WithLawson.isClosed_preimage_ofLawson]
    apply IsClosed.inter
      (lawsonClosed_of_lowerClosed _ (IsLower.isClosed_upperClosure (finite_singleton a)))
    rw [lowerClosure_singleton, LowerSet.coe_Iic, ← WithLawson.isClosed_preimage_ofLawson]
    exact lawsonClosed_of_scottClosed _ isClosed_Iic

end IsLawson

end Topology

