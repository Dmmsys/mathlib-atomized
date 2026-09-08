/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Matteo Cipollina
-/
module

public import Mathlib.Combinatorics.Quiver.Subquiver
public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Combinatorics.Quiver.Symmetric

/-!
## Weakly and strongly connected components

For a quiver `V`, define the type `WeaklyConnectedComponent V` as the quotient of `V` by
the relation which identifies `a` with `b` if there is a path from `a` to `b` in `Symmetrify V`.
(These zigzags can be seen as a proof-relevant analogue of `EqvGen`.)

We define:
* `Quiver.IsStronglyConnected V`: every pair of vertices is connected by a (possibly empty) path.
* `Quiver.IsSStronglyConnected V`: every pair of vertices is connected by a path of positive length.
* `Quiver.StronglyConnectedComponent V`: the quotient by the equivalence relation “paths in both
  directions”.

These concepts relate strong and weak connectivity and let us reason about strongly connected
components in directed graphs.
-/

@[expose] public section

universe v u

namespace Quiver

variable (V : Type*) [Quiver.{u} V]

/-- Two vertices are related in the zigzag setoid if there is a
zigzag of arrows from one to the other. -/
@[instance_reducible]
/-
**Quiver.zigzagSetoid** 是 Mathlib 中的一个定义，位于命名空间 `Quiver`。
形式化陈述：zigzagSetoid : Setoid V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two vertices are related in the zigzag setoid if there is a
zigzag of arrows from one to the other.
-/
def zigzagSetoid : Setoid V :=
  ⟨fun a b ↦ Nonempty (@Path (Symmetrify V) _ a b), fun _ ↦ ⟨Path.nil⟩, fun ⟨p⟩ ↦
    ⟨p.reverse⟩, fun ⟨p⟩ ⟨q⟩ ↦ ⟨p.comp q⟩⟩

/-- The type of weakly connected components of a directed graph. Two vertices are
in the same weakly connected component if there is a zigzag of arrows from one
to the other. -/
/-
**Quiver.WeaklyConnectedComponent** 是 Mathlib 中的一个定义，位于命名空间 `Quiver`。
形式化陈述：WeaklyConnectedComponent : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of weakly connected components of a directed graph. Two vertices are
in the same weakly connected component if there is a zigzag of arrows from one
to the other.
-/
def WeaklyConnectedComponent : Type _ :=
  Quotient (zigzagSetoid V)

namespace WeaklyConnectedComponent

variable {V}

/-- The weakly connected component corresponding to a vertex. -/
/-
**Quiver.WeaklyConnectedComponent.mk** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.WeaklyCon
nectedComponent`。
形式化陈述：{V : Type u_1} → [inst : Quiver V] → V → Quiver.WeaklyConnectedComponent V
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)

--- 原说明 ---
The weakly connected component corresponding to a vertex.
-/
protected def mk : V → WeaklyConnectedComponent V :=
  @Quotient.mk' _ (zigzagSetoid V)
/-
**Quiver.WeaklyConnectedComponent.** 是 Mathlib 中的一个实例，位于命名空间 `Quiver.WeaklyConne
ctedComponent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeTC V (WeaklyConnectedComponent V) :=
  ⟨WeaklyConnectedComponent.mk⟩
/-
**Quiver.WeaklyConnectedComponent.** 是 Mathlib 中的一个实例，位于命名空间 `Quiver.WeaklyConne
ctedComponent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited V] : Inhabited (WeaklyConnectedComponent V) :=
  ⟨show V from default⟩
/-
**Quiver.WeaklyConnectedComponent.eq** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.WeaklyCon
nectedComponent`。
形式化陈述：∀ {V : Type u_1} [inst : Quiver V] (a b : V),   Quiver.WeaklyConnectedComp
onent.mk a = Quiver.WeaklyConnectedComponent.mk b ↔ Nonempty (Quiver.Path a b)
参数：a b : V；Quiver.Path a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b
-/
protected theorem eq (a b : V) :
    (a : WeaklyConnectedComponent V) = b ↔ Nonempty (@Path (Symmetrify V) _ a b) :=
  Quotient.eq''

end WeaklyConnectedComponent

variable {V}

/-- A wide subquiver `H` of `Symmetrify V` determines a wide subquiver of `V`, containing an
arrow `e` if either `e` or its reversal is in `H`. -/
/-
**Quiver.wideSubquiverSymmetrify** 是 Mathlib 中的一个定义，位于命名空间 `Quiver`。
形式化陈述：wideSubquiverSymmetrify (H : WideSubquiver (Symmetrify V)) : WideSubquiver
 V
参数：H : WideSubquiver (Symmetrify V)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A wide subquiver `H` of `Symmetrify V` determines a wide subquiver of `V`, conta
ining an
arrow `e` if either `e` or its reversal is in `H`.
-/
def wideSubquiverSymmetrify (H : WideSubquiver (Symmetrify V)) : WideSubquiver V :=
  fun a b ↦ {e | .inl e ∈ H a b ∨ .inr e ∈ H b a}

/-!
## Strongly connected components (directed connectivity)

We define strong connectivity (`IsStronglyConnected`), its positive-length refinement
(`IsSStronglyConnected`), and strongly connected components.
-/

section StronglyConnected

variable (V : Type*) [Quiver V]

/-- Strong connectivity: every ordered pair of vertices is joined by a (possibly empty)
directed path. -/
/-
**Quiver.IsStronglyConnected** 是 Mathlib 中的一个定义，位于命名空间 `Quiver`。
形式化陈述：IsStronglyConnected : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Strong connectivity: every ordered pair of vertices is joined by a (possibly emp
ty)
directed path.
-/
def IsStronglyConnected : Prop :=
  ∀ i j : V, Nonempty (Path i j)

/-- Positive strong connectivity: every ordered pair of vertices is joined by a directed path
of positive length. -/
/-
**Quiver.IsSStronglyConnected** 是 Mathlib 中的一个定义，位于命名空间 `Quiver`。
形式化陈述：IsSStronglyConnected : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Positive strong connectivity: every ordered pair of vertices is joined by a dire
cted path
of positive length.
-/
def IsSStronglyConnected : Prop :=
  ∀ i j : V, ∃ p : Path i j, 0 < p.length
/-
**Quiver.isStronglyConnected_iff** 是 Mathlib 中的一个定理，位于命名空间 `Quiver`。
形式化陈述：∀ (V : Type u_2) [inst : Quiver V], Quiver.IsStronglyConnected V ↔ ∀ (i j 
: V), Nonempty (Quiver.Path i j)
参数：V : Type u_2；i j : V；Quiver.Path i j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma isStronglyConnected_iff :
    IsStronglyConnected V ↔ ∀ i j : V, Nonempty (Path i j) := Iff.rfl
/-
**Quiver.isSStronglyConnected_iff** 是 Mathlib 中的一个定理，位于命名空间 `Quiver`。
形式化陈述：∀ (V : Type u_2) [inst : Quiver V], Quiver.IsSStronglyConnected V ↔ ∀ (i j
 : V), ∃ p, 0 < p.length
参数：V : Type u_2；i j : V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma isSStronglyConnected_iff :
    IsSStronglyConnected V ↔ ∀ i j : V, ∃ p : Path i j, 0 < p.length := Iff.rfl
/-
**Quiver.IsStronglyConnected.nonempty_path** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.IsS
tronglyConnected`。
形式化陈述：∀ (V : Type u_2) [inst : Quiver V], Quiver.IsStronglyConnected V → ∀ (i j 
: V), Nonempty (Quiver.Path i j)
参数：V : Type u_2；i j : V；Quiver.Path i j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsStronglyConnected.nonempty_path
    (h : IsStronglyConnected V) (i j : V) : Nonempty (Path i j) := h i j
/-
**Quiver.IsSStronglyConnected.exists_pos_path** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.
IsSStronglyConnected`。
形式化陈述：∀ (V : Type u_2) [inst : Quiver V], Quiver.IsSStronglyConnected V → ∀ (i j
 : V), ∃ p, 0 < p.length
参数：V : Type u_2；i j : V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsSStronglyConnected.exists_pos_path
    (h : IsSStronglyConnected V) (i j : V) : ∃ p : Path i j, 0 < p.length := h i j
/-
**Quiver.IsSStronglyConnected.exists_pos_cycle** 是 Mathlib 中的一个定理，位于命名空间 `Quiver
.IsSStronglyConnected`。
形式化陈述：∀ (V : Type u_2) [inst : Quiver V], Quiver.IsSStronglyConnected V → ∀ (i :
 V), ∃ p, 0 < p.length
参数：V : Type u_2；i : V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsSStronglyConnected.exists_pos_cycle
    (h : IsSStronglyConnected V) (i : V) : ∃ p : Path i i, 0 < p.length := h i i
/-
**Quiver.IsSStronglyConnected.isStronglyConnected** 是 Mathlib 中的一个定理，位于命名空间 `Qui
ver.IsSStronglyConnected`。
形式化陈述：∀ (V : Type u_2) [inst : Quiver V], Quiver.IsSStronglyConnected V → Quiver
.IsStronglyConnected V
参数：V : Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsSStronglyConnected.isStronglyConnected
    (h : IsSStronglyConnected V) : IsStronglyConnected V := by
  intro i j; obtain ⟨p, _⟩ := h i j; exact ⟨p⟩

/-- Equivalence relation identifying vertices connected by directed paths in both directions. -/
@[instance_reducible]
/-
**Quiver.stronglyConnectedSetoid** 是 Mathlib 中的一个定义，位于命名空间 `Quiver`。
形式化陈述：stronglyConnectedSetoid : Setoid V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence relation identifying vertices connected by directed paths in both di
rections.
-/
def stronglyConnectedSetoid : Setoid V :=
  ⟨fun a b => (Nonempty (Path a b)) ∧ (Nonempty (Path b a)),
   fun _ => ⟨⟨Path.nil⟩, ⟨Path.nil⟩⟩, fun ⟨hab, hba⟩ => ⟨hba, hab⟩, fun ⟨hab, hba⟩ ⟨hbc, hcb⟩ =>
     ⟨⟨hab.some.comp hbc.some⟩, ⟨hcb.some.comp hba.some⟩⟩⟩

/-- The type of strongly connected components (bidirectional reachability classes). -/
/-
**Quiver.StronglyConnectedComponent** 是 Mathlib 中的一个定义，位于命名空间 `Quiver`。
形式化陈述：StronglyConnectedComponent : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of strongly connected components (bidirectional reachability classes).
-/
def StronglyConnectedComponent : Type _ :=
  Quotient (stronglyConnectedSetoid V)

namespace StronglyConnectedComponent

variable {V}

/-- The canonical map from a vertex to its strongly connected component. -/
/-
**Quiver.StronglyConnectedComponent.mk** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Strongl
yConnectedComponent`。
形式化陈述：{V : Type u_2} → [inst : Quiver V] → V → Quiver.StronglyConnectedComponent
 V
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)

--- 原说明 ---
The canonical map from a vertex to its strongly connected component.
-/
protected def mk : V → StronglyConnectedComponent V :=
  @Quotient.mk' _ (stronglyConnectedSetoid V)
/-
**Quiver.StronglyConnectedComponent.** 是 Mathlib 中的一个实例，位于命名空间 `Quiver.StronglyC
onnectedComponent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe V (StronglyConnectedComponent V) :=
  ⟨StronglyConnectedComponent.mk⟩
/-
**Quiver.StronglyConnectedComponent.** 是 Mathlib 中的一个实例，位于命名空间 `Quiver.StronglyC
onnectedComponent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited V] : Inhabited (StronglyConnectedComponent V) :=
  ⟨(default : V)⟩
/-
**Quiver.StronglyConnectedComponent.eq** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Strongl
yConnectedComponent`。
形式化陈述：∀ {V : Type u_2} [inst : Quiver V] (a b : V),   Quiver.StronglyConnectedCo
mponent.mk a = Quiver.StronglyConnectedComponent.mk b ↔     Nonempty (Quiver.Pat
h a b) ∧ Nonempty (Quiver.Path b a)
参数：a b : V；Quiver.Path a b；Quiver.Path b a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b
-/
protected lemma eq (a b : V) :
  (a : StronglyConnectedComponent V) = b
    ↔ (Nonempty (Path a b) ∧ Nonempty (Path b a)) := Quotient.eq''
/-
**Quiver.StronglyConnectedComponent.mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.S
tronglyConnectedComponent`。
形式化陈述：∀ {V : Type u_2} [inst : Quiver V] {a b : V},   Quiver.StronglyConnectedCo
mponent.mk a = Quiver.StronglyConnectedComponent.mk b ↔     Nonempty (Quiver.Pat
h a b) ∧ Nonempty (Quiver.Path b a)
参数：Quiver.Path a b；Quiver.Path b a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.StronglyConnectedComponent.eq`：∀ {V : Type u_2} [inst : Quiver V]
 (a b : V),   Quiver.StronglyConnectedComponent.mk a = Quiver.StronglyConnectedC
omponent.mk b ↔     Nonemp…
-/
@[simp] lemma mk_eq_mk {a b : V} :
    (StronglyConnectedComponent.mk a : StronglyConnectedComponent V) =
    StronglyConnectedComponent.mk b ↔ (Nonempty (Path a b) ∧ Nonempty (Path b a)) :=
  StronglyConnectedComponent.eq a b
/-
**Quiver.StronglyConnectedComponent.IsSStronglyConnected.pos_cycle** 是 Mathlib 中
的一个定理，位于命名空间 `Quiver.StronglyConnectedComponent.IsSStronglyConnected`。
形式化陈述：∀ {V : Type u_2} [inst : Quiver V], Quiver.IsSStronglyConnected V → ∀ (v :
 V), ∃ p, 0 < p.length
参数：v : V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsSStronglyConnected.pos_cycle (h : IsSStronglyConnected V) (v : V) :
    ∃ p : Path v v, 0 < p.length := h v v

end StronglyConnectedComponent

variable {V}

/-
**Quiver.stronglyConnectedComponent_eq_of_path** 是 Mathlib 中的一个引理，位于命名空间 `Quiver
`。
形式化陈述：stronglyConnectedComponent_eq_of_path {a b : V} (hab : Nonempty (Path a b)
) (hba : Nonempty (Path b a)) : (a : StronglyConnectedComponent V) = b
参数：hab : Nonempty (Path a b)；hba : Nonempty (Path b a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quiver.StronglyConnectedComponent.eq`：∀ {V : Type u_2} [inst : Quiver V]
 (a b : V),   Quiver.StronglyConnectedComponent.mk a = Quiver.StronglyConnectedC
omponent.mk b ↔     Nonemp…
-/
lemma stronglyConnectedComponent_eq_of_path {a b : V}
    (hab : Nonempty (Path a b)) (hba : Nonempty (Path b a)) :
    (a : StronglyConnectedComponent V) = b :=
  (StronglyConnectedComponent.eq (a := a) (b := b)).2 ⟨hab, hba⟩
/-
**Quiver.exists_path_of_stronglyConnectedComponent_eq** 是 Mathlib 中的一个引理，位于命名空间 
`Quiver`。
形式化陈述：exists_path_of_stronglyConnectedComponent_eq {a b : V} (h : (a : StronglyC
onnectedComponent V) = b) : (Nonempty (Path a b)) ∧ (Nonempty (Path b a))
参数：h : (a : StronglyConnectedComponent V) = b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Quiver.StronglyConnectedComponent.eq`：∀ {V : Type u_2} [inst : Quiver V]
 (a b : V),   Quiver.StronglyConnectedComponent.mk a = Quiver.StronglyConnectedC
omponent.mk b ↔     Nonemp…
-/
lemma exists_path_of_stronglyConnectedComponent_eq {a b : V}
    (h : (a : StronglyConnectedComponent V) = b) :
    (Nonempty (Path a b)) ∧ (Nonempty (Path b a)) :=
  (StronglyConnectedComponent.eq (a := a) (b := b)).1 h
/-
**Quiver.stronglyConnectedComponent_singleton_iff** 是 Mathlib 中的一个引理，位于命名空间 `Qui
ver`。
形式化陈述：stronglyConnectedComponent_singleton_iff (v : V) : (forall w : V, (w : Str
onglyConnectedComponent V) = v -> w = v) ↔ (forall w : V, w != v -> ¬(Nonempty (
Path v w) ∧ Nonempty (Path w v)))
参数：v : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Quiver.stronglyConnectedComponent_eq_of_path`：stronglyConnectedComponent
_eq_of_path {a b : V} (hab : Nonempty (Path a b)) (hba : Nonempty (Path b a)) : 
(a : StronglyConnectedComponent V)…
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `Quiver.exists_path_of_stronglyConnectedComponent_eq`：exists_path_of_stro
nglyConnectedComponent_eq {a b : V} (h : (a : StronglyConnectedComponent V) = b)
 : (Nonempty (Path a b)) ∧ (Nonempty (Pat…
-/
lemma stronglyConnectedComponent_singleton_iff (v : V) :
    (∀ w : V, (w : StronglyConnectedComponent V) = v → w = v) ↔
    (∀ w : V, w ≠ v → ¬(Nonempty (Path v w) ∧ Nonempty (Path w v))) := by
  constructor
  · intro h_singleton w hw_ne h_bidir
    obtain ⟨hab, hba⟩ := h_bidir
    have h_same_scc : (w : StronglyConnectedComponent V) = v :=
      stronglyConnectedComponent_eq_of_path (a := w) (b := v) hba hab
    obtain ⟨rfl⟩ := h_singleton w h_same_scc
    contradiction
  · intro h_no_bidir w h_same_scc
    by_contra hw_ne
    obtain ⟨hab, hba⟩ :=
      exists_path_of_stronglyConnectedComponent_eq (a := w) (b := v) h_same_scc
    exact (h_no_bidir w hw_ne) ⟨hba, hab⟩
/-
**Quiver.IsStronglyConnected.isStronglyConnected_symmetrify** 是 Mathlib 中的一个定理，位
于命名空间 `Quiver.IsStronglyConnected`。
形式化陈述：∀ {V : Type u_2} [inst : Quiver V], Quiver.IsStronglyConnected V → Quiver.
IsStronglyConnected (Quiver.Symmetrify V)
参数：Quiver.Symmetrify V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsStronglyConnected.isStronglyConnected_symmetrify (h : IsStronglyConnected V) :
    IsStronglyConnected (Symmetrify V) := by
  intro a b
  obtain ⟨p⟩ := h a b
  induction p with
  | nil => exact ⟨Path.nil⟩
  | cons q e ih => exact ⟨ih.some.cons (Sum.inl e)⟩
/-
**Quiver.IsStronglyConnected.isSStronglyConnected_of_hom** 是 Mathlib 中的一个定理，位于命名
空间 `Quiver.IsStronglyConnected`。
形式化陈述：∀ {V : Type u_2} [inst : Quiver V],   Quiver.IsStronglyConnected V → ∀ {i₀
 j₀ : V} (e₀ : i₀ ⟶ j₀), Quiver.IsSStronglyConnected V
参数：e₀ : i₀ ⟶ j₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Quiver.Path.length_comp`：∀ {V : Type u} [inst : Quiver V] {a b : V} (p :
 Quiver.Path a b) {c : V} (q : Quiver.Path b c),   (p.comp q).length = p.length 
+ q.length
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
-/
lemma IsStronglyConnected.isSStronglyConnected_of_hom (h_sc : IsStronglyConnected V)
    {i₀ j₀ : V} (e₀ : i₀ ⟶ j₀) :
    IsSStronglyConnected V := by
  intro i j
  obtain ⟨p₁⟩ := h_sc i i₀
  obtain ⟨p₂⟩ := h_sc j₀ j
  let p : Path i j := p₁.comp (e₀.toPath.comp p₂)
  have hp_pos : 0 < p.length := by
    simpa [p, Path.length_comp, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.succ_pos (p₁.length + p₂.length)
  exact ⟨p, hp_pos⟩

end StronglyConnected

end Quiver

