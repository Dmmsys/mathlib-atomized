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
/--
Definition of `zigzagSetoid` / `zigzagSetoid` 的定义

English:
definition zigzagSetoid
  signature: : Setoid V
  body: ⟨fun a b => Nonempty (@Path (Symmetrify V) _ a b), fun _ => ⟨Path.nil⟩, fun ⟨p⟩ =>
    ⟨p.reverse⟩, fun ⟨p⟩ ⟨q⟩ => ⟨p.comp q⟩⟩

中文:
定义 zigzagSetoid
  签名: : 集合等价关系 V
  定义体: ⟨fun a b => Nonempty (@Path (Symmetrify V) _ a b), fun _ => ⟨Path.nil⟩, fun ⟨p⟩ =>
    ⟨p.reverse⟩, fun ⟨p⟩ ⟨q⟩ => ⟨p.comp q⟩⟩

Depends on / 依赖: Nonempty, Path.nil, Symmetrify, p.comp, p.reverse, reverse
-/
def zigzagSetoid : Setoid V :=
  ⟨fun a b => Nonempty (@Path (Symmetrify V) _ a b), fun _ => ⟨Path.nil⟩, fun ⟨p⟩ =>
    ⟨p.reverse⟩, fun ⟨p⟩ ⟨q⟩ => ⟨p.comp q⟩⟩

/--
Definition of `WeaklyConnectedComponent` / `WeaklyConnectedComponent` 的定义

English:
definition WeaklyConnectedComponent
  signature: : Type _
  body: Quotient (zigzagSetoid V)

中文:
定义 WeaklyConnectedComponent
  签名: : 类型 _
  定义体: Quotient (zigzagSetoid V)

Depends on / 依赖: Quotient, zigzagSetoid
-/
def WeaklyConnectedComponent : Type _ :=
  Quotient (zigzagSetoid V)

namespace WeaklyConnectedComponent

variable {V}

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : V -> WeaklyConnectedComponent V
  body: @Quotient.mk' _ (zigzagSetoid V)

中文:
定义 mk
  签名: : V -> WeaklyConnectedComponent V
  定义体: @Quotient.mk' _ (zigzagSetoid V)
-/
protected def mk : V -> WeaklyConnectedComponent V :=
  @Quotient.mk' _ (zigzagSetoid V)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC V (WeaklyConnectedComponent V)
  body: ⟨WeaklyConnectedComponent.mk⟩

中文:
实例 :
  签名: CoeTC V (WeaklyConnectedComponent V)
  定义体: ⟨WeaklyConnectedComponent.mk⟩

Depends on / 依赖: WeaklyConnectedComponent, WeaklyConnectedComponent.mk
-/
instance : CoeTC V (WeaklyConnectedComponent V) :=
  ⟨WeaklyConnectedComponent.mk⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: V] : Inhabited (WeaklyConnectedComponent V)
  body: ⟨show V from default⟩

中文:
实例 [可居
  签名: V] : 可居 (WeaklyConnectedComponent V)
  定义体: ⟨show V from default⟩
-/
instance [Inhabited V] : Inhabited (WeaklyConnectedComponent V) :=
  ⟨show V from default⟩

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: (a b : V)
  proof: Quotient.eq''

中文:
定理 eq
  条件: (a b : V)
  证明: Quotient.eq''
-/
protected theorem eq (a b : V) :
    (a : WeaklyConnectedComponent V) = b ↔ Nonempty (@Path (Symmetrify V) _ a b) :=
  Quotient.eq''

end WeaklyConnectedComponent

variable {V}

/--
Definition of `wideSubquiverSymmetrify` / `wideSubquiverSymmetrify` 的定义

English:
definition wideSubquiverSymmetrify
  signature: (H : WideSubquiver (Symmetrify V))
  body: fun a b => {e | .inl e in H a b ∨ .inr e in H b a}

中文:
定义 wideSubquiverSymmetrify
  签名: (H : WideSubquiver (Symmetrify V))
  定义体: fun a b => {e | .inl e in H a b ∨ .inr e in H b a}
-/
def wideSubquiverSymmetrify (H : WideSubquiver (Symmetrify V)) : WideSubquiver V :=
  fun a b => {e | .inl e in H a b ∨ .inr e in H b a}

/-!
## Strongly connected components (directed connectivity)

We define strong connectivity (`IsStronglyConnected`), its positive-length refinement
(`IsSStronglyConnected`), and strongly connected components.
-/

section StronglyConnected

variable (V : Type*) [Quiver V]

/--
Definition of `IsStronglyConnected` / `IsStronglyConnected` 的定义

English:
definition IsStronglyConnected
  signature: : Prop
  body: forall i j : V, Nonempty (Path i j)

中文:
定义 IsStronglyConnected
  签名: : 命题
  定义体: forall i j : V, Nonempty (Path i j)

Depends on / 依赖: Nonempty
-/
def IsStronglyConnected : Prop :=
  forall i j : V, Nonempty (Path i j)

/--
Definition of `IsSStronglyConnected` / `IsSStronglyConnected` 的定义

English:
definition IsSStronglyConnected
  signature: : Prop
  body: forall i j : V, exists p : Path i j, 0 < p.length

中文:
定义 IsSStronglyConnected
  签名: : 命题
  定义体: forall i j : V, exists p : Path i j, 0 < p.length

Depends on / 依赖: length, p.length
-/
def IsSStronglyConnected : Prop :=
  forall i j : V, exists p : Path i j, 0 < p.length

/--
lemma `isStronglyConnected_iff` / 引理 `isStronglyConnected_iff`

English:
lemma isStronglyConnected_iff
  proof: Iff.rfl

中文:
引理 isStronglyConnected_iff
  证明: Iff.rfl
-/
@[simp] lemma isStronglyConnected_iff :
    IsStronglyConnected V ↔ forall i j : V, Nonempty (Path i j) := Iff.rfl

/--
lemma `isSStronglyConnected_iff` / 引理 `isSStronglyConnected_iff`

English:
lemma isSStronglyConnected_iff
  proof: Iff.rfl

中文:
引理 isSStronglyConnected_iff
  证明: Iff.rfl
-/
@[simp] lemma isSStronglyConnected_iff :
    IsSStronglyConnected V ↔ forall i j : V, exists p : Path i j, 0 < p.length := Iff.rfl

/--
lemma `IsStronglyConnected.nonempty_path` / 引理 `IsStronglyConnected.nonempty_path`

English:
lemma IsStronglyConnected.nonempty_path
  proof: h i j

中文:
引理 IsStronglyConnected.nonempty_path
  证明: h i j
-/
lemma IsStronglyConnected.nonempty_path
    (h : IsStronglyConnected V) (i j : V) : Nonempty (Path i j) := h i j

/--
lemma `IsSStronglyConnected.exists_pos_path` / 引理 `IsSStronglyConnected.exists_pos_path`

English:
lemma IsSStronglyConnected.exists_pos_path
  proof: h i j

中文:
引理 IsSStronglyConnected.存在_pos_path
  证明: h i j
-/
lemma IsSStronglyConnected.exists_pos_path
    (h : IsSStronglyConnected V) (i j : V) : exists p : Path i j, 0 < p.length := h i j

/--
lemma `IsSStronglyConnected.exists_pos_cycle` / 引理 `IsSStronglyConnected.exists_pos_cycle`

English:
lemma IsSStronglyConnected.exists_pos_cycle
  proof: h i i

中文:
引理 IsSStronglyConnected.存在_pos_cycle
  证明: h i i
-/
lemma IsSStronglyConnected.exists_pos_cycle
    (h : IsSStronglyConnected V) (i : V) : exists p : Path i i, 0 < p.length := h i i

/--
lemma `IsSStronglyConnected.isStronglyConnected` / 引理 `IsSStronglyConnected.isStronglyConnected`

English:
lemma IsSStronglyConnected.isStronglyConnected
  proof: by
  intro i j; obtain ⟨p, _⟩ := h i j; exact ⟨p⟩

中文:
引理 IsSStronglyConnected.isStronglyConnected
  证明: by
  intro i j; obtain ⟨p, _⟩ := h i j; exact ⟨p⟩
-/
lemma IsSStronglyConnected.isStronglyConnected
    (h : IsSStronglyConnected V) : IsStronglyConnected V := by
  intro i j; obtain ⟨p, _⟩ := h i j; exact ⟨p⟩

/-- Equivalence relation identifying vertices connected by directed paths in both directions. -/
@[instance_reducible]
/--
Definition of `stronglyConnectedSetoid` / `stronglyConnectedSetoid` 的定义

English:
definition stronglyConnectedSetoid
  signature: : Setoid V
  body: ⟨fun a b => (Nonempty (Path a b)) ∧ (Nonempty (Path b a)),
   fun _ => ⟨⟨Path.nil⟩, ⟨Path.nil⟩⟩, fun ⟨hab, hba⟩ => ⟨hba, hab⟩, fun ⟨hab, hba⟩ ⟨hbc, hcb⟩ =>
     ⟨⟨hab.some.comp hbc.some⟩, ⟨hcb.some.comp hba.some⟩⟩⟩

中文:
定义 stronglyConnectedSetoid
  签名: : 集合等价关系 V
  定义体: ⟨fun a b => (Nonempty (Path a b)) ∧ (Nonempty (Path b a)),
   fun _ => ⟨⟨Path.nil⟩, ⟨Path.nil⟩⟩, fun ⟨hab, hba⟩ => ⟨hba, hab⟩, fun ⟨hab, hba⟩ ⟨hbc, hcb⟩ =>
     ⟨⟨hab.some.comp hbc.some⟩, ⟨hcb.some.comp hba.some⟩⟩⟩

Depends on / 依赖: Nonempty, Path.nil, hab.some.comp, hba.some, hbc.some, hcb.some.comp
-/
def stronglyConnectedSetoid : Setoid V :=
  ⟨fun a b => (Nonempty (Path a b)) ∧ (Nonempty (Path b a)),
   fun _ => ⟨⟨Path.nil⟩, ⟨Path.nil⟩⟩, fun ⟨hab, hba⟩ => ⟨hba, hab⟩, fun ⟨hab, hba⟩ ⟨hbc, hcb⟩ =>
     ⟨⟨hab.some.comp hbc.some⟩, ⟨hcb.some.comp hba.some⟩⟩⟩

/--
Definition of `StronglyConnectedComponent` / `StronglyConnectedComponent` 的定义

English:
definition StronglyConnectedComponent
  signature: : Type _
  body: Quotient (stronglyConnectedSetoid V)

中文:
定义 StronglyConnectedComponent
  签名: : 类型 _
  定义体: Quotient (stronglyConnectedSetoid V)

Depends on / 依赖: Quotient, stronglyConnectedSetoid
-/
def StronglyConnectedComponent : Type _ :=
  Quotient (stronglyConnectedSetoid V)

namespace StronglyConnectedComponent

variable {V}

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : V -> StronglyConnectedComponent V
  body: @Quotient.mk' _ (stronglyConnectedSetoid V)

中文:
定义 mk
  签名: : V -> StronglyConnectedComponent V
  定义体: @Quotient.mk' _ (stronglyConnectedSetoid V)
-/
protected def mk : V -> StronglyConnectedComponent V :=
  @Quotient.mk' _ (stronglyConnectedSetoid V)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe V (StronglyConnectedComponent V)
  body: ⟨StronglyConnectedComponent.mk⟩

中文:
实例 :
  签名: Coe V (StronglyConnectedComponent V)
  定义体: ⟨StronglyConnectedComponent.mk⟩

Depends on / 依赖: StronglyConnectedComponent, StronglyConnectedComponent.mk
-/
instance : Coe V (StronglyConnectedComponent V) :=
  ⟨StronglyConnectedComponent.mk⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: V] : Inhabited (StronglyConnectedComponent V)
  body: ⟨(default : V)⟩

中文:
实例 [可居
  签名: V] : 可居 (StronglyConnectedComponent V)
  定义体: ⟨(default : V)⟩
-/
instance [Inhabited V] : Inhabited (StronglyConnectedComponent V) :=
  ⟨(default : V)⟩

/--
lemma `eq` / 引理 `eq`

English:
lemma eq
  given: (a b : V)
  proof: Quotient.eq''

中文:
引理 eq
  条件: (a b : V)
  证明: Quotient.eq''
-/
protected lemma eq (a b : V) :
  (a : StronglyConnectedComponent V) = b
    ↔ (Nonempty (Path a b) ∧ Nonempty (Path b a)) := Quotient.eq''

/--
lemma `mk_eq_mk` / 引理 `mk_eq_mk`

English:
lemma mk_eq_mk
  given: {a b : V}
  proof: StronglyConnectedComponent.eq a b

中文:
引理 mk_eq_mk
  条件: {a b : V}
  证明: StronglyConnectedComponent.eq a b
-/
@[simp] lemma mk_eq_mk {a b : V} :
    (StronglyConnectedComponent.mk a : StronglyConnectedComponent V) =
    StronglyConnectedComponent.mk b ↔ (Nonempty (Path a b) ∧ Nonempty (Path b a)) :=
  StronglyConnectedComponent.eq a b

/--
lemma `IsSStronglyConnected.pos_cycle` / 引理 `IsSStronglyConnected.pos_cycle`

English:
lemma IsSStronglyConnected.pos_cycle
  given: (h : IsSStronglyConnected V) (v : V)
  proof: h v v

中文:
引理 IsSStronglyConnected.pos_cycle
  条件: (h : IsSStronglyConnected V) (v : V)
  证明: h v v
-/
lemma IsSStronglyConnected.pos_cycle (h : IsSStronglyConnected V) (v : V) :
    exists p : Path v v, 0 < p.length := h v v

end StronglyConnectedComponent

variable {V}

/--
lemma `stronglyConnectedComponent_eq_of_path` / 引理 `stronglyConnectedComponent_eq_of_path`

English:
lemma stronglyConnectedComponent_eq_of_path
  statement: {a b : V}
  proof: (StronglyConnectedComponent.eq (a := a) (b := b)).2 ⟨hab, hba⟩

中文:
引理 stronglyConnectedComponent_eq_of_path
  结论: {a b : V}
  证明: (StronglyConnectedComponent.eq (a := a) (b := b)).2 ⟨hab, hba⟩

Depends on / 依赖: StronglyConnectedComponent, StronglyConnectedComponent.eq
-/
lemma stronglyConnectedComponent_eq_of_path {a b : V}
    (hab : Nonempty (Path a b)) (hba : Nonempty (Path b a)) :
    (a : StronglyConnectedComponent V) = b :=
  (StronglyConnectedComponent.eq (a := a) (b := b)).2 ⟨hab, hba⟩

/--
lemma `exists_path_of_stronglyConnectedComponent_eq` / 引理 `exists_path_of_stronglyConnectedComponent_eq`

English:
lemma exists_path_of_stronglyConnectedComponent_eq
  statement: {a b : V}
  proof: (StronglyConnectedComponent.eq (a := a) (b := b)).1 h

中文:
引理 存在_path_of_stronglyConnectedComponent_eq
  结论: {a b : V}
  证明: (StronglyConnectedComponent.eq (a := a) (b := b)).1 h

Depends on / 依赖: StronglyConnectedComponent, StronglyConnectedComponent.eq
-/
lemma exists_path_of_stronglyConnectedComponent_eq {a b : V}
    (h : (a : StronglyConnectedComponent V) = b) :
    (Nonempty (Path a b)) ∧ (Nonempty (Path b a)) :=
  (StronglyConnectedComponent.eq (a := a) (b := b)).1 h

/--
lemma `stronglyConnectedComponent_singleton_iff` / 引理 `stronglyConnectedComponent_singleton_iff`

English:
lemma stronglyConnectedComponent_singleton_iff
  given: (v : V)
  proof: by
  constructor
  · intro h_singleton w hw_ne h_bidir
    obtain ⟨hab, hba⟩ := h_bidir
    have h_same_scc : (w : StronglyConnectedComponent V) = v :=
      stronglyConnectedComponent_eq_of_path (a := w) (b := v) hba hab
    obtain ⟨rfl⟩ := h_singleton w h_same_scc
    contradiction
  · intro h_no_

中文:
引理 stronglyConnectedComponent_singleton_iff
  条件: (v : V)
  证明: by
  constructor
  · intro h_singleton w hw_ne h_bidir
    obtain ⟨hab, hba⟩ := h_bidir
    have h_same_scc : (w : StronglyConnectedComponent V) = v :=
      stronglyConnectedComponent_eq_of_path (a := w) (b := v) hba hab
    obtain ⟨rfl⟩ := h_singleton w h_same_scc
    contradiction
  · intro h_no_

Depends on / 依赖: StronglyConnectedComponent, exists_path_of_stronglyConnectedComponent_eq, h_bidir, h_no_bidir, h_same_scc, h_singleton, hw_ne, stronglyConnectedComponent_eq_of_path
-/
lemma stronglyConnectedComponent_singleton_iff (v : V) :
    (forall w : V, (w : StronglyConnectedComponent V) = v -> w = v) ↔
    (forall w : V, w != v -> ¬(Nonempty (Path v w) ∧ Nonempty (Path w v))) := by
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

/--
lemma `IsStronglyConnected.isStronglyConnected_symmetrify` / 引理 `IsStronglyConnected.isStronglyConnected_symmetrify`

English:
lemma IsStronglyConnected.isStronglyConnected_symmetrify
  given: (h : IsStronglyConnected V)
  proof: by
  intro a b
  obtain ⟨p⟩ := h a b
  induction p with
  | nil => exact ⟨Path.nil⟩
  | cons q e ih => exact ⟨ih.some.cons (Sum.inl e)⟩

中文:
引理 IsStronglyConnected.isStronglyConnected_symmetrify
  条件: (h : IsStronglyConnected V)
  证明: by
  intro a b
  obtain ⟨p⟩ := h a b
  induction p with
  | nil => exact ⟨Path.nil⟩
  | cons q e ih => exact ⟨ih.some.cons (Sum.inl e)⟩

Depends on / 依赖: Path.nil, Sum.inl, ih.some.cons
-/
lemma IsStronglyConnected.isStronglyConnected_symmetrify (h : IsStronglyConnected V) :
    IsStronglyConnected (Symmetrify V) := by
  intro a b
  obtain ⟨p⟩ := h a b
  induction p with
  | nil => exact ⟨Path.nil⟩
  | cons q e ih => exact ⟨ih.some.cons (Sum.inl e)⟩

/--
lemma `IsStronglyConnected.isSStronglyConnected_of_hom` / 引理 `IsStronglyConnected.isSStronglyConnected_of_hom`

English:
lemma IsStronglyConnected.isSStronglyConnected_of_hom
  statement: (h_sc : IsStronglyConnected V)
  proof: by
  intro i j
  obtain ⟨p₁⟩ := h_sc i i₀
  obtain ⟨p₂⟩ := h_sc j₀ j
  let p : Path i j := p₁.comp (e₀.toPath.comp p₂)
  have hp_pos : 0 < p.length := by
    simpa [p, Path.length_comp, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.succ_pos (p₁.length + p₂.length)
  exact ⟨p, hp_po

中文:
引理 IsStronglyConnected.isSStronglyConnected_of_hom
  结论: (h_sc : IsStronglyConnected V)
  证明: by
  intro i j
  obtain ⟨p₁⟩ := h_sc i i₀
  obtain ⟨p₂⟩ := h_sc j₀ j
  let p : Path i j := p₁.comp (e₀.toPath.comp p₂)
  have hp_pos : 0 < p.length := by
    simpa [p, Path.length_comp, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.succ_pos (p₁.length + p₂.length)
  exact ⟨p, hp_po

Depends on / 依赖: Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.succ_pos, Path.length_comp, add_assoc, add_comm, add_left_comm, h_sc, hp_pos, length, length_comp, p.length, succ_pos, toPath, toPath.comp
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
