/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Structure groupoids

This file contains the definitions and properties of structure groupoids, i.e., sets of open partial
homeomorphisms stable under composition and inverse. These are used to define charted spaces (and
hence manifolds). See the file `Mathlib.Geometry.Manifold.ChartedSpace` for more details.

## Main definitions

* `StructureGroupoid H` : a subset of open partial homeomorphisms of `H` stable under composition,
  inverse and restriction (ex: partial diffeomorphisms).
* `continuousGroupoid H` : the groupoid of all open partial homeomorphisms of `H`.

Additional useful definitions:

* `Pregroupoid H` : a subset of partial maps of `H` stable under composition and
  restriction, but not inverse (ex: smooth maps)
* `Pregroupoid.groupoid` : construct a groupoid from a pregroupoid, by requiring that a map and
  its inverse both belong to the pregroupoid (ex: construct diffeos from smooth maps)

## Notation

In the scope `Manifold`, we denote the composition of open partial homeomorphisms with `≫ₕ`, and the
composition of partial equivs with `≫`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Topology

variable {H : Type*}

/- Notational shortcut for the composition of open partial homeomorphisms and partial equivs, i.e.,
`OpenPartialHomeomorph.trans` and `PartialEquiv.trans`.
Note that, as is usual for equivs, the composition is from left to right, hence the direction of
the arrow. -/
@[inherit_doc] scoped[Manifold] infixr:100 " ≫ₕ " => OpenPartialHomeomorph.trans

@[inherit_doc] scoped[Manifold] infixr:100 " ≫ " => PartialEquiv.trans

open Set OpenPartialHomeomorph Manifold

/-! ### Structure groupoids -/

section Groupoid

/-! One could add to the definition of a structure groupoid the fact that the restriction of an
element of the groupoid to any open set still belongs to the groupoid.
(This is in Kobayashi-Nomizu.)
I am not sure I want this, for instance on `H × E` where `E` is a vector space, and the groupoid is
made of functions respecting the fibers and linear in the fibers (so that a charted space over this
groupoid is naturally a vector bundle) I prefer that the members of the groupoid are always
defined on sets of the form `s × E`. There is a typeclass `ClosedUnderRestriction` for groupoids
which have the restriction property.

The only nontrivial requirement is locality: if an open partial homeomorphism belongs to the
groupoid around each point in its domain of definition, then it belongs to the groupoid. Without
this requirement, the composition of structomorphisms does not have to be a structomorphism. Note
that this implies that an open partial homeomorphism with empty source belongs to any structure
groupoid, as it trivially satisfies this condition.

There is also a technical point, related to the fact that an open partial homeomorphism is by
definition a global map which is a homeomorphism when restricted to its source subset (and its
values outside of the source are not relevant). Therefore, we also require that being a member of
the groupoid only depends on the values on the source.

We use primes in the structure names as we will reformulate them below (without primes) using a
`Membership` instance, writing `e ∈ G` instead of `e ∈ G.members`.
-/


/--
Definition of `StructureGroupoid` / `StructureGroupoid` 的定义

English:
structure StructureGroupoid
  parameters: (H : Type*) [TopologicalSpace H]
  axioms and operations (6):
    - members : Set (OpenPartialHomeomorph H H)
    - trans' : forall e e' : OpenPartialHomeomorph H H, e in members -> e' in members -> e ≫ₕ e' in members
    - symm' : forall e : OpenPartialHomeomorph H H, e in members -> e.symm in members
    - id_mem' : OpenPartialHomeomorph.refl H in members
    - locality' : forall e : OpenPartialHomeomorph H H, (forall x in e.source, exists s, IsOpen s ∧ x in s ∧ e.restr s in members) -> e in members
    - mem_of_eqOnSource' : forall e e' : OpenPartialHomeomorph H H, e in members -> e' ≈ e -> e' in members

中文:
结构 StructureGroupoid
  参数: (H : 类型) [TopologicalSpace H]
  公理与运算 (6 个):
    - members : Set (OpenPartialHomeomorph H H)
    - trans' : 对任意 e e' : OpenPartialHomeomorph H H, e in members -> e' in members -> e ≫ₕ e' in members
    - symm' : 对任意 e : OpenPartialHomeomorph H H, e in members -> e.symm in members
    - id_mem' : OpenPartialHomeomorph.refl H in members
    - locality' : 对任意 e : OpenPartialHomeomorph H H, (对任意 x in e.source, 存在 s, IsOpen s ∧ x in s ∧ e.restr s in members) -> e in members
    - mem_of_eqOnSource' : 对任意 e e' : OpenPartialHomeomorph H H, e in members -> e' ≈ e -> e' in members
-/
structure StructureGroupoid (H : Type*) [TopologicalSpace H] where
  /-- Members of the structure groupoid are open partial homeomorphisms. -/
  members : Set (OpenPartialHomeomorph H H)
  /-- Structure groupoids are stable under composition. -/
  trans' : forall e e' : OpenPartialHomeomorph H H, e in members -> e' in members -> e ≫ₕ e' in members
  /-- Structure groupoids are stable under inverse. -/
  symm' : forall e : OpenPartialHomeomorph H H, e in members -> e.symm in members
  /-- The identity morphism lies in the structure groupoid. -/
  id_mem' : OpenPartialHomeomorph.refl H in members
  /-- Let `e` be an open partial homeomorphism. If for every `x ∈ e.source`, the restriction of e
  to some open set around `x` lies in the groupoid, then `e` lies in the groupoid. -/
  locality' : forall e : OpenPartialHomeomorph H H,
    (forall x in e.source, exists s, IsOpen s ∧ x in s ∧ e.restr s in members) -> e in members
  /-- Membership in a structure groupoid respects the equivalence of open partial homeomorphisms. -/
  mem_of_eqOnSource' : forall e e' : OpenPartialHomeomorph H H, e in members -> e' ≈ e -> e' in members

variable [TopologicalSpace H]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership (OpenPartialHomeomorph H H) (StructureGroupoid H)
  body: ⟨fun (G : StructureGroupoid H) (e : OpenPartialHomeomorph H H) => e in G.members⟩

中文:
实例 :
  签名: Membership (OpenPartialHomeomorph H H) (StructureGroupoid H)
  定义体: ⟨fun (G : StructureGroupoid H) (e : OpenPartialHomeomorph H H) => e in G.members⟩

Depends on / 依赖: G.members, OpenPartialHomeomorph, StructureGroupoid, members
-/
instance : Membership (OpenPartialHomeomorph H H) (StructureGroupoid H) :=
  ⟨fun (G : StructureGroupoid H) (e : OpenPartialHomeomorph H H) => e in G.members⟩

instance (H : Type*) [TopologicalSpace H] :
    SetLike (StructureGroupoid H) (OpenPartialHomeomorph H H) where
  coe s := s.members
  coe_injective N O h := by cases N; cases O; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (StructureGroupoid H)
  body: ⟨fun G G' => StructureGroupoid.mk
    (members := G.members inter G'.members)
    (trans' := fun e e' he he' =>
      ⟨G.trans' e e' he.left he'.left, G'.trans' e e' he.right he'.right⟩)
    (symm' := fun e he => ⟨G.symm' e he.left, G'.symm' e he.right⟩)
    (id_mem' := ⟨G.id_mem', G'.id_mem'⟩)
    

中文:
实例 :
  签名: Min (StructureGroupoid H)
  定义体: ⟨fun G G' => StructureGroupoid.mk
    (members := G.members inter G'.members)
    (trans' := fun e e' he he' =>
      ⟨G.trans' e e' he.left he'.left, G'.trans' e e' he.right he'.right⟩)
    (symm' := fun e he => ⟨G.symm' e he.left, G'.symm' e he.right⟩)
    (id_mem' := ⟨G.id_mem', G'.id_mem'⟩)
    

Depends on / 依赖: And.intro, G.id_mem, G.locality, G.members, G.symm, G.trans, StructureGroupoid, StructureGroupoid.mk, all_goals, he.left, he.right, hs.left, id_mem, locality, mem_inter_iff, members
-/
instance : Min (StructureGroupoid H) :=
  ⟨fun G G' => StructureGroupoid.mk
    (members := G.members inter G'.members)
    (trans' := fun e e' he he' =>
      ⟨G.trans' e e' he.left he'.left, G'.trans' e e' he.right he'.right⟩)
    (symm' := fun e he => ⟨G.symm' e he.left, G'.symm' e he.right⟩)
    (id_mem' := ⟨G.id_mem', G'.id_mem'⟩)
    (locality' := by
      intro e hx
      apply (mem_inter_iff e G.members G'.members).mpr
      refine And.intro (G.locality' e ?_) (G'.locality' e ?_)
      all_goals
        intro x hex
        rcases hx x hex with ⟨s, hs⟩
        use s
        refine And.intro hs.left (And.intro hs.right.left ?_)
      · exact hs.right.right.left
      · exact hs.right.right.right)
    (mem_of_eqOnSource' := fun e e' he hee' =>
      ⟨G.mem_of_eqOnSource' e e' he.left hee', G'.mem_of_eqOnSource' e e' he.right hee'⟩)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (StructureGroupoid H)
  body: ⟨fun S => StructureGroupoid.mk
    (members := ⋂ s in S, s.members)
    (trans' := by
      simp only [mem_iInter]
      intro e e' he he' i hi
      exact i.trans' e e' (he i hi) (he' i hi))
    (symm' := by
      simp only [mem_iInter]
      intro e he i hi
      exact i.symm' e (he i hi))
    (id

中文:
实例 :
  签名: InfSet (StructureGroupoid H)
  定义体: ⟨fun S => StructureGroupoid.mk
    (members := ⋂ s in S, s.members)
    (trans' := by
      simp only [mem_iInter]
      intro e e' he he' i hi
      exact i.trans' e e' (he i hi) (he' i hi))
    (symm' := by
      simp only [mem_iInter]
      intro e he i hi
      exact i.symm' e (he i hi))
    (id

Depends on / 依赖: StructureGroupoid, StructureGroupoid.mk, hs.left, hs.right.left, hs.right.right, i.id_mem, i.locality, i.symm, i.trans, id_mem, locality, mem_iInter, mem_of_e, members, s.members
-/
instance : InfSet (StructureGroupoid H) :=
  ⟨fun S => StructureGroupoid.mk
    (members := ⋂ s in S, s.members)
    (trans' := by
      simp only [mem_iInter]
      intro e e' he he' i hi
      exact i.trans' e e' (he i hi) (he' i hi))
    (symm' := by
      simp only [mem_iInter]
      intro e he i hi
      exact i.symm' e (he i hi))
    (id_mem' := by
      simp only [mem_iInter]
      intro i _
      exact i.id_mem')
    (locality' := by
      simp only [mem_iInter]
      intro e he i hi
      refine i.locality' e ?_
      intro x hex
      rcases he x hex with ⟨s, hs⟩
      exact ⟨s, ⟨hs.left, ⟨hs.right.left, hs.right.right i hi⟩⟩⟩)
    (mem_of_eqOnSource' := by
      simp only [mem_iInter]
      intro e e' he he'e
      exact fun i hi => i.mem_of_eqOnSource' e e' (he i hi) he'e)⟩

/--
theorem `StructureGroupoid.trans` / 定理 `StructureGroupoid.trans`

English:
theorem StructureGroupoid.trans
  statement: (G : StructureGroupoid H) {e e' : OpenPartialHomeomorph H H}
  proof: G.trans' e e' he he'

中文:
定理 StructureGroupoid.trans
  结论: (G : StructureGroupoid H) {e e' : OpenPartialHomeomorph H H}
  证明: G.trans' e e' he he'

Depends on / 依赖: G.trans
-/
theorem StructureGroupoid.trans (G : StructureGroupoid H) {e e' : OpenPartialHomeomorph H H}
    (he : e in G) (he' : e' in G) : e ≫ₕ e' in G :=
  G.trans' e e' he he'

/--
theorem `StructureGroupoid.symm` / 定理 `StructureGroupoid.symm`

English:
theorem StructureGroupoid.symm
  statement: (G : StructureGroupoid H) {e : OpenPartialHomeomorph H H}
  proof: G.symm' e he

中文:
定理 StructureGroupoid.symm
  结论: (G : StructureGroupoid H) {e : OpenPartialHomeomorph H H}
  证明: G.symm' e he

Depends on / 依赖: G.symm
-/
theorem StructureGroupoid.symm (G : StructureGroupoid H) {e : OpenPartialHomeomorph H H}
    (he : e in G) : e.symm in G :=
  G.symm' e he

/--
theorem `StructureGroupoid.id_mem` / 定理 `StructureGroupoid.id_mem`

English:
theorem StructureGroupoid.id_mem
  given: (G : StructureGroupoid H)
  statement: OpenPartialHomeomorph.refl H in G
  proof: G.id_mem'

中文:
定理 StructureGroupoid.id_mem
  条件: (G : StructureGroupoid H)
  结论: OpenPartialHomeomorph.refl H in G
  证明: G.id_mem'

Depends on / 依赖: G.id_mem, id_mem
-/
theorem StructureGroupoid.id_mem (G : StructureGroupoid H) : OpenPartialHomeomorph.refl H in G :=
  G.id_mem'

/--
theorem `StructureGroupoid.locality` / 定理 `StructureGroupoid.locality`

English:
theorem StructureGroupoid.locality
  statement: (G : StructureGroupoid H) {e : OpenPartialHomeomorph H H}
  proof: G.locality' e h

中文:
定理 StructureGroupoid.locality
  结论: (G : StructureGroupoid H) {e : OpenPartialHomeomorph H H}
  证明: G.locality' e h

Depends on / 依赖: G.locality, locality
-/
theorem StructureGroupoid.locality (G : StructureGroupoid H) {e : OpenPartialHomeomorph H H}
    (h : forall x in e.source, exists s, IsOpen s ∧ x in s ∧ e.restr s in G) : e in G :=
  G.locality' e h

/--
theorem `StructureGroupoid.mem_of_eqOnSource` / 定理 `StructureGroupoid.mem_of_eqOnSource`

English:
theorem StructureGroupoid.mem_of_eqOnSource
  statement: (G : StructureGroupoid H)
  proof: G.mem_of_eqOnSource' e e' he h

中文:
定理 StructureGroupoid.mem_of_eqOnSource
  结论: (G : StructureGroupoid H)
  证明: G.mem_of_eqOnSource' e e' he h

Depends on / 依赖: G.mem_of_eqOnSource, mem_of_eqOnSource
-/
theorem StructureGroupoid.mem_of_eqOnSource (G : StructureGroupoid H)
    {e e' : OpenPartialHomeomorph H H} (he : e in G) (h : e' ≈ e) : e' in G :=
  G.mem_of_eqOnSource' e e' he h

/--
theorem `StructureGroupoid.mem_iff_of_eqOnSource` / 定理 `StructureGroupoid.mem_iff_of_eqOnSource`

English:
theorem StructureGroupoid.mem_iff_of_eqOnSource
  statement: {G : StructureGroupoid H}
  proof: ⟨fun he => G.mem_of_eqOnSource he (Setoid.symm h), fun he' => G.mem_of_eqOnSource he' h⟩

中文:
定理 StructureGroupoid.mem_iff_of_eqOnSource
  结论: {G : StructureGroupoid H}
  证明: ⟨fun he => G.mem_of_eqOnSource he (Setoid.symm h), fun he' => G.mem_of_eqOnSource he' h⟩

Depends on / 依赖: G.mem_of_eqOnSource, Setoid, Setoid.symm, mem_of_eqOnSource
-/
theorem StructureGroupoid.mem_iff_of_eqOnSource {G : StructureGroupoid H}
    {e e' : OpenPartialHomeomorph H H} (h : e ≈ e') : e in G ↔ e' in G :=
  ⟨fun he => G.mem_of_eqOnSource he (Setoid.symm h), fun he' => G.mem_of_eqOnSource he' h⟩

/--
Instance `StructureGroupoid.partialOrder` / 实例 `StructureGroupoid.partialOrder`

English:
instance StructureGroupoid.partialOrder
  signature: : PartialOrder (StructureGroupoid H)
  body: PartialOrder.lift StructureGroupoid.members fun a b h => by
    cases a
    cases b
    dsimp at h
    induction h
    rfl

中文:
实例 StructureGroupoid.partialOrder
  签名: : PartialOrder (StructureGroupoid H)
  定义体: PartialOrder.lift StructureGroupoid.members fun a b h => by
    cases a
    cases b
    dsimp at h
    induction h
    rfl

Depends on / 依赖: PartialOrder, PartialOrder.lift, StructureGroupoid, StructureGroupoid.members, members
-/
instance StructureGroupoid.partialOrder : PartialOrder (StructureGroupoid H) :=
  PartialOrder.lift StructureGroupoid.members fun a b h => by
    cases a
    cases b
    dsimp at h
    induction h
    rfl

/--
theorem `StructureGroupoid.le_iff` / 定理 `StructureGroupoid.le_iff`

English:
theorem StructureGroupoid.le_iff
  given: {G₁ G₂ : StructureGroupoid H}
  statement: G₁ <= G₂ ↔ forall e, e in G₁ -> e in G₂
  proof: Iff.rfl

中文:
定理 StructureGroupoid.le_iff
  条件: {G₁ G₂ : StructureGroupoid H}
  结论: G₁ <= G₂ ↔ 对任意 e, e in G₁ -> e in G₂
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem StructureGroupoid.le_iff {G₁ G₂ : StructureGroupoid H} : G₁ <= G₂ ↔ forall e, e in G₁ -> e in G₂ :=
  Iff.rfl

/--
Definition of `idGroupoid` / `idGroupoid` 的定义

English:
definition idGroupoid
  signature: (H : Type*) [TopologicalSpace H]
  body: {OpenPartialHomeomorph.refl H} union { e : OpenPartialHomeomorph H H | e.source = ∅ }
  trans' e e' he he' := by
    rcases he with he | he
    · simpa only [mem_singleton_iff.1 he, refl_trans]
    · have : (e ≫ₕ e').source subseteq e.source := sep_subset _ _
      rw [he] at this
      have : e ≫ₕ 

中文:
定义 idGroupoid
  签名: (H : 类型) [TopologicalSpace H]
  定义体: {OpenPartialHomeomorph.refl H} union { e : OpenPartialHomeomorph H H | e.source = ∅ }
  trans' e e' he he' := by
    rcases he with he | he
    · simpa only [mem_singleton_iff.1 he, refl_trans]
    · have : (e ≫ₕ e').source subseteq e.source := sep_subset _ _
      rw [he] at this
      have : e ≫ₕ 

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.refl, e.source, source
-/
def idGroupoid (H : Type*) [TopologicalSpace H] : StructureGroupoid H where
  members := {OpenPartialHomeomorph.refl H} union { e : OpenPartialHomeomorph H H | e.source = ∅ }
  trans' e e' he he' := by
    rcases he with he | he
    · simpa only [mem_singleton_iff.1 he, refl_trans]
    · have : (e ≫ₕ e').source subseteq e.source := sep_subset _ _
      rw [he] at this
      have : e ≫ₕ e' in { e : OpenPartialHomeomorph H H | e.source = ∅ } := eq_bot_iff.2 this
      exact (mem_union _ _ _).2 (Or.inr this)
  symm' e he := by
    rcases (mem_union _ _ _).1 he with E | E
    · simp [mem_singleton_iff.mp E]
    · right
      simpa only [e.toPartialEquiv.image_source_eq_target.symm, mfld_simps] using! E
  id_mem' := mem_union_left _ rfl
  locality' e he := by
    rcases e.source.eq_empty_or_nonempty with h | h
    · right
      exact h
    · left
      rcases h with ⟨x, hx⟩
      rcases he x hx with ⟨s, open_s, xs, hs⟩
      have x's : x in (e.restr s).source := by
        rw [restr_source]; rw [open_s.interior_eq]
        exact ⟨hx, xs⟩
      rcases hs with hs | hs
      · replace hs : OpenPartialHomeomorph.restr e s = OpenPartialHomeomorph.refl H := by
          simpa only using! hs
        have : (e.restr s).source = univ := by
          rw [hs]
          simp
        have : e.toPartialEquiv.source inter interior s = univ := this
        have : univ subseteq interior s := by
          rw [← this]
          exact inter_subset_right
        have : s = univ := by rwa [open_s.interior_eq, univ_subset_iff] at this
        simpa only [this, restr_univ] using! hs
      · exfalso
        rw [mem_ofPred_eq] at hs
        rwa [hs] at x's
  mem_of_eqOnSource' e e' he he'e := by
    rcases he with he | he
    · left
      have : e = e' := by
        refine eq_of_eqOnSource_univ (Setoid.symm he'e) ?_ ?_ <;>
          rw [Set.mem_singleton_iff.1 he] <;> rfl
      rwa [← this]
    · right
      have he : e.toPartialEquiv.source = ∅ := he
      rwa [Set.mem_ofPred_eq, EqOnSource.source_eq he'e]

/--
Instance `instStructureGroupoidOrderBot` / 实例 `instStructureGroupoidOrderBot`

English:
instance instStructureGroupoidOrderBot
  signature: : OrderBot (StructureGroupoid H) where
  body: idGroupoid H
  bot_le := by
    intro u f hf
    have hf :
        f in {OpenPartialHomeomorph.refl H} union { e : OpenPartialHomeomorph H H | e.source = ∅ } :=
      hf
    simp only [singleton_union, mem_ofPred_eq, mem_insert_iff] at hf
    rcases hf with hf | hf
    · rw [hf]
      apply u.id_mem

中文:
实例 instStructureGroupoidOrderBot
  签名: : OrderBot (StructureGroupoid H) where
  定义体: idGroupoid H
  bot_le := by
    intro u f hf
    have hf :
        f in {OpenPartialHomeomorph.refl H} union { e : OpenPartialHomeomorph H H | e.source = ∅ } :=
      hf
    simp only [singleton_union, mem_ofPred_eq, mem_insert_iff] at hf
    rcases hf with hf | hf
    · rw [hf]
      apply u.id_mem

Depends on / 依赖: idGroupoid
-/
instance instStructureGroupoidOrderBot : OrderBot (StructureGroupoid H) where
  bot := idGroupoid H
  bot_le := by
    intro u f hf
    have hf :
        f in {OpenPartialHomeomorph.refl H} union { e : OpenPartialHomeomorph H H | e.source = ∅ } :=
      hf
    simp only [singleton_union, mem_ofPred_eq, mem_insert_iff] at hf
    rcases hf with hf | hf
    · rw [hf]
      apply u.id_mem
    · apply u.locality
      intro x hx
      rw [hf]; rw [mem_empty_iff_false] at hx
      exact hx.elim

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (StructureGroupoid H)
  body: ⟨idGroupoid H⟩

中文:
实例 :
  签名: Inhabited (StructureGroupoid H)
  定义体: ⟨idGroupoid H⟩

Depends on / 依赖: idGroupoid
-/
instance : Inhabited (StructureGroupoid H) := ⟨idGroupoid H⟩

/--
Definition of `Pregroupoid` / `Pregroupoid` 的定义

English:
structure Pregroupoid
  parameters: (H : Type*) [TopologicalSpace H]
  axioms and operations (5):
    - property : (H -> H) -> Set H -> Prop
    - comp : forall {f g u v}, property f u -> property g v -> IsOpen u -> IsOpen v -> IsOpen (u inter f ⁻¹' v) -> property (g ∘ f) (u inter f ⁻¹' v)
    - id_mem : property id univ
    - locality : forall {f u}, IsOpen u -> (forall x in u, exists v, IsOpen v ∧ x in v ∧ property f (u inter v)) -> property f u
    - congr : forall {f g : H -> H} {u}, IsOpen u -> (forall x in u, g x = f x) -> property f u -> property g u

中文:
结构 Pregroupoid
  参数: (H : 类型) [TopologicalSpace H]
  公理与运算 (5 个):
    - property : (H -> H) -> Set H -> 命题
    - comp : 对任意 {f g u v}, property f u -> property g v -> IsOpen u -> IsOpen v -> IsOpen (u inter f ⁻¹' v) -> property (g ∘ f) (u inter f ⁻¹' v)
    - id_mem : property id univ
    - locality : 对任意 {f u}, IsOpen u -> (对任意 x in u, 存在 v, IsOpen v ∧ x in v ∧ property f (u inter v)) -> property f u
    - congr : 对任意 {f g : H -> H} {u}, IsOpen u -> (对任意 x in u, g x = f x) -> property f u -> property g u
-/
structure Pregroupoid (H : Type*) [TopologicalSpace H] where
  /-- Property describing membership in this groupoid: the pregroupoid "contains"
  all functions `H → H` having the pregroupoid property on some `s : Set H` -/
  property : (H -> H) -> Set H -> Prop
  /-- The pregroupoid property is stable under composition -/
  comp : forall {f g u v}, property f u -> property g v ->
    IsOpen u -> IsOpen v -> IsOpen (u inter f ⁻¹' v) -> property (g ∘ f) (u inter f ⁻¹' v)
  /-- Pregroupoids contain the identity map (on `univ`) -/
  id_mem : property id univ
  /-- The pregroupoid property is "local", in the sense that `f` has the pregroupoid property on `u`
  iff its restriction to each open subset of `u` has it -/
  locality :
    forall {f u}, IsOpen u -> (forall x in u, exists v, IsOpen v ∧ x in v ∧ property f (u inter v)) -> property f u
  /-- If `f = g` on `u` and `property f u`, then `property g u` -/
  congr : forall {f g : H -> H} {u}, IsOpen u -> (forall x in u, g x = f x) -> property f u -> property g u

/--
Definition of `Pregroupoid.groupoid` / `Pregroupoid.groupoid` 的定义

English:
definition Pregroupoid.groupoid
  signature: (PG : Pregroupoid H)
  body: { e : OpenPartialHomeomorph H H | PG.property e e.source ∧ PG.property e.symm e.target }
  trans' e e' he he' := by
    constructor
    · apply PG.comp he.1 he'.1 e.open_source e'.open_source
      apply e.continuousOn_toFun.isOpen_inter_preimage e.open_source e'.open_source
    · apply PG.comp he'.

中文:
定义 Pregroupoid.groupoid
  签名: (PG : Pregroupoid H)
  定义体: { e : OpenPartialHomeomorph H H | PG.property e e.source ∧ PG.property e.symm e.target }
  trans' e e' he he' := by
    constructor
    · apply PG.comp he.1 he'.1 e.open_source e'.open_source
      apply e.continuousOn_toFun.isOpen_inter_preimage e.open_source e'.open_source
    · apply PG.comp he'.

Depends on / 依赖: OpenPartialHomeomorph, PG.comp, PG.id_mem, PG.property, continuousOn_invFun, continuousOn_invFun.isOpen_inter_preimage, continuousOn_toFun, e.continuousOn_toFun.isOpen_inter_preimage, e.open_source, e.open_target, e.source, e.symm, e.target, id_mem, isOpen_inter_preimage, locality, open_source, open_target, property, source
-/
def Pregroupoid.groupoid (PG : Pregroupoid H) : StructureGroupoid H where
  members :=
    { e : OpenPartialHomeomorph H H | PG.property e e.source ∧ PG.property e.symm e.target }
  trans' e e' he he' := by
    constructor
    · apply PG.comp he.1 he'.1 e.open_source e'.open_source
      apply e.continuousOn_toFun.isOpen_inter_preimage e.open_source e'.open_source
    · apply PG.comp he'.2 he.2 e'.open_target e.open_target
      apply e'.continuousOn_invFun.isOpen_inter_preimage e'.open_target e.open_target
  symm' _ he := ⟨he.2, he.1⟩
  id_mem' := ⟨PG.id_mem, PG.id_mem⟩
  locality' e he := by
    constructor
    · refine PG.locality e.open_source fun x xu => ?_
      rcases he x xu with ⟨s, s_open, xs, hs⟩
      refine ⟨s, s_open, xs, ?_⟩
      convert! hs.1 using 1
      dsimp [OpenPartialHomeomorph.restr]
      rw [s_open.interior_eq]
    · refine PG.locality e.open_target fun x xu => ?_
      rcases he (e.symm x) (e.map_target xu) with ⟨s, s_open, xs, hs⟩
      refine ⟨e.target inter e.symm ⁻¹' s, ?_, ⟨xu, xs⟩, ?_⟩
      · exact ContinuousOn.isOpen_inter_preimage e.continuousOn_invFun e.open_target s_open
      · rw [← inter_assoc, inter_self]
        convert! hs.2 using 1
        dsimp [OpenPartialHomeomorph.restr]
        rw [s_open.interior_eq]
  mem_of_eqOnSource' e e' he ee' := by
    constructor
    · apply PG.congr e'.open_source ee'.2
      simp only [ee'.1, he.1]
    · have A := EqOnSource.symm' ee'
      apply PG.congr e'.symm.open_source A.2
      convert! he.2 using 1
      rw [A.1]; rw [symm_toPartialEquiv]; rw [PartialEquiv.symm_source]

/--
theorem `mem_groupoid_of_pregroupoid` / 定理 `mem_groupoid_of_pregroupoid`

English:
theorem mem_groupoid_of_pregroupoid
  given: {PG : Pregroupoid H} {e : OpenPartialHomeomorph H H}
  proof: Iff.rfl

中文:
定理 mem_groupoid_of_pregroupoid
  条件: {PG : Pregroupoid H} {e : OpenPartialHomeomorph H H}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_groupoid_of_pregroupoid {PG : Pregroupoid H} {e : OpenPartialHomeomorph H H} :
    e in PG.groupoid ↔ PG.property e e.source ∧ PG.property e.symm e.target :=
  Iff.rfl

/--
theorem `groupoid_of_pregroupoid_le` / 定理 `groupoid_of_pregroupoid_le`

English:
theorem groupoid_of_pregroupoid_le
  statement: (PG₁ PG₂ : Pregroupoid H)
  proof: by
  refine StructureGroupoid.le_iff.2 fun e he => ?_
  rw [mem_groupoid_of_pregroupoid] at he ⊢
  exact ⟨h _ _ he.1, h _ _ he.2⟩

中文:
定理 groupoid_of_pregroupoid_le
  结论: (PG₁ PG₂ : Pregroupoid H)
  证明: by
  refine StructureGroupoid.le_iff.2 fun e he => ?_
  rw [mem_groupoid_of_pregroupoid] at he ⊢
  exact ⟨h _ _ he.1, h _ _ he.2⟩

Depends on / 依赖: Fintype, Fintype.linearIndependent_iff, LinearMap, LinearMap.ker_eq_bot, StructureGroupoid, StructureGroupoid.le_iff, funext_iff, ker_eq_bot, le_iff, linearIndependent_iff, mem_groupoid_of_pregroupoid
-/
theorem groupoid_of_pregroupoid_le (PG₁ PG₂ : Pregroupoid H)
    (h : forall f s, PG₁.property f s -> PG₂.property f s) : PG₁.groupoid <= PG₂.groupoid := by
  refine StructureGroupoid.le_iff.2 fun e he => ?_
  rw [mem_groupoid_of_pregroupoid] at he ⊢
  exact ⟨h _ _ he.1, h _ _ he.2⟩

/--
theorem `mem_pregroupoid_of_eqOnSource` / 定理 `mem_pregroupoid_of_eqOnSource`

English:
theorem mem_pregroupoid_of_eqOnSource
  statement: (PG : Pregroupoid H) {e e' : OpenPartialHomeomorph H H}
  proof: by
  rw [← he'.1]
  exact PG.congr e.open_source he'.eqOn.symm he

中文:
定理 mem_pregroupoid_of_eqOnSource
  结论: (PG : Pregroupoid H) {e e' : OpenPartialHomeomorph H H}
  证明: by
  rw [← he'.1]
  exact PG.congr e.open_source he'.eqOn.symm he

Depends on / 依赖: PG.congr, e.open_source, eqOn.symm, open_source
-/
theorem mem_pregroupoid_of_eqOnSource (PG : Pregroupoid H) {e e' : OpenPartialHomeomorph H H}
    (he' : e ≈ e') (he : PG.property e e.source) : PG.property e' e'.source := by
  rw [← he'.1]
  exact PG.congr e.open_source he'.eqOn.symm he

/--
Definition of `continuousPregroupoid` / `continuousPregroupoid` 的定义

English:
abbreviation continuousPregroupoid
  signature: (H : Type*) [TopologicalSpace H]
  body: True
  comp _ _ _ _ _ := trivial
  id_mem := trivial
  locality _ _ := trivial
  congr _ _ _ := trivial

中文:
缩写 continuousPregroupoid
  签名: (H : 类型) [TopologicalSpace H]
  定义体: True
  comp _ _ _ _ _ := trivial
  id_mem := trivial
  locality _ _ := trivial
  congr _ _ _ := trivial
-/
abbrev continuousPregroupoid (H : Type*) [TopologicalSpace H] : Pregroupoid H where
  property _ _ := True
  comp _ _ _ _ _ := trivial
  id_mem := trivial
  locality _ _ := trivial
  congr _ _ _ := trivial

instance (H : Type*) [TopologicalSpace H] : Inhabited (Pregroupoid H) :=
  ⟨continuousPregroupoid H⟩

/--
Definition of `continuousGroupoid` / `continuousGroupoid` 的定义

English:
definition continuousGroupoid
  signature: (H : Type*) [TopologicalSpace H]
  body: Pregroupoid.groupoid (continuousPregroupoid H)

中文:
定义 continuousGroupoid
  签名: (H : 类型) [TopologicalSpace H]
  定义体: Pregroupoid.groupoid (continuousPregroupoid H)

Depends on / 依赖: Pregroupoid, Pregroupoid.groupoid, continuousPregroupoid, groupoid
-/
def continuousGroupoid (H : Type*) [TopologicalSpace H] : StructureGroupoid H :=
  Pregroupoid.groupoid (continuousPregroupoid H)

/--
Instance `instStructureGroupoidOrderTop` / 实例 `instStructureGroupoidOrderTop`

English:
instance instStructureGroupoidOrderTop
  signature: : OrderTop (StructureGroupoid H) where
  body: continuousGroupoid H
  le_top _ _ _ := ⟨trivial, trivial⟩

中文:
实例 instStructureGroupoidOrderTop
  签名: : OrderTop (StructureGroupoid H) where
  定义体: continuousGroupoid H
  le_top _ _ _ := ⟨trivial, trivial⟩

Depends on / 依赖: continuousGroupoid
-/
instance instStructureGroupoidOrderTop : OrderTop (StructureGroupoid H) where
  top := continuousGroupoid H
  le_top _ _ _ := ⟨trivial, trivial⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (StructureGroupoid H)
  body: { completeLatticeOfInf _ (by
      exact fun s =>
      ⟨fun S Ss F hF => mem_iInter₂.mp hF S Ss,
      fun T Tl F fT => mem_iInter₂.mpr (fun i his => Tl his fT)⟩) with
    le := (· <= ·)
    lt := (· < ·)
    bot := instStructureGroupoidOrderBot.bot
    bot_le := instStructureGroupoidOrderBot.bot_l

中文:
实例 :
  签名: CompleteLattice (StructureGroupoid H)
  定义体: { completeLatticeOfInf _ (by
      exact fun s =>
      ⟨fun S Ss F hF => mem_iInter₂.mp hF S Ss,
      fun T Tl F fT => mem_iInter₂.mpr (fun i his => Tl his fT)⟩) with
    le := (· <= ·)
    lt := (· < ·)
    bot := instStructureGroupoidOrderBot.bot
    bot_le := instStructureGroupoidOrderBot.bot_l

Depends on / 依赖: And.left, And.right, bot_le, completeLatticeOfInf, inf_le_left, inf_le_right, instStructureGroupoidOrderBot, instStructureGroupoidOrderBot.bot, instStructureGroupoidOrderBot.bot_le, instStructureGroupoidOrderTop, instStructureGroupoidOrderTop.le_top, instStructureGroupoidOrderTop.top, le_inf, le_top
-/
instance : CompleteLattice (StructureGroupoid H) :=
  { completeLatticeOfInf _ (by
      exact fun s =>
      ⟨fun S Ss F hF => mem_iInter₂.mp hF S Ss,
      fun T Tl F fT => mem_iInter₂.mpr (fun i his => Tl his fT)⟩) with
    le := (· <= ·)
    lt := (· < ·)
    bot := instStructureGroupoidOrderBot.bot
    bot_le := instStructureGroupoidOrderBot.bot_le
    top := instStructureGroupoidOrderTop.top
    le_top := instStructureGroupoidOrderTop.le_top
    inf := (· ⊓ ·)
    le_inf := fun _ _ _ h₁₂ h₁₃ _ hm => ⟨h₁₂ hm, h₁₃ hm⟩
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right }

/--
Definition of `ClosedUnderRestriction` / `ClosedUnderRestriction` 的定义

English:
class ClosedUnderRestriction
  parameters: (G : StructureGroupoid H)
  axioms and operations (1):
    - closedUnderRestriction : forall {e : OpenPartialHomeomorph H H}, e in G -> forall s : Set H, IsOpen s -> e.restr s in G

中文:
类 ClosedUnderRestriction
  参数: (G : StructureGroupoid H)
  公理与运算 (1 个):
    - closedUnderRestriction : 对任意 {e : OpenPartialHomeomorph H H}, e in G -> 对任意 s : Set H, IsOpen s -> e.restr s in G
-/
class ClosedUnderRestriction (G : StructureGroupoid H) : Prop where
  closedUnderRestriction :
    forall {e : OpenPartialHomeomorph H H}, e in G -> forall s : Set H, IsOpen s -> e.restr s in G

/--
theorem `closedUnderRestriction'` / 定理 `closedUnderRestriction'`

English:
theorem closedUnderRestriction'
  statement: {G : StructureGroupoid H} [ClosedUnderRestriction G]
  proof: ClosedUnderRestriction.closedUnderRestriction he s hs

中文:
定理 closedUnderRestriction'
  结论: {G : StructureGroupoid H} [ClosedUnderRestriction G]
  证明: ClosedUnderRestriction.closedUnderRestriction he s hs

Depends on / 依赖: ClosedUnderRestriction, ClosedUnderRestriction.closedUnderRestriction, closedUnderRestriction
-/
theorem closedUnderRestriction' {G : StructureGroupoid H} [ClosedUnderRestriction G]
    {e : OpenPartialHomeomorph H H} (he : e in G) {s : Set H} (hs : IsOpen s) : e.restr s in G :=
  ClosedUnderRestriction.closedUnderRestriction he s hs

/--
lemma `StructureGroupoid.restr_mem_of_eqOn` / 引理 `StructureGroupoid.restr_mem_of_eqOn`

English:
lemma StructureGroupoid.restr_mem_of_eqOn
  statement: {G : StructureGroupoid H} [ClosedUnderRestriction G]
  proof: G.mem_of_eqOnSource (closedUnderRestriction' he (e'.open_source.inter hs))
    (Setoid.symm (restr_eqOnSource_of_eqOn' hs heq hsub))

中文:
引理 StructureGroupoid.restr_mem_of_eqOn
  结论: {G : StructureGroupoid H} [ClosedUnderRestriction G]
  证明: G.mem_of_eqOnSource (closedUnderRestriction' he (e'.open_source.inter hs))
    (Setoid.symm (restr_eqOnSource_of_eqOn' hs heq hsub))

Depends on / 依赖: G.mem_of_eqOnSource, Setoid, Setoid.symm, closedUnderRestriction, mem_of_eqOnSource, open_source, open_source.inter, restr_eqOnSource_of_eqOn
-/
lemma StructureGroupoid.restr_mem_of_eqOn {G : StructureGroupoid H} [ClosedUnderRestriction G]
    {e e' : OpenPartialHomeomorph H H} (he : e in G) {s : Set H} (hs : IsOpen s)
    (heq : EqOn e e' s) (hsub : e'.source inter s subseteq e.source) : e'.restr s in G :=
  G.mem_of_eqOnSource (closedUnderRestriction' he (e'.open_source.inter hs))
    (Setoid.symm (restr_eqOnSource_of_eqOn' hs heq hsub))

/--
Definition of `idRestrGroupoid` / `idRestrGroupoid` 的定义

English:
definition idRestrGroupoid
  signature: : StructureGroupoid H where
  body: { e | exists (s : Set H) (h : IsOpen s), e ≈ OpenPartialHomeomorph.ofSet s h }
  trans' := by
    rintro e e' ⟨s, hs, hse⟩ ⟨s', hs', hse'⟩
    refine ⟨s inter s', hs.inter hs', ?_⟩
    have := OpenPartialHomeomorph.EqOnSource.trans' hse hse'
    rwa [OpenPartialHomeomorph.ofSet_trans_ofSet] at this


中文:
定义 idRestrGroupoid
  签名: : StructureGroupoid H where
  定义体: { e | exists (s : Set H) (h : IsOpen s), e ≈ OpenPartialHomeomorph.ofSet s h }
  trans' := by
    rintro e e' ⟨s, hs, hse⟩ ⟨s', hs', hse'⟩
    refine ⟨s inter s', hs.inter hs', ?_⟩
    have := OpenPartialHomeomorph.EqOnSource.trans' hse hse'
    rwa [OpenPartialHomeomorph.ofSet_trans_ofSet] at this


Depends on / 依赖: IsOpen, OpenPartialHomeomorph, OpenPartialHomeomorph.ofSet
-/
def idRestrGroupoid : StructureGroupoid H where
  members := { e | exists (s : Set H) (h : IsOpen s), e ≈ OpenPartialHomeomorph.ofSet s h }
  trans' := by
    rintro e e' ⟨s, hs, hse⟩ ⟨s', hs', hse'⟩
    refine ⟨s inter s', hs.inter hs', ?_⟩
    have := OpenPartialHomeomorph.EqOnSource.trans' hse hse'
    rwa [OpenPartialHomeomorph.ofSet_trans_ofSet] at this
  symm' := by
    rintro e ⟨s, hs, hse⟩
    refine ⟨s, hs, ?_⟩
    rw [← ofSet_symm]
    exact OpenPartialHomeomorph.EqOnSource.symm' hse
  id_mem' := ⟨univ, isOpen_univ, by simp only [mfld_simps, refl]⟩
  locality' := by
    intro e h
    refine ⟨e.source, e.open_source, by simp only [mfld_simps], ?_⟩
    intro x hx
    rcases h x hx with ⟨s, hs, hxs, s', hs', hes'⟩
    have hes : x in (e.restr s).source := by
      rw [e.restr_source]
      refine ⟨hx, ?_⟩
      rw [hs.interior_eq]
      exact hxs
    simpa only [mfld_simps] using OpenPartialHomeomorph.EqOnSource.eqOn hes' hes
  mem_of_eqOnSource' := by
    rintro e e' ⟨s, hs, hse⟩ hee'
    exact ⟨s, hs, Setoid.trans hee' hse⟩

/--
theorem `idRestrGroupoid_mem` / 定理 `idRestrGroupoid_mem`

English:
theorem idRestrGroupoid_mem
  given: {s : Set H} (hs : IsOpen s)
  statement: ofSet s hs in @idRestrGroupoid H _
  proof: ⟨s, hs, refl _⟩

中文:
定理 idRestrGroupoid_mem
  条件: {s : Set H} (hs : IsOpen s)
  结论: ofSet s hs in @idRestrGroupoid H _
  证明: ⟨s, hs, refl _⟩
-/
theorem idRestrGroupoid_mem {s : Set H} (hs : IsOpen s) : ofSet s hs in @idRestrGroupoid H _ :=
  ⟨s, hs, refl _⟩

/--
Instance `closedUnderRestriction_idRestrGroupoid` / 实例 `closedUnderRestriction_idRestrGroupoid`

English:
instance closedUnderRestriction_idRestrGroupoid
  signature: : ClosedUnderRestriction (@idRestrGroupoid H _)
  body: ⟨by
    rintro e ⟨s', hs', he⟩ s hs
    use s' inter s, hs'.inter hs
    refine Setoid.trans (OpenPartialHomeomorph.EqOnSource.restr he s) ?_
    exact ⟨by simp only [hs.interior_eq, mfld_simps], by simp only [mfld_simps, eqOn_refl]⟩⟩

中文:
实例 closedUnderRestriction_idRestrGroupoid
  签名: : ClosedUnderRestriction (@idRestrGroupoid H _)
  定义体: ⟨by
    rintro e ⟨s', hs', he⟩ s hs
    use s' inter s, hs'.inter hs
    refine Setoid.trans (OpenPartialHomeomorph.EqOnSource.restr he s) ?_
    exact ⟨by simp only [hs.interior_eq, mfld_simps], by simp only [mfld_simps, eqOn_refl]⟩⟩

Depends on / 依赖: EqOnSource, OpenPartialHomeomorph, OpenPartialHomeomorph.EqOnSource.restr, Setoid, Setoid.trans, eqOn_refl, hs.interior_eq, interior_eq, mfld_simps
-/
instance closedUnderRestriction_idRestrGroupoid : ClosedUnderRestriction (@idRestrGroupoid H _) :=
  ⟨by
    rintro e ⟨s', hs', he⟩ s hs
    use s' inter s, hs'.inter hs
    refine Setoid.trans (OpenPartialHomeomorph.EqOnSource.restr he s) ?_
    exact ⟨by simp only [hs.interior_eq, mfld_simps], by simp only [mfld_simps, eqOn_refl]⟩⟩

/--
theorem `closedUnderRestriction_iff_id_le` / 定理 `closedUnderRestriction_iff_id_le`

English:
theorem closedUnderRestriction_iff_id_le
  given: (G : StructureGroupoid H)
  proof: by
  constructor
  · intro _i
    rw [StructureGroupoid.le_iff]
    rintro e ⟨s, hs, hes⟩
    refine G.mem_of_eqOnSource ?_ hes
    convert! closedUnderRestriction' G.id_mem hs
    ext <;> simp [hs.interior_eq]
  · intro h
    constructor
    intro e he s hs
    rw [← ofSet_trans (e : OpenPartialHom

中文:
定理 closedUnderRestriction_iff_id_le
  条件: (G : StructureGroupoid H)
  证明: by
  constructor
  · intro _i
    rw [StructureGroupoid.le_iff]
    rintro e ⟨s, hs, hes⟩
    refine G.mem_of_eqOnSource ?_ hes
    convert! closedUnderRestriction' G.id_mem hs
    ext <;> simp [hs.interior_eq]
  · intro h
    constructor
    intro e he s hs
    rw [← ofSet_trans (e : OpenPartialHom

Depends on / 依赖: G.id_mem, G.mem_of_eqOnSource, G.trans, OpenPartialHomeomorph, StructureGroupoid, StructureGroupoid.le_iff, StructureGroupoid.le_iff.mp, closedUnderRestriction, convert, hs.interior_eq, idRestrGroupoid_mem, id_mem, interior_eq, le_iff, mem_of_eqOnSource, ofSet_trans
-/
theorem closedUnderRestriction_iff_id_le (G : StructureGroupoid H) :
    ClosedUnderRestriction G ↔ idRestrGroupoid <= G := by
  constructor
  · intro _i
    rw [StructureGroupoid.le_iff]
    rintro e ⟨s, hs, hes⟩
    refine G.mem_of_eqOnSource ?_ hes
    convert! closedUnderRestriction' G.id_mem hs
    ext <;> simp [hs.interior_eq]
  · intro h
    constructor
    intro e he s hs
    rw [← ofSet_trans (e : OpenPartialHomeomorph H H) hs]
    refine G.trans ?_ he
    apply StructureGroupoid.le_iff.mp h
    exact idRestrGroupoid_mem hs

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ClosedUnderRestriction (continuousGroupoid H)
  body: (closedUnderRestriction_iff_id_le _).mpr le_top

中文:
实例 :
  签名: ClosedUnderRestriction (continuousGroupoid H)
  定义体: (closedUnderRestriction_iff_id_le _).mpr le_top

Depends on / 依赖: closedUnderRestriction_iff_id_le, le_top
-/
instance : ClosedUnderRestriction (continuousGroupoid H) :=
  (closedUnderRestriction_iff_id_le _).mpr le_top

end Groupoid
