/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Gabin Kolly
-/
module

public import Mathlib.ModelTheory.FinitelyGenerated
public import Mathlib.ModelTheory.PartialEquiv
public import Mathlib.ModelTheory.Bundled
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Fraïssé Classes and Fraïssé Limits

This file pertains to the ages of countable first-order structures. The age of a structure is the
class of all finitely-generated structures that embed into it.

Of particular interest are Fraïssé classes, which are exactly the ages of countable
ultrahomogeneous structures. To each is associated a unique (up to nonunique isomorphism)
Fraïssé limit - the countable ultrahomogeneous structure with that age.

## Main Definitions

- `FirstOrder.Language.age` is the class of finitely-generated structures that embed into a
  particular structure.
- A class `K` is `FirstOrder.Language.Hereditary` when all finitely-generated
  structures that embed into structures in `K` are also in `K`.
- A class `K` has `FirstOrder.Language.JointEmbedding` when for every `M`, `N` in
  `K`, there is another structure in `K` into which both `M` and `N` embed.
- A class `K` has `FirstOrder.Language.Amalgamation` when for any pair of embeddings
  of a structure `M` in `K` into other structures in `K`, those two structures can be embedded into
  a fourth structure in `K` such that the resulting square of embeddings commutes.
- `FirstOrder.Language.IsFraisse` indicates that a class is nonempty, essentially countable,
  and satisfies the hereditary, joint embedding, and amalgamation properties.
- `FirstOrder.Language.IsFraisseLimit` indicates that a structure is a Fraïssé limit for a given
  class.

## Main Results

- We show that the age of any structure is isomorphism-invariant and satisfies the hereditary and
  joint-embedding properties.
- `FirstOrder.Language.age.countable_quotient` shows that the age of any countable structure is
  essentially countable.
- `FirstOrder.Language.exists_countable_is_age_of_iff` gives necessary and sufficient conditions
  for a class to be the age of a countable structure in a language with countably many functions.
- `FirstOrder.Language.IsFraisseLimit.nonempty_equiv` shows that any class which is Fraïssé has
  at most one Fraïssé limit up to equivalence.
- `FirstOrder.Language.empty.isFraisseLimit_of_countable_infinite` shows that any countably infinite
  structure in the empty language is a Fraïssé limit of the class of finite structures.
- `FirstOrder.Language.empty.isFraisse_finite` shows that the class of finite structures in the
  empty language is Fraïssé.

## Implementation Notes

- Classes of structures are formalized with `Set (Bundled L.Structure)`.
- Some results pertain to countable limit structures, others to countably-generated limit
  structures. In the case of a language with countably many function symbols, these are equivalent.

## References

- [W. Hodges, *A Shorter Model Theory*][Hodges97]
- [K. Tent, M. Ziegler, *A Course in Model Theory*][Tent_Ziegler]

## TODO

- Show existence of Fraïssé limits

-/

@[expose] public section


universe u v w w'

open scoped FirstOrder

open Set CategoryTheory

namespace FirstOrder

namespace Language

open Structure Substructure

variable (L : Language.{u, v})

/-! ### The Age of a Structure and Fraïssé Classes -/


/--
Definition of `age` / `age` 的定义

English:
definition age
  signature: (M : Type w) [L.Structure M]
  body: {N | Structure.FG L N ∧ Nonempty (N ↪[L] M)}

中文:
定义 age
  签名: (M : 类型 w) [L.结构 M]
  定义体: {N | Structure.FG L N ∧ Nonempty (N ↪[L] M)}

Depends on / 依赖: Nonempty, Structure, Structure.FG
-/
def age (M : Type w) [L.Structure M] : Set (Bundled.{w} L.Structure) :=
  {N | Structure.FG L N ∧ Nonempty (N ↪[L] M)}

variable {L}
variable (K : Set (Bundled.{w} L.Structure))

/--
Definition of `Hereditary` / `Hereditary` 的定义

English:
definition Hereditary
  signature: : Prop
  body: forall M : Bundled.{w} L.Structure, M in K -> L.age M subseteq K

中文:
定义 Hereditary
  签名: : 命题
  定义体: forall M : Bundled.{w} L.Structure, M in K -> L.age M subseteq K

Depends on / 依赖: Bundled, L.Structure, L.age, Structure, subseteq
-/
def Hereditary : Prop :=
  forall M : Bundled.{w} L.Structure, M in K -> L.age M subseteq K

/--
Definition of `JointEmbedding` / `JointEmbedding` 的定义

English:
definition JointEmbedding
  signature: : Prop
  body: DirectedOn (fun M N : Bundled.{w} L.Structure => Nonempty (M ↪[L] N)) K

中文:
定义 JointEmbedding
  签名: : 命题
  定义体: DirectedOn (fun M N : Bundled.{w} L.Structure => Nonempty (M ↪[L] N)) K

Depends on / 依赖: Bundled, DirectedOn, L.Structure, Nonempty, Structure
-/
def JointEmbedding : Prop :=
  DirectedOn (fun M N : Bundled.{w} L.Structure => Nonempty (M ↪[L] N)) K

/--
Definition of `Amalgamation` / `Amalgamation` 的定义

English:
definition Amalgamation
  signature: : Prop
  body: forall (M N P : Bundled.{w} L.Structure) (MN : M ↪[L] N) (MP : M ↪[L] P),
    M in K -> N in K -> P in K -> exists (Q : Bundled.{w} L.Structure) (NQ : N ↪[L] Q) (PQ : P ↪[L] Q),
      Q in K ∧ NQ.comp MN = PQ.comp MP

中文:
定义 Amalgamation
  签名: : 命题
  定义体: forall (M N P : Bundled.{w} L.Structure) (MN : M ↪[L] N) (MP : M ↪[L] P),
    M in K -> N in K -> P in K -> exists (Q : Bundled.{w} L.Structure) (NQ : N ↪[L] Q) (PQ : P ↪[L] Q),
      Q in K ∧ NQ.comp MN = PQ.comp MP

Depends on / 依赖: Bundled, L.Structure, NQ.comp, PQ.comp, Structure
-/
def Amalgamation : Prop :=
  forall (M N P : Bundled.{w} L.Structure) (MN : M ↪[L] N) (MP : M ↪[L] P),
    M in K -> N in K -> P in K -> exists (Q : Bundled.{w} L.Structure) (NQ : N ↪[L] Q) (PQ : P ↪[L] Q),
      Q in K ∧ NQ.comp MN = PQ.comp MP

/--
Definition of `IsFraisse` / `IsFraisse` 的定义

English:
class IsFraisse
  parameters: : Prop where
  axioms and operations (6):
    - is_nonempty : K.Nonempty
    - FG : forall M : Bundled.{w} L.Structure, M in K -> Structure.FG L M
    - is_essentially_countable : (Quotient.mk' '' K).Countable
    - hereditary : Hereditary K
    - jointEmbedding : JointEmbedding K
    - amalgamation : Amalgamation K

中文:
类 是Fraisse
  参数: : 命题 where
  公理与运算 (6 个):
    - is_nonempty : K.非空
    - FG : 对任意 M : 打包.{w} L.结构, M in K -> 结构.FG L M
    - is_essentially_countable : (商.mk' '' K).可数
    - hereditary : Hereditary K
    - jointEmbedding : JointEmbedding K
    - amalgamation : Amalgamation K
-/
class IsFraisse : Prop where
  is_nonempty : K.Nonempty
  FG : forall M : Bundled.{w} L.Structure, M in K -> Structure.FG L M
  is_essentially_countable : (Quotient.mk' '' K).Countable
  hereditary : Hereditary K
  jointEmbedding : JointEmbedding K
  amalgamation : Amalgamation K

variable {K} (L) (M : Type w) [Structure L M]

/--
theorem `age.is_equiv_invariant` / 定理 `age.is_equiv_invariant`

English:
theorem age.is_equiv_invariant
  given: (N P : Bundled.{w} L.Structure) (h : Nonempty (N ≃[L] P))
  proof: and_congr h.some.fg_iff
    ⟨Nonempty.map fun x => Embedding.comp x h.some.symm.toEmbedding,
      Nonempty.map fun x => Embedding.comp x h.some.toEmbedding⟩

中文:
定理 age.is_equiv_invariant
  条件: (N P : 打包.{w} L.结构) (h : 非空 (N ≃[L] P))
  证明: and_congr h.some.fg_iff
    ⟨Nonempty.map fun x => Embedding.comp x h.some.symm.toEmbedding,
      Nonempty.map fun x => Embedding.comp x h.some.toEmbedding⟩

Depends on / 依赖: Embedding, Embedding.comp, Nonempty, Nonempty.map, and_congr, fg_iff, h.some.fg_iff, h.some.symm.toEmbedding, h.some.toEmbedding, toEmbedding
-/
theorem age.is_equiv_invariant (N P : Bundled.{w} L.Structure) (h : Nonempty (N ≃[L] P)) :
    N in L.age M ↔ P in L.age M :=
  and_congr h.some.fg_iff
    ⟨Nonempty.map fun x => Embedding.comp x h.some.symm.toEmbedding,
      Nonempty.map fun x => Embedding.comp x h.some.toEmbedding⟩

variable {L} {M} {N : Type w} [Structure L N]

/--
theorem `Embedding.age_subset_age` / 定理 `Embedding.age_subset_age`

English:
theorem Embedding.age_subset_age
  given: (MN : M ↪[L] N)
  statement: L.age M subseteq L.age N
  proof: fun _ =>
  And.imp_right (Nonempty.map MN.comp)

中文:
定理 嵌入.age_subset_age
  条件: (MN : M ↪[L] N)
  结论: L.age M subseteq L.age N
  证明: fun _ =>
  And.imp_right (Nonempty.map MN.comp)
-/
theorem Embedding.age_subset_age (MN : M ↪[L] N) : L.age M subseteq L.age N := fun _ =>
  And.imp_right (Nonempty.map MN.comp)

/--
theorem `Equiv.age_eq_age` / 定理 `Equiv.age_eq_age`

English:
theorem Equiv.age_eq_age
  given: (MN : M ≃[L] N)
  statement: L.age M = L.age N
  proof: le_antisymm MN.toEmbedding.age_subset_age MN.symm.toEmbedding.age_subset_age

中文:
定理 等价.age_eq_age
  条件: (MN : M ≃[L] N)
  结论: L.age M = L.age N
  证明: le_antisymm MN.toEmbedding.age_subset_age MN.symm.toEmbedding.age_subset_age

Depends on / 依赖: MN.symm.toEmbedding.age_subset_age, MN.toEmbedding.age_subset_age, age_subset_age, le_antisymm, toEmbedding
-/
theorem Equiv.age_eq_age (MN : M ≃[L] N) : L.age M = L.age N :=
  le_antisymm MN.toEmbedding.age_subset_age MN.symm.toEmbedding.age_subset_age

/--
theorem `Structure.FG.mem_age_of_equiv` / 定理 `Structure.FG.mem_age_of_equiv`

English:
theorem Structure.FG.mem_age_of_equiv
  statement: {M N : Bundled L.Structure} (h : Structure.FG L M)
  proof: ⟨MN.some.fg_iff.1 h, ⟨MN.some.symm.toEmbedding⟩⟩

中文:
定理 结构.FG.mem_age_of_equiv
  结论: {M N : 打包 L.结构} (h : 结构.FG L M)
  证明: ⟨MN.some.fg_iff.1 h, ⟨MN.some.symm.toEmbedding⟩⟩

Depends on / 依赖: MN.some.fg_iff, MN.some.symm.toEmbedding, fg_iff, toEmbedding
-/
theorem Structure.FG.mem_age_of_equiv {M N : Bundled L.Structure} (h : Structure.FG L M)
    (MN : Nonempty (M ≃[L] N)) : N in L.age M :=
  ⟨MN.some.fg_iff.1 h, ⟨MN.some.symm.toEmbedding⟩⟩

/--
theorem `Hereditary.is_equiv_invariant_of_fg` / 定理 `Hereditary.is_equiv_invariant_of_fg`

English:
theorem Hereditary.is_equiv_invariant_of_fg
  statement: (h : Hereditary K)
  proof: ⟨fun MK => h M MK ((fg M MK).mem_age_of_equiv hn),
   fun NK => h N NK ((fg N NK).mem_age_of_equiv ⟨hn.some.symm⟩)⟩

中文:
定理 Hereditary.is_equiv_invariant_of_fg
  结论: (h : Hereditary K)
  证明: ⟨fun MK => h M MK ((fg M MK).mem_age_of_equiv hn),
   fun NK => h N NK ((fg N NK).mem_age_of_equiv ⟨hn.some.symm⟩)⟩

Depends on / 依赖: hn.some.symm, mem_age_of_equiv
-/
theorem Hereditary.is_equiv_invariant_of_fg (h : Hereditary K)
    (fg : forall M : Bundled.{w} L.Structure, M in K -> Structure.FG L M) (M N : Bundled.{w} L.Structure)
    (hn : Nonempty (M ≃[L] N)) : M in K ↔ N in K :=
  ⟨fun MK => h M MK ((fg M MK).mem_age_of_equiv hn),
   fun NK => h N NK ((fg N NK).mem_age_of_equiv ⟨hn.some.symm⟩)⟩

/--
theorem `IsFraisse.is_equiv_invariant` / 定理 `IsFraisse.is_equiv_invariant`

English:
theorem IsFraisse.is_equiv_invariant
  statement: [h : IsFraisse K] {M N : Bundled.{w} L.Structure}
  proof: h.hereditary.is_equiv_invariant_of_fg h.FG M N hn

中文:
定理 是Fraisse.is_equiv_invariant
  结论: [h : 是Fraisse K] {M N : 打包.{w} L.结构}
  证明: h.hereditary.is_equiv_invariant_of_fg h.FG M N hn

Depends on / 依赖: h.FG, h.hereditary.is_equiv_invariant_of_fg, hereditary, is_equiv_invariant_of_fg
-/
theorem IsFraisse.is_equiv_invariant [h : IsFraisse K] {M N : Bundled.{w} L.Structure}
    (hn : Nonempty (M ≃[L] N)) : M in K ↔ N in K :=
  h.hereditary.is_equiv_invariant_of_fg h.FG M N hn

variable (M)

/--
theorem `age.nonempty` / 定理 `age.nonempty`

English:
theorem age.nonempty
  statement: (L.age M).Nonempty
  proof: ⟨Bundled.of (Substructure.closure L (∅ : Set M)),
    (fg_iff_structure_fg _).1 (fg_closure Set.finite_empty), ⟨Substructure.subtype _⟩⟩

中文:
定理 age.nonempty
  结论: (L.age M).非空
  证明: ⟨Bundled.of (Substructure.closure L (∅ : Set M)),
    (fg_iff_structure_fg _).1 (fg_closure Set.finite_empty), ⟨Substructure.subtype _⟩⟩

Depends on / 依赖: Bundled, Bundled.of, Set.finite_empty, Substructure, Substructure.closure, Substructure.subtype, closure, fg_closure, fg_iff_structure_fg, finite_empty, subtype
-/
theorem age.nonempty : (L.age M).Nonempty :=
  ⟨Bundled.of (Substructure.closure L (∅ : Set M)),
    (fg_iff_structure_fg _).1 (fg_closure Set.finite_empty), ⟨Substructure.subtype _⟩⟩

/--
theorem `age.hereditary` / 定理 `age.hereditary`

English:
theorem age.hereditary
  statement: Hereditary (L.age M)
  proof: fun _ hN _ hP => hN.2.some.age_subset_age hP

中文:
定理 age.hereditary
  结论: Hereditary (L.age M)
  证明: fun _ hN _ hP => hN.2.some.age_subset_age hP

Depends on / 依赖: age_subset_age, some.age_subset_age
-/
theorem age.hereditary : Hereditary (L.age M) := fun _ hN _ hP => hN.2.some.age_subset_age hP

/--
theorem `age.jointEmbedding` / 定理 `age.jointEmbedding`

English:
theorem age.jointEmbedding
  statement: JointEmbedding (L.age M)
  proof: fun _ hN _ hP =>
  ⟨Bundled.of (↥(hN.2.some.toHom.range ⊔ hP.2.some.toHom.range)),
    ⟨(fg_iff_structure_fg _).1 ((hN.1.range hN.2.some.toHom).sup (hP.1.range hP.2.some.toHom)),
      ⟨Substructure.subtype _⟩⟩,
    ⟨Embedding.comp (inclusion le_sup_left) hN.2.some.equivRange.toEmbedding⟩,
    ⟨Embedding.comp (inclusion le_sup_right) hP.2.some.equivRange.toEmbedding⟩⟩

中文:
定理 age.jointEmbedding
  结论: JointEmbedding (L.age M)
  证明: fun _ hN _ hP =>
  ⟨Bundled.of (↥(hN.2.some.toHom.range ⊔ hP.2.some.toHom.range)),
    ⟨(fg_iff_structure_fg _).1 ((hN.1.range hN.2.some.toHom).sup (hP.1.range hP.2.some.toHom)),
      ⟨Substructure.subtype _⟩⟩,
    ⟨Embedding.comp (inclusion le_sup_left) hN.2.some.equivRange.toEmbedding⟩,
    ⟨Embedding.comp (inclusion le_sup_right) hP.2.some.equivRange.toEmbedding⟩⟩
-/
theorem age.jointEmbedding : JointEmbedding (L.age M) := fun _ hN _ hP =>
  ⟨Bundled.of (↥(hN.2.some.toHom.range ⊔ hP.2.some.toHom.range)),
    ⟨(fg_iff_structure_fg _).1 ((hN.1.range hN.2.some.toHom).sup (hP.1.range hP.2.some.toHom)),
      ⟨Substructure.subtype _⟩⟩,
    ⟨Embedding.comp (inclusion le_sup_left) hN.2.some.equivRange.toEmbedding⟩,
    ⟨Embedding.comp (inclusion le_sup_right) hP.2.some.equivRange.toEmbedding⟩⟩

variable {M} in
/--
theorem `age.fg_substructure` / 定理 `age.fg_substructure`

English:
theorem age.fg_substructure
  given: {S : L.Substructure M} (fg : S.FG)
  statement: Bundled.mk S in L.age M
  proof: by
  exact ⟨(Substructure.fg_iff_structure_fg _).1 fg, ⟨subtype _⟩⟩

中文:
定理 age.fg_substructure
  条件: {S : L.子结构 M} (fg : S.FG)
  结论: 打包.mk S in L.age M
  证明: by
  exact ⟨(Substructure.fg_iff_structure_fg _).1 fg, ⟨subtype _⟩⟩

Depends on / 依赖: Substructure, Substructure.fg_iff_structure_fg, fg_iff_structure_fg, subtype
-/
theorem age.fg_substructure {S : L.Substructure M} (fg : S.FG) : Bundled.mk S in L.age M := by
  exact ⟨(Substructure.fg_iff_structure_fg _).1 fg, ⟨subtype _⟩⟩

/--
theorem `age.has_representative_as_substructure` / 定理 `age.has_representative_as_substructure`

English:
theorem age.has_representative_as_substructure
  proof: by
  rintro _ ⟨N, ⟨N_fg, ⟨N_incl⟩⟩, N_eq⟩
  refine N_eq.symm ▸ ⟨⟨N_incl.toHom.range, ?_⟩, Quotient.sound ⟨N_incl.equivRange.symm⟩⟩
  exact FG.range N_fg (Embedding.toHom N_incl)

中文:
定理 age.has_representative_as_substructure
  证明: by
  rintro _ ⟨N, ⟨N_fg, ⟨N_incl⟩⟩, N_eq⟩
  refine N_eq.symm ▸ ⟨⟨N_incl.toHom.range, ?_⟩, Quotient.sound ⟨N_incl.equivRange.symm⟩⟩
  exact FG.range N_fg (Embedding.toHom N_incl)

Depends on / 依赖: Embedding, Embedding.toHom, FG.range, N_eq, N_eq.symm, N_fg, N_incl, N_incl.equivRange.symm, N_incl.toHom.range, Quotient, Quotient.sound, equivRange
-/
theorem age.has_representative_as_substructure :
    forall C in Quotient.mk' '' L.age M, exists V : {V : L.Substructure M // FG V},
      ⟦Bundled.mk V⟧ = C := by
  rintro _ ⟨N, ⟨N_fg, ⟨N_incl⟩⟩, N_eq⟩
  refine N_eq.symm ▸ ⟨⟨N_incl.toHom.range, ?_⟩, Quotient.sound ⟨N_incl.equivRange.symm⟩⟩
  exact FG.range N_fg (Embedding.toHom N_incl)

/--
theorem `age.countable_quotient` / 定理 `age.countable_quotient`

English:
theorem age.countable_quotient
  given: [h : Countable M]
  statement: (Quotient.mk' '' L.age M).Countable
  proof: by
  classical
  refine (congr_arg _ (Set.ext <| Quotient.forall.2 fun N => ?_)).mp
    (countable_range fun s : Finset M => ⟦⟨closure L (s : Set M), inferInstance⟩⟧)
  constructor
  · rintro ⟨s, hs⟩
    use Bundled.of (closure L (s : Set M))
    exact ⟨⟨(fg_iff_structure_fg _).1 (fg_closure s.finite_toSet), ⟨Substructure.subtype _⟩⟩, hs⟩
  · simp only [mem_range, Quotient.eq]
    rintro ⟨P, ⟨⟨s, hs⟩, ⟨PM⟩⟩, hP2⟩
refine ⟨s.image PM, Setoid.trans (b := P) ?_ Quotient.exact hP2⟩
    rw [← Embedding.coe_toHom]; rw [Finset.coe_image]; rw [closure_image PM.toHom]; rw [hs]; rw [← Hom.range_eq_map]
    exact ⟨PM.equivRange.symm⟩

中文:
定理 age.countable_quotient
  条件: [h : 可数 M]
  结论: (商.mk' '' L.age M).可数
  证明: by
  classical
  refine (congr_arg _ (Set.ext <| Quotient.forall.2 fun N => ?_)).mp
    (countable_range fun s : Finset M => ⟦⟨closure L (s : Set M), inferInstance⟩⟧)
  constructor
  · rintro ⟨s, hs⟩
    use Bundled.of (closure L (s : Set M))
    exact ⟨⟨(fg_iff_structure_fg _).1 (fg_closure s.finite_toSet), ⟨Substructure.subtype _⟩⟩, hs⟩
  · simp only [mem_range, Quotient.eq]
    rintro ⟨P, ⟨⟨s, hs⟩, ⟨PM⟩⟩, hP2⟩
refine ⟨s.image PM, Setoid.trans (b := P) ?_ Quotient.exact hP2⟩
    rw [← Embedding.coe_toHom]; rw [Finset.coe_image]; rw [closure_image PM.toHom]; rw [hs]; rw [← Hom.range_eq_map]
    exact ⟨PM.equivRange.symm⟩

Depends on / 依赖: Bundled, Bundled.of, Embedding, Embedding.coe_toHom, Finset, Finset.coe_i, Quotient, Quotient.eq, Quotient.exact, Quotient.forall, Set.ext, Setoid, Setoid.trans, Substructure, Substructure.subtype, classical, closure, coe_i, coe_toHom, congr_arg
-/
theorem age.countable_quotient [h : Countable M] : (Quotient.mk' '' L.age M).Countable := by
  classical
  refine (congr_arg _ (Set.ext <| Quotient.forall.2 fun N => ?_)).mp
    (countable_range fun s : Finset M => ⟦⟨closure L (s : Set M), inferInstance⟩⟧)
  constructor
  · rintro ⟨s, hs⟩
    use Bundled.of (closure L (s : Set M))
    exact ⟨⟨(fg_iff_structure_fg _).1 (fg_closure s.finite_toSet), ⟨Substructure.subtype _⟩⟩, hs⟩
  · simp only [mem_range, Quotient.eq]
    rintro ⟨P, ⟨⟨s, hs⟩, ⟨PM⟩⟩, hP2⟩
refine ⟨s.image PM, Setoid.trans (b := P) ?_ Quotient.exact hP2⟩
    rw [← Embedding.coe_toHom]; rw [Finset.coe_image]; rw [closure_image PM.toHom]; rw [hs]; rw [← Hom.range_eq_map]
    exact ⟨PM.equivRange.symm⟩

set_option backward.isDefEq.respectTransparency false in
-- This is not a simp-lemma because it does not apply to itself.
/--
theorem `age_directLimit` / 定理 `age_directLimit`

English:
theorem age_directLimit
  statement: {ι : Type w} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  proof: by
  classical
  ext M
  simp only [mem_iUnion]
  constructor
  · rintro ⟨Mfg, ⟨e⟩⟩
    obtain ⟨s, hs⟩ := Mfg.range e.toHom
    let out := @Quotient.out _ (DirectLimit.setoid G f)
    obtain ⟨i, hi⟩ := Finset.exists_le (s.image (Sigma.fst ∘ out))
    have e' := (DirectLimit.of L ι G f i).equivRange.symm.toEmbedding
    refine ⟨i, Mfg, ⟨e'.comp ((Substructure.inclusion ?_).comp e.equivRange.toEmbedding)⟩⟩
    rw [← hs]; rw [closure_le]
    intro x hx
    refine ⟨f (out x).1 i (hi (out x).1 (Finset.mem_image_of_mem _ hx)) (out x).2, ?_⟩
    rw [Embedding.coe_toHom]; rw [DirectLimit.of_apply]; rw [@Quotient.mk_eq_iff_out _ (_)]; rw [DirectLimit.equiv_iff G f (le_refl _) (hi (out x).1 (Finset.mem_image_of_mem _ hx))]; rw [DirectedSystem.map_self]
  · rintro ⟨i, Mfg, ⟨e⟩⟩
    exact ⟨Mfg, ⟨Embedding.comp (DirectLimit.of L ι G f i) e⟩⟩

中文:
定理 age_directLimit
  结论: {ι : 类型 w} [预序 ι] [IsDirectedOrder ι] [非空 ι]
  证明: by
  classical
  ext M
  simp only [mem_iUnion]
  constructor
  · rintro ⟨Mfg, ⟨e⟩⟩
    obtain ⟨s, hs⟩ := Mfg.range e.toHom
    let out := @Quotient.out _ (DirectLimit.setoid G f)
    obtain ⟨i, hi⟩ := Finset.exists_le (s.image (Sigma.fst ∘ out))
    have e' := (DirectLimit.of L ι G f i).equivRange.symm.toEmbedding
    refine ⟨i, Mfg, ⟨e'.comp ((Substructure.inclusion ?_).comp e.equivRange.toEmbedding)⟩⟩
    rw [← hs]; rw [closure_le]
    intro x hx
    refine ⟨f (out x).1 i (hi (out x).1 (Finset.mem_image_of_mem _ hx)) (out x).2, ?_⟩
    rw [Embedding.coe_toHom]; rw [DirectLimit.of_apply]; rw [@Quotient.mk_eq_iff_out _ (_)]; rw [DirectLimit.equiv_iff G f (le_refl _) (hi (out x).1 (Finset.mem_image_of_mem _ hx))]; rw [DirectedSystem.map_self]
  · rintro ⟨i, Mfg, ⟨e⟩⟩
    exact ⟨Mfg, ⟨Embedding.comp (DirectLimit.of L ι G f i) e⟩⟩

Depends on / 依赖: DirectLimit, DirectLimit.of, DirectLimit.setoid, Finset, Finset.exists_le, Finset.mem_image_of_mem, Mfg.range, Quotient, Quotient.out, Sigma.fst, Substructure, Substructure.inclusion, classical, closure_le, e.equivRange.toEmbedding, e.toHom, equivRange, equivRange.symm.toEmbedding, exists_le, inclusion
-/
theorem age_directLimit {ι : Type w} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (G : ι -> Type max w w') [forall i, L.Structure (G i)] (f : forall i j, i <= j -> G i ↪[L] G j)
    [DirectedSystem G fun i j h => f i j h] : L.age (DirectLimit G f) = ⋃ i : ι, L.age (G i) := by
  classical
  ext M
  simp only [mem_iUnion]
  constructor
  · rintro ⟨Mfg, ⟨e⟩⟩
    obtain ⟨s, hs⟩ := Mfg.range e.toHom
    let out := @Quotient.out _ (DirectLimit.setoid G f)
    obtain ⟨i, hi⟩ := Finset.exists_le (s.image (Sigma.fst ∘ out))
    have e' := (DirectLimit.of L ι G f i).equivRange.symm.toEmbedding
    refine ⟨i, Mfg, ⟨e'.comp ((Substructure.inclusion ?_).comp e.equivRange.toEmbedding)⟩⟩
    rw [← hs]; rw [closure_le]
    intro x hx
    refine ⟨f (out x).1 i (hi (out x).1 (Finset.mem_image_of_mem _ hx)) (out x).2, ?_⟩
    rw [Embedding.coe_toHom]; rw [DirectLimit.of_apply]; rw [@Quotient.mk_eq_iff_out _ (_)]; rw [DirectLimit.equiv_iff G f (le_refl _) (hi (out x).1 (Finset.mem_image_of_mem _ hx))]; rw [DirectedSystem.map_self]
  · rintro ⟨i, Mfg, ⟨e⟩⟩
    exact ⟨Mfg, ⟨Embedding.comp (DirectLimit.of L ι G f i) e⟩⟩

/--
theorem `exists_cg_is_age_of` / 定理 `exists_cg_is_age_of`

English:
theorem exists_cg_is_age_of
  statement: (hn : K.Nonempty)
  proof: by
  obtain ⟨F, hF⟩ := hc.exists_eq_range (hn.image _)
  simp only [Set.ext_iff, Quotient.forall, mem_image, mem_range] at hF
  simp_rw [Quotient.eq_mk_iff_out] at hF
  have hF' : forall n : Nat, (F n).out in K := by
    intro n
    obtain ⟨P, hP1, hP2⟩ := (hF (F n).out).2 ⟨n, Setoid.refl _⟩
    -- Porting note: fix hP2 because `Quotient.out (Quotient.mk' x) ≈ a` was not simplified
    -- to `x ≈ a` in hF
    replace hP2 := Setoid.trans (Setoid.symm (Quotient.mk_out P)) hP2
    exact (hp.is_equiv_invariant_of_fg fg _ _ hP2).1 hP1
  choose P hPK hP hFP using fun (N : K) (n : Nat) => jep N N.2 (F (n + 1)).out (hF' _)
  let G : Nat -> K := @Nat.rec (fun _ => K) ⟨(F 0).out, hF' 0⟩ fun n N => ⟨P N n, hPK N n⟩
  let f : forall (i j : Nat), i <= j -> (G i).val ↪[L] (G j).val :=
    DirectedSystem.natLERec fun n => (hP _ n).some
  refine ⟨Bundled.of (@DirectLimit L _ _ (fun n => (G n).val) _ f _ _), ?_, ?_⟩
  · exact DirectLimit.cg _ (fun n => (fg _ (G n).2).cg)
  · refine (age_directLimit (fun n => (G n).val) f).trans
      (subset_antisymm (iUnion_subset fun n N hN => hp (G n).val (G n).2 hN) fun N KN => ?_)
    have : Quotient.out (Quotient.mk' N) ≈ N := Quotient.eq_mk_iff_out.mp rfl
    obtain ⟨n, ⟨e⟩⟩ := (hF N).1 ⟨N, KN, this⟩
    refine mem_iUnion_of_mem n ⟨fg _ KN, ⟨Embedding.comp ?_ e.symm.toEmbedding⟩⟩
    rcases n with - | n
    · dsimp [G]; exact Embedding.refl _ _
    · dsimp [G]; exact (hFP _ n).some

中文:
定理 存在_cg_is_age_of
  结论: (hn : K.非空)
  证明: by
  obtain ⟨F, hF⟩ := hc.exists_eq_range (hn.image _)
  simp only [Set.ext_iff, Quotient.forall, mem_image, mem_range] at hF
  simp_rw [Quotient.eq_mk_iff_out] at hF
  have hF' : forall n : Nat, (F n).out in K := by
    intro n
    obtain ⟨P, hP1, hP2⟩ := (hF (F n).out).2 ⟨n, Setoid.refl _⟩
    -- Porting note: fix hP2 because `Quotient.out (Quotient.mk' x) ≈ a` was not simplified
    -- to `x ≈ a` in hF
    replace hP2 := Setoid.trans (Setoid.symm (Quotient.mk_out P)) hP2
    exact (hp.is_equiv_invariant_of_fg fg _ _ hP2).1 hP1
  choose P hPK hP hFP using fun (N : K) (n : Nat) => jep N N.2 (F (n + 1)).out (hF' _)
  let G : Nat -> K := @Nat.rec (fun _ => K) ⟨(F 0).out, hF' 0⟩ fun n N => ⟨P N n, hPK N n⟩
  let f : forall (i j : Nat), i <= j -> (G i).val ↪[L] (G j).val :=
    DirectedSystem.natLERec fun n => (hP _ n).some
  refine ⟨Bundled.of (@DirectLimit L _ _ (fun n => (G n).val) _ f _ _), ?_, ?_⟩
  · exact DirectLimit.cg _ (fun n => (fg _ (G n).2).cg)
  · refine (age_directLimit (fun n => (G n).val) f).trans
      (subset_antisymm (iUnion_subset fun n N hN => hp (G n).val (G n).2 hN) fun N KN => ?_)
    have : Quotient.out (Quotient.mk' N) ≈ N := Quotient.eq_mk_iff_out.mp rfl
    obtain ⟨n, ⟨e⟩⟩ := (hF N).1 ⟨N, KN, this⟩
    refine mem_iUnion_of_mem n ⟨fg _ KN, ⟨Embedding.comp ?_ e.symm.toEmbedding⟩⟩
    rcases n with - | n
    · dsimp [G]; exact Embedding.refl _ _
    · dsimp [G]; exact (hFP _ n).some

Depends on / 依赖: Quotient, Quotient.eq_mk_iff_out, Quotient.forall, Set.ext_iff, Setoid, Setoid.refl, eq_mk_iff_out, exists_eq_range, ext_iff, hc.exists_eq_range, hn.image, mem_image, mem_range, simp_rw
-/
theorem exists_cg_is_age_of (hn : K.Nonempty)
    (hc : (Quotient.mk' '' K).Countable)
    (fg : forall M : Bundled.{w} L.Structure, M in K -> Structure.FG L M) (hp : Hereditary K)
    (jep : JointEmbedding K) : exists M : Bundled.{w} L.Structure, Structure.CG L M ∧ L.age M = K := by
  obtain ⟨F, hF⟩ := hc.exists_eq_range (hn.image _)
  simp only [Set.ext_iff, Quotient.forall, mem_image, mem_range] at hF
  simp_rw [Quotient.eq_mk_iff_out] at hF
  have hF' : forall n : Nat, (F n).out in K := by
    intro n
    obtain ⟨P, hP1, hP2⟩ := (hF (F n).out).2 ⟨n, Setoid.refl _⟩
    -- Porting note: fix hP2 because `Quotient.out (Quotient.mk' x) ≈ a` was not simplified
    -- to `x ≈ a` in hF
    replace hP2 := Setoid.trans (Setoid.symm (Quotient.mk_out P)) hP2
    exact (hp.is_equiv_invariant_of_fg fg _ _ hP2).1 hP1
  choose P hPK hP hFP using fun (N : K) (n : Nat) => jep N N.2 (F (n + 1)).out (hF' _)
  let G : Nat -> K := @Nat.rec (fun _ => K) ⟨(F 0).out, hF' 0⟩ fun n N => ⟨P N n, hPK N n⟩
  let f : forall (i j : Nat), i <= j -> (G i).val ↪[L] (G j).val :=
    DirectedSystem.natLERec fun n => (hP _ n).some
  refine ⟨Bundled.of (@DirectLimit L _ _ (fun n => (G n).val) _ f _ _), ?_, ?_⟩
  · exact DirectLimit.cg _ (fun n => (fg _ (G n).2).cg)
  · refine (age_directLimit (fun n => (G n).val) f).trans
      (subset_antisymm (iUnion_subset fun n N hN => hp (G n).val (G n).2 hN) fun N KN => ?_)
    have : Quotient.out (Quotient.mk' N) ≈ N := Quotient.eq_mk_iff_out.mp rfl
    obtain ⟨n, ⟨e⟩⟩ := (hF N).1 ⟨N, KN, this⟩
    refine mem_iUnion_of_mem n ⟨fg _ KN, ⟨Embedding.comp ?_ e.symm.toEmbedding⟩⟩
    rcases n with - | n
    · dsimp [G]; exact Embedding.refl _ _
    · dsimp [G]; exact (hFP _ n).some

/--
theorem `exists_countable_is_age_of_iff` / 定理 `exists_countable_is_age_of_iff`

English:
theorem exists_countable_is_age_of_iff
  given: [Countable (Σ l, L.Functions l)]
  proof: by
  constructor
  · rintro ⟨M, h1, h2, rfl⟩
    refine ⟨age.nonempty M, age.is_equiv_invariant L M, age.countable_quotient M, fun N hN => hN.1,
      age.hereditary M, age.jointEmbedding M⟩
  · rintro ⟨Kn, _, cq, hfg, hp, jep⟩
    obtain ⟨M, hM, rfl⟩ := exists_cg_is_age_of Kn cq hfg hp jep
    exact ⟨M, Structure.cg_iff_countable.1 hM, rfl⟩

中文:
定理 存在_countable_is_age_of_iff
  条件: [可数 (Σ l, L.函数 l)]
  证明: by
  constructor
  · rintro ⟨M, h1, h2, rfl⟩
    refine ⟨age.nonempty M, age.is_equiv_invariant L M, age.countable_quotient M, fun N hN => hN.1,
      age.hereditary M, age.jointEmbedding M⟩
  · rintro ⟨Kn, _, cq, hfg, hp, jep⟩
    obtain ⟨M, hM, rfl⟩ := exists_cg_is_age_of Kn cq hfg hp jep
    exact ⟨M, Structure.cg_iff_countable.1 hM, rfl⟩

Depends on / 依赖: Structure, Structure.cg_iff_countable, age.countable_quotient, age.hereditary, age.is_equiv_invariant, age.jointEmbedding, age.nonempty, cg_iff_countable, countable_quotient, exists_cg_is_age_of, hereditary, is_equiv_invariant, jointEmbedding, nonempty
-/
theorem exists_countable_is_age_of_iff [Countable (Σ l, L.Functions l)] :
    (exists M : Bundled.{w} L.Structure, Countable M ∧ L.age M = K) ↔
      K.Nonempty ∧ (forall M N : Bundled.{w} L.Structure, Nonempty (M ≃[L] N) -> (M in K ↔ N in K)) ∧
      (Quotient.mk' '' K).Countable ∧ (forall M : Bundled.{w} L.Structure, M in K -> Structure.FG L M) ∧
      Hereditary K ∧ JointEmbedding K := by
  constructor
  · rintro ⟨M, h1, h2, rfl⟩
    refine ⟨age.nonempty M, age.is_equiv_invariant L M, age.countable_quotient M, fun N hN => hN.1,
      age.hereditary M, age.jointEmbedding M⟩
  · rintro ⟨Kn, _, cq, hfg, hp, jep⟩
    obtain ⟨M, hM, rfl⟩ := exists_cg_is_age_of Kn cq hfg hp jep
    exact ⟨M, Structure.cg_iff_countable.1 hM, rfl⟩

variable (L)

/--
Definition of `IsUltrahomogeneous` / `IsUltrahomogeneous` 的定义

English:
definition IsUltrahomogeneous
  signature: : Prop
  body: forall (S : L.Substructure M) (_ : S.FG) (f : S ↪[L] M),
    exists g : M ≃[L] M, f = g.toEmbedding.comp S.subtype

中文:
定义 IsUltrahomogeneous
  签名: : 命题
  定义体: forall (S : L.Substructure M) (_ : S.FG) (f : S ↪[L] M),
    exists g : M ≃[L] M, f = g.toEmbedding.comp S.subtype

Depends on / 依赖: L.Substructure, S.FG, S.subtype, Substructure, g.toEmbedding.comp, subtype, toEmbedding
-/
def IsUltrahomogeneous : Prop :=
  forall (S : L.Substructure M) (_ : S.FG) (f : S ↪[L] M),
    exists g : M ≃[L] M, f = g.toEmbedding.comp S.subtype

variable {L} (K)

/--
Definition of `IsFraisseLimit` / `IsFraisseLimit` 的定义

English:
structure IsFraisseLimit
  parameters: [Countable (Σ l, L.Functions l)] [Countable M]
  axioms and operations (2):
    - ultrahomogeneous : IsUltrahomogeneous L M
    - age : L.age M = K

中文:
结构 是FraisseLimit
  参数: [可数 (Σ l, L.函数 l)] [可数 M]
  公理与运算 (2 个):
    - ultrahomogeneous : IsUltrahomogeneous L M
    - age : L.age M = K
-/
structure IsFraisseLimit [Countable (Σ l, L.Functions l)] [Countable M] : Prop where
  protected ultrahomogeneous : IsUltrahomogeneous L M
  protected age : L.age M = K

variable {M}

/--
theorem `IsUltrahomogeneous.extend_embedding` / 定理 `IsUltrahomogeneous.extend_embedding`

English:
theorem IsUltrahomogeneous.extend_embedding
  statement: (M_homog : L.IsUltrahomogeneous M) {S : Type*}
  proof: by
  let ⟨r⟩ := h
  let s := r.comp g
  let ⟨t, eq⟩ := M_homog s.toHom.range (S_FG.range s.toHom) (f.comp s.equivRange.symm.toEmbedding)
  use t.toEmbedding.comp r
  change _ = t.toEmbedding.comp s
  ext x
  have eq' := congr_fun (congr_arg DFunLike.coe eq) ⟨s x, Hom.mem_range.2 ⟨x, rfl⟩⟩
  simp only [Embedding.comp_apply,
    coe_subtype] at eq'
  simp only [Embedding.comp_apply, ← eq', Equiv.coe_toEmbedding, EmbeddingLike.apply_eq_iff_eq]
  apply (Embedding.equivRange (Embedding.comp r g)).injective
  ext
  simp only [Equiv.apply_symm_apply, Embedding.equivRange_apply, s]

中文:
定理 IsUltrahomogeneous.extend_embedding
  结论: (M_homog : L.IsUltrahomogeneous M) {S : 类型}
  证明: by
  let ⟨r⟩ := h
  let s := r.comp g
  let ⟨t, eq⟩ := M_homog s.toHom.range (S_FG.range s.toHom) (f.comp s.equivRange.symm.toEmbedding)
  use t.toEmbedding.comp r
  change _ = t.toEmbedding.comp s
  ext x
  have eq' := congr_fun (congr_arg DFunLike.coe eq) ⟨s x, Hom.mem_range.2 ⟨x, rfl⟩⟩
  simp only [Embedding.comp_apply,
    coe_subtype] at eq'
  simp only [Embedding.comp_apply, ← eq', Equiv.coe_toEmbedding, EmbeddingLike.apply_eq_iff_eq]
  apply (Embedding.equivRange (Embedding.comp r g)).injective
  ext
  simp only [Equiv.apply_symm_apply, Embedding.equivRange_apply, s]

Depends on / 依赖: DFunLike, DFunLike.coe, Embedding, Embedding.comp, Embedding.comp_apply, Embedding.equivRange, EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, Equiv.coe_toEmbedding, Hom.mem_range, M_homog, S_FG, S_FG.range, apply_eq_iff_eq, coe_subtype, coe_toEmbedding, comp_apply, congr_arg, congr_fun, equivRange
-/
theorem IsUltrahomogeneous.extend_embedding (M_homog : L.IsUltrahomogeneous M) {S : Type*}
    [L.Structure S] (S_FG : FG L S) {T : Type*} [L.Structure T] [h : Nonempty (T ↪[L] M)]
    (f : S ↪[L] M) (g : S ↪[L] T) :
    exists f' : T ↪[L] M, f = f'.comp g := by
  let ⟨r⟩ := h
  let s := r.comp g
  let ⟨t, eq⟩ := M_homog s.toHom.range (S_FG.range s.toHom) (f.comp s.equivRange.symm.toEmbedding)
  use t.toEmbedding.comp r
  change _ = t.toEmbedding.comp s
  ext x
  have eq' := congr_fun (congr_arg DFunLike.coe eq) ⟨s x, Hom.mem_range.2 ⟨x, rfl⟩⟩
  simp only [Embedding.comp_apply,
    coe_subtype] at eq'
  simp only [Embedding.comp_apply, ← eq', Equiv.coe_toEmbedding, EmbeddingLike.apply_eq_iff_eq]
  apply (Embedding.equivRange (Embedding.comp r g)).injective
  ext
  simp only [Equiv.apply_symm_apply, Embedding.equivRange_apply, s]

/--
theorem `isUltrahomogeneous_iff_IsExtensionPair` / 定理 `isUltrahomogeneous_iff_IsExtensionPair`

English:
theorem isUltrahomogeneous_iff_IsExtensionPair
  given: (M_CG : CG L M)
  statement: L.IsUltrahomogeneous M ↔
  proof: by
  constructor
  · intro M_homog ⟨f, f_FG⟩ m
    let S := f.dom ⊔ closure L {m}
    have dom_le_S : f.dom <= S := le_sup_left
    let ⟨f', eq_f'⟩ := M_homog.extend_embedding (f.dom.fg_iff_structure_fg.1 f_FG)
      ((subtype _).comp f.toEquiv.toEmbedding) (inclusion dom_le_S) (h := ⟨subtype _⟩)
    refine ⟨⟨⟨S, f'.toHom.range, f'.equivRange⟩, f_FG.sup (fg_closure_singleton _)⟩,
      subset_closure.trans (le_sup_right : _ <= S) (mem_singleton m), ⟨dom_le_S, ?_⟩⟩
    ext
    simp only [Embedding.comp_apply, Equiv.coe_toEmbedding, coe_subtype, eq_f',
      Embedding.equivRange_apply, Substructure.coe_inclusion]
  · intro h S S_FG f
    let ⟨g, ⟨dom_le_dom, eq⟩⟩ :=
      equiv_between_cg M_CG M_CG ⟨⟨S, f.toHom.range, f.equivRange⟩, S_FG⟩ h h
    use g
    simp only [Embedding.subtype_equivRange] at eq
    rw [← eq]
    ext
    rfl

中文:
定理 isUltrahomogeneous_iff_IsExtensionPair
  条件: (M_CG : CG L M)
  结论: L.IsUltrahomogeneous M ↔
  证明: by
  constructor
  · intro M_homog ⟨f, f_FG⟩ m
    let S := f.dom ⊔ closure L {m}
    have dom_le_S : f.dom <= S := le_sup_left
    let ⟨f', eq_f'⟩ := M_homog.extend_embedding (f.dom.fg_iff_structure_fg.1 f_FG)
      ((subtype _).comp f.toEquiv.toEmbedding) (inclusion dom_le_S) (h := ⟨subtype _⟩)
    refine ⟨⟨⟨S, f'.toHom.range, f'.equivRange⟩, f_FG.sup (fg_closure_singleton _)⟩,
      subset_closure.trans (le_sup_right : _ <= S) (mem_singleton m), ⟨dom_le_S, ?_⟩⟩
    ext
    simp only [Embedding.comp_apply, Equiv.coe_toEmbedding, coe_subtype, eq_f',
      Embedding.equivRange_apply, Substructure.coe_inclusion]
  · intro h S S_FG f
    let ⟨g, ⟨dom_le_dom, eq⟩⟩ :=
      equiv_between_cg M_CG M_CG ⟨⟨S, f.toHom.range, f.equivRange⟩, S_FG⟩ h h
    use g
    simp only [Embedding.subtype_equivRange] at eq
    rw [← eq]
    ext
    rfl

Depends on / 依赖: Embedding, Embedding.comp_apply, Equiv.coe_toEmbedding, M_homog, M_homog.extend_embedding, closure, coe_toEmbedding, comp_apply, dom_le_S, eq_f, equivRange, extend_embedding, f.dom, f.dom.fg_iff_structure_fg, f.toEquiv.toEmbedding, f_FG, f_FG.sup, fg_closure_singleton, fg_iff_structure_fg, inclusion
-/
theorem isUltrahomogeneous_iff_IsExtensionPair (M_CG : CG L M) : L.IsUltrahomogeneous M ↔
    L.IsExtensionPair M M := by
  constructor
  · intro M_homog ⟨f, f_FG⟩ m
    let S := f.dom ⊔ closure L {m}
    have dom_le_S : f.dom <= S := le_sup_left
    let ⟨f', eq_f'⟩ := M_homog.extend_embedding (f.dom.fg_iff_structure_fg.1 f_FG)
      ((subtype _).comp f.toEquiv.toEmbedding) (inclusion dom_le_S) (h := ⟨subtype _⟩)
    refine ⟨⟨⟨S, f'.toHom.range, f'.equivRange⟩, f_FG.sup (fg_closure_singleton _)⟩,
      subset_closure.trans (le_sup_right : _ <= S) (mem_singleton m), ⟨dom_le_S, ?_⟩⟩
    ext
    simp only [Embedding.comp_apply, Equiv.coe_toEmbedding, coe_subtype, eq_f',
      Embedding.equivRange_apply, Substructure.coe_inclusion]
  · intro h S S_FG f
    let ⟨g, ⟨dom_le_dom, eq⟩⟩ :=
      equiv_between_cg M_CG M_CG ⟨⟨S, f.toHom.range, f.equivRange⟩, S_FG⟩ h h
    use g
    simp only [Embedding.subtype_equivRange] at eq
    rw [← eq]
    ext
    rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `IsUltrahomogeneous.amalgamation_age` / 定理 `IsUltrahomogeneous.amalgamation_age`

English:
theorem IsUltrahomogeneous.amalgamation_age
  given: (h : L.IsUltrahomogeneous M)
  proof: by
  rintro N P Q NP NQ ⟨Nfg, ⟨-⟩⟩ ⟨Pfg, ⟨PM⟩⟩ ⟨Qfg, ⟨QM⟩⟩
  obtain ⟨g, hg⟩ := h (PM.comp NP).toHom.range (Nfg.range _)
    ((QM.comp NQ).comp (PM.comp NP).equivRange.symm.toEmbedding)
  let s := (g.toHom.comp PM.toHom).range ⊔ QM.toHom.range
  refine ⟨Bundled.of s,
    Embedding.comp (Substructure.inclusion le_sup_left)
      (g.toEmbedding.comp PM).equivRange.toEmbedding,
    Embedding.comp (Substructure.inclusion le_sup_right) QM.equivRange.toEmbedding,
    ⟨(fg_iff_structure_fg _).1 (FG.sup (Pfg.range _) (Qfg.range _)), ⟨Substructure.subtype _⟩⟩, ?_⟩
  ext n
  apply Subtype.ext
  have hgn := (Embedding.ext_iff.1 hg) ((PM.comp NP).equivRange n)
  simp only [Embedding.comp_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply,
    Substructure.coe_subtype, Embedding.equivRange_apply] at hgn
  simp only [Embedding.comp_apply, Equiv.coe_toEmbedding]
  erw [Substructure.coe_inclusion, Substructure.coe_inclusion]
  simp only [Embedding.equivRange_apply, hgn]
  -- This used to be `simp only [...]` before https://github.com/leanprover/lean4/pull/2644
  erw [Embedding.comp_apply, Equiv.coe_toEmbedding,
    Embedding.equivRange_apply]
  simp

中文:
定理 IsUltrahomogeneous.amalgamation_age
  条件: (h : L.IsUltrahomogeneous M)
  证明: by
  rintro N P Q NP NQ ⟨Nfg, ⟨-⟩⟩ ⟨Pfg, ⟨PM⟩⟩ ⟨Qfg, ⟨QM⟩⟩
  obtain ⟨g, hg⟩ := h (PM.comp NP).toHom.range (Nfg.range _)
    ((QM.comp NQ).comp (PM.comp NP).equivRange.symm.toEmbedding)
  let s := (g.toHom.comp PM.toHom).range ⊔ QM.toHom.range
  refine ⟨Bundled.of s,
    Embedding.comp (Substructure.inclusion le_sup_left)
      (g.toEmbedding.comp PM).equivRange.toEmbedding,
    Embedding.comp (Substructure.inclusion le_sup_right) QM.equivRange.toEmbedding,
    ⟨(fg_iff_structure_fg _).1 (FG.sup (Pfg.range _) (Qfg.range _)), ⟨Substructure.subtype _⟩⟩, ?_⟩
  ext n
  apply Subtype.ext
  have hgn := (Embedding.ext_iff.1 hg) ((PM.comp NP).equivRange n)
  simp only [Embedding.comp_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply,
    Substructure.coe_subtype, Embedding.equivRange_apply] at hgn
  simp only [Embedding.comp_apply, Equiv.coe_toEmbedding]
  erw [Substructure.coe_inclusion, Substructure.coe_inclusion]
  simp only [Embedding.equivRange_apply, hgn]
  -- This used to be `simp only [...]` before https://github.com/leanprover/lean4/pull/2644
  erw [Embedding.comp_apply, Equiv.coe_toEmbedding,
    Embedding.equivRange_apply]
  simp

Depends on / 依赖: Bundled, Bundled.of, Embedding, Embedding.comp, FG.sup, Nfg.range, PM.comp, PM.toHom, Pfg.range, QM.comp, QM.equivRange.toEmbedding, QM.toHom.range, Qfg.range, Substructure, Substructure.inclusion, equivRange, equivRange.symm.toEmbedding, equivRange.toEmbedding, fg_iff_structure_fg, g.toEmbedding.comp
-/
theorem IsUltrahomogeneous.amalgamation_age (h : L.IsUltrahomogeneous M) :
    Amalgamation (L.age M) := by
  rintro N P Q NP NQ ⟨Nfg, ⟨-⟩⟩ ⟨Pfg, ⟨PM⟩⟩ ⟨Qfg, ⟨QM⟩⟩
  obtain ⟨g, hg⟩ := h (PM.comp NP).toHom.range (Nfg.range _)
    ((QM.comp NQ).comp (PM.comp NP).equivRange.symm.toEmbedding)
  let s := (g.toHom.comp PM.toHom).range ⊔ QM.toHom.range
  refine ⟨Bundled.of s,
    Embedding.comp (Substructure.inclusion le_sup_left)
      (g.toEmbedding.comp PM).equivRange.toEmbedding,
    Embedding.comp (Substructure.inclusion le_sup_right) QM.equivRange.toEmbedding,
    ⟨(fg_iff_structure_fg _).1 (FG.sup (Pfg.range _) (Qfg.range _)), ⟨Substructure.subtype _⟩⟩, ?_⟩
  ext n
  apply Subtype.ext
  have hgn := (Embedding.ext_iff.1 hg) ((PM.comp NP).equivRange n)
  simp only [Embedding.comp_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply,
    Substructure.coe_subtype, Embedding.equivRange_apply] at hgn
  simp only [Embedding.comp_apply, Equiv.coe_toEmbedding]
  erw [Substructure.coe_inclusion, Substructure.coe_inclusion]
  simp only [Embedding.equivRange_apply, hgn]
  -- This used to be `simp only [...]` before https://github.com/leanprover/lean4/pull/2644
  erw [Embedding.comp_apply, Equiv.coe_toEmbedding,
    Embedding.equivRange_apply]
  simp

/--
theorem `IsUltrahomogeneous.age_isFraisse` / 定理 `IsUltrahomogeneous.age_isFraisse`

English:
theorem IsUltrahomogeneous.age_isFraisse
  given: [Countable M] (h : L.IsUltrahomogeneous M)
  proof: ⟨age.nonempty M, fun _ hN => hN.1, age.countable_quotient M,
    age.hereditary M, age.jointEmbedding M, h.amalgamation_age⟩

中文:
定理 IsUltrahomogeneous.age_isFraisse
  条件: [可数 M] (h : L.IsUltrahomogeneous M)
  证明: ⟨age.nonempty M, fun _ hN => hN.1, age.countable_quotient M,
    age.hereditary M, age.jointEmbedding M, h.amalgamation_age⟩

Depends on / 依赖: age.countable_quotient, age.hereditary, age.jointEmbedding, age.nonempty, amalgamation_age, countable_quotient, h.amalgamation_age, hereditary, jointEmbedding, nonempty
-/
theorem IsUltrahomogeneous.age_isFraisse [Countable M] (h : L.IsUltrahomogeneous M) :
    IsFraisse (L.age M) :=
  ⟨age.nonempty M, fun _ hN => hN.1, age.countable_quotient M,
    age.hereditary M, age.jointEmbedding M, h.amalgamation_age⟩

namespace IsFraisseLimit

/--
theorem `isFraisse` / 定理 `isFraisse`

English:
theorem isFraisse
  given: [Countable (Σ l, L.Functions l)] [Countable M] (h : IsFraisseLimit K M)
  proof: (congr rfl h.age).mp h.ultrahomogeneous.age_isFraisse

中文:
定理 isFraisse
  条件: [可数 (Σ l, L.函数 l)] [可数 M] (h : 是FraisseLimit K M)
  证明: (congr rfl h.age).mp h.ultrahomogeneous.age_isFraisse

Depends on / 依赖: age_isFraisse, h.age, h.ultrahomogeneous.age_isFraisse, ultrahomogeneous
-/
theorem isFraisse [Countable (Σ l, L.Functions l)] [Countable M] (h : IsFraisseLimit K M) :
    IsFraisse K :=
  (congr rfl h.age).mp h.ultrahomogeneous.age_isFraisse

variable {K} {N : Type w} [L.Structure N]
variable [Countable (Σ l, L.Functions l)] [Countable M] [Countable N]
variable (hM : IsFraisseLimit K M) (hN : IsFraisseLimit K N)

include hM hN

/--
theorem `isExtensionPair` / 定理 `isExtensionPair`

English:
theorem isExtensionPair
  statement: L.IsExtensionPair M N
  proof: by
  intro ⟨f, f_FG⟩ m
  let S := f.dom ⊔ closure L {m}
  have S_FG : S.FG := f_FG.sup (Substructure.fg_closure_singleton _)
  have S_in_age_N : ⟨S, inferInstance⟩ in L.age N := by
    rw [hN.age]; rw [← hM.age]
    exact ⟨(fg_iff_structure_fg S).1 S_FG, ⟨subtype _⟩⟩
  have nonempty_S_N : Nonempty (S ↪[L] N) := S_in_age_N.2
  let ⟨g, g_eq⟩ := hN.ultrahomogeneous.extend_embedding (f.dom.fg_iff_structure_fg.1 f_FG)
    ((subtype f.cod).comp f.toEquiv.toEmbedding) (inclusion (le_sup_left : _ <= S))
  refine ⟨⟨⟨S, g.toHom.range, g.equivRange⟩, S_FG⟩,
    subset_closure.trans (le_sup_right : _ <= S) (mem_singleton m), ⟨le_sup_left, ?_⟩⟩
  ext
  simp [S, g_eq]

中文:
定理 isExtensionPair
  结论: L.IsExtensionPair M N
  证明: by
  intro ⟨f, f_FG⟩ m
  let S := f.dom ⊔ closure L {m}
  have S_FG : S.FG := f_FG.sup (Substructure.fg_closure_singleton _)
  have S_in_age_N : ⟨S, inferInstance⟩ in L.age N := by
    rw [hN.age]; rw [← hM.age]
    exact ⟨(fg_iff_structure_fg S).1 S_FG, ⟨subtype _⟩⟩
  have nonempty_S_N : Nonempty (S ↪[L] N) := S_in_age_N.2
  let ⟨g, g_eq⟩ := hN.ultrahomogeneous.extend_embedding (f.dom.fg_iff_structure_fg.1 f_FG)
    ((subtype f.cod).comp f.toEquiv.toEmbedding) (inclusion (le_sup_left : _ <= S))
  refine ⟨⟨⟨S, g.toHom.range, g.equivRange⟩, S_FG⟩,
    subset_closure.trans (le_sup_right : _ <= S) (mem_singleton m), ⟨le_sup_left, ?_⟩⟩
  ext
  simp [S, g_eq]
-/
protected theorem isExtensionPair : L.IsExtensionPair M N := by
  intro ⟨f, f_FG⟩ m
  let S := f.dom ⊔ closure L {m}
  have S_FG : S.FG := f_FG.sup (Substructure.fg_closure_singleton _)
  have S_in_age_N : ⟨S, inferInstance⟩ in L.age N := by
    rw [hN.age]; rw [← hM.age]
    exact ⟨(fg_iff_structure_fg S).1 S_FG, ⟨subtype _⟩⟩
  have nonempty_S_N : Nonempty (S ↪[L] N) := S_in_age_N.2
  let ⟨g, g_eq⟩ := hN.ultrahomogeneous.extend_embedding (f.dom.fg_iff_structure_fg.1 f_FG)
    ((subtype f.cod).comp f.toEquiv.toEmbedding) (inclusion (le_sup_left : _ <= S))
  refine ⟨⟨⟨S, g.toHom.range, g.equivRange⟩, S_FG⟩,
    subset_closure.trans (le_sup_right : _ <= S) (mem_singleton m), ⟨le_sup_left, ?_⟩⟩
  ext
  simp [S, g_eq]

/--
theorem `nonempty_equiv` / 定理 `nonempty_equiv`

English:
theorem nonempty_equiv
  statement: Nonempty (M ≃[L] N)
  proof: by
  let S : L.Substructure M := ⊥
  have S_fg : FG L S := (fg_iff_structure_fg _).1 Substructure.fg_bot
  obtain ⟨_, ⟨emb_S : S ↪[L] N⟩⟩ : ⟨S, inferInstance⟩ in L.age N := by
    rw [hN.age]; rw [← hM.age]
    exact ⟨S_fg, ⟨subtype _⟩⟩
  let v : M ≃ₚ[L] N := {
    dom := S
    cod := emb_S.toHom.range
    toEquiv := emb_S.equivRange
  }
  exact ⟨Exists.choose (equiv_between_cg cg_of_countable cg_of_countable
    ⟨v, ((Substructure.fg_iff_structure_fg _).2 S_fg)⟩ (hM.isExtensionPair hN)
      (hN.isExtensionPair hM))⟩

中文:
定理 nonempty_equiv
  结论: 非空 (M ≃[L] N)
  证明: by
  let S : L.Substructure M := ⊥
  have S_fg : FG L S := (fg_iff_structure_fg _).1 Substructure.fg_bot
  obtain ⟨_, ⟨emb_S : S ↪[L] N⟩⟩ : ⟨S, inferInstance⟩ in L.age N := by
    rw [hN.age]; rw [← hM.age]
    exact ⟨S_fg, ⟨subtype _⟩⟩
  let v : M ≃ₚ[L] N := {
    dom := S
    cod := emb_S.toHom.range
    toEquiv := emb_S.equivRange
  }
  exact ⟨Exists.choose (equiv_between_cg cg_of_countable cg_of_countable
    ⟨v, ((Substructure.fg_iff_structure_fg _).2 S_fg)⟩ (hM.isExtensionPair hN)
      (hN.isExtensionPair hM))⟩

Depends on / 依赖: Exists, Exists.choose, L.Substructure, L.age, S_fg, Substructure, Substructure.fg_bot, Substructure.fg_iff_structure_fg, cg_of_countable, emb_S, emb_S.equivRange, emb_S.toHom.range, equivRange, equiv_between_cg, fg_bot, fg_iff_structure_fg, hM.age, hM.isExtensionPair, hN.age, hN.isExtensionPair
-/
theorem nonempty_equiv : Nonempty (M ≃[L] N) := by
  let S : L.Substructure M := ⊥
  have S_fg : FG L S := (fg_iff_structure_fg _).1 Substructure.fg_bot
  obtain ⟨_, ⟨emb_S : S ↪[L] N⟩⟩ : ⟨S, inferInstance⟩ in L.age N := by
    rw [hN.age]; rw [← hM.age]
    exact ⟨S_fg, ⟨subtype _⟩⟩
  let v : M ≃ₚ[L] N := {
    dom := S
    cod := emb_S.toHom.range
    toEquiv := emb_S.equivRange
  }
  exact ⟨Exists.choose (equiv_between_cg cg_of_countable cg_of_countable
    ⟨v, ((Substructure.fg_iff_structure_fg _).2 S_fg)⟩ (hM.isExtensionPair hN)
      (hN.isExtensionPair hM))⟩

end IsFraisseLimit

namespace empty

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isFraisseLimit_of_countable_infinite` / 定理 `isFraisseLimit_of_countable_infinite`

English:
theorem isFraisseLimit_of_countable_infinite
  proof: by
    ext S
    simp only [age, Structure.fg_iff_finite, mem_ofPred_eq, and_iff_left_iff_imp]
    intro hS
    simp
  ultrahomogeneous S hS f := by
    classical
    have : Finite S := hS.finite
    have : Infinite { x // x ∉ S } := ((Set.toFinite _).infinite_compl).to_subtype
    have : Finite f.toHom.range := (((Substructure.fg_iff_structure_fg S).1 hS).range _).finite
    have : Infinite { x // x ∉ f.toHom.range } := ((Set.toFinite _).infinite_compl).to_subtype
    refine ⟨StrongHomClass.toEquiv (f.equivRange.subtypeCongr nonempty_equiv_of_countable.some), ?_⟩
    ext x
    simp [Equiv.subtypeCongr]

中文:
定理 isFraisseLimit_of_countable_infinite
  证明: by
    ext S
    simp only [age, Structure.fg_iff_finite, mem_ofPred_eq, and_iff_left_iff_imp]
    intro hS
    simp
  ultrahomogeneous S hS f := by
    classical
    have : Finite S := hS.finite
    have : Infinite { x // x ∉ S } := ((Set.toFinite _).infinite_compl).to_subtype
    have : Finite f.toHom.range := (((Substructure.fg_iff_structure_fg S).1 hS).range _).finite
    have : Infinite { x // x ∉ f.toHom.range } := ((Set.toFinite _).infinite_compl).to_subtype
    refine ⟨StrongHomClass.toEquiv (f.equivRange.subtypeCongr nonempty_equiv_of_countable.some), ?_⟩
    ext x
    simp [Equiv.subtypeCongr]

Depends on / 依赖: Finite, Infinite, Set.toFinite, StrongHomClass, StrongHomClass.toEquiv, Structure, Structure.fg_iff_finite, Substructure, Substructure.fg_iff_structure_fg, and_iff_left_iff_imp, classical, equivRange, f.equivRange.subtypeCongr, f.toHom.range, fg_iff_finite, fg_iff_structure_fg, finite, hS.finite, infinite_compl, mem_ofPred_eq
-/
theorem isFraisseLimit_of_countable_infinite
    (M : Type*) [Countable M] [Infinite M] [Language.empty.Structure M] :
    IsFraisseLimit { S : Bundled Language.empty.Structure | Finite S } M where
  age := by
    ext S
    simp only [age, Structure.fg_iff_finite, mem_ofPred_eq, and_iff_left_iff_imp]
    intro hS
    simp
  ultrahomogeneous S hS f := by
    classical
    have : Finite S := hS.finite
    have : Infinite { x // x ∉ S } := ((Set.toFinite _).infinite_compl).to_subtype
    have : Finite f.toHom.range := (((Substructure.fg_iff_structure_fg S).1 hS).range _).finite
    have : Infinite { x // x ∉ f.toHom.range } := ((Set.toFinite _).infinite_compl).to_subtype
    refine ⟨StrongHomClass.toEquiv (f.equivRange.subtypeCongr nonempty_equiv_of_countable.some), ?_⟩
    ext x
    simp [Equiv.subtypeCongr]

/--
theorem `isFraisse_finite` / 定理 `isFraisse_finite`

English:
theorem isFraisse_finite
  statement: IsFraisse { S : Bundled.{w} Language.empty.Structure | Finite S }
  proof: by
  have : Language.empty.Structure (ULift Nat : Type w) := emptyStructure
  exact (isFraisseLimit_of_countable_infinite (ULift Nat)).isFraisse

中文:
定理 isFraisse_finite
  结论: 是Fraisse { S : 打包.{w} Language.empty.结构 | 有限 S }
  证明: by
  have : Language.empty.Structure (ULift Nat : Type w) := emptyStructure
  exact (isFraisseLimit_of_countable_infinite (ULift Nat)).isFraisse

Depends on / 依赖: Language, Language.empty.Structure, Structure, emptyStructure, isFraisse, isFraisseLimit_of_countable_infinite
-/
theorem isFraisse_finite : IsFraisse { S : Bundled.{w} Language.empty.Structure | Finite S } := by
  have : Language.empty.Structure (ULift Nat : Type w) := emptyStructure
  exact (isFraisseLimit_of_countable_infinite (ULift Nat)).isFraisse

end empty

end Language

end FirstOrder
