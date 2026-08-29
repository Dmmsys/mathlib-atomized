/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Data.Set.Subset
public import Mathlib.Order.Irreducible
public import Mathlib.Topology.Order.LowerUpperTopology
public import Mathlib.Topology.Sets.Closeds

/-!
# Hull-Kernel Topology

Let `α` be a `CompleteLattice` and let `T` be a subset of `α`. The pair of maps
`S → sInf (Subtype.val '' S)` and `a → T ↓∩ Ici a` are often referred to as the `kernel` and the
`hull` respectively. They form an antitone Galois connection between the subsets of `T` and `α`.
When `α` can be generated from `T` by taking infs, this becomes a Galois insertion and the relative
topology (`Topology.lower`) on `T` takes on a particularly simple form: the relative-open sets are
exactly the sets of the form `(hull T a)ᶜ` for some `a` in `α`. The topological closure coincides
with the closure arising from the Galois insertion. For this reason the relative lower topology on
`T` is often referred to as the "hull-kernel topology". The names "Jacobson topology" and "structure
topology" also occur in the literature.

## Main statements

- `PrimitiveSpectrum.isTopologicalBasis_relativeLower` - the sets `(hull a)ᶜ` form a basis for the
  relative lower topology on `T`.
- `PrimitiveSpectrum.isOpen_iff` - for a complete lattice, the sets `(hull a)ᶜ` are the relative
  topology.
- `PrimitiveSpectrum.gc` - the `kernel` and the `hull` form a Galois connection
- `PrimitiveSpectrum.gi` - when `T` generates `α`, the Galois connection becomes an insertion.

## Implementation notes

The antitone Galois connection from `Set T` to `α` is implemented as a monotone Galois connection
between `Set T` to `αᵒᵈ`.

## Motivation

The motivating example for the study of a set `T` of prime elements which generate `α` is the
primitive spectrum of the lattice of M-ideals of a Banach space.

## References

* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]
* [Henriksen et al, *Joincompact spaces, continuous lattices and C⋆-algebras*][henriksen_et_al1997]

## Tags

lower topology, hull-kernel topology, Jacobson topology, structure topology, primitive spectrum

-/

@[expose] public section

variable {α}

open TopologicalSpace
open Topology
open Set
open Set.Notation

section SemilatticeInf

variable [SemilatticeInf α]
namespace PrimitiveSpectrum

/--
Definition of `hull` / `hull` 的定义

English:
abbreviation hull
  signature: (T : Set α) (a : α)
  body: T ↓inter Ici a

中文:
缩写 hull
  签名: (T : 集合 α) (a : α)
  定义体: T ↓inter Ici a
-/
abbrev hull (T : Set α) (a : α) := T ↓inter Ici a

variable {T : Set α}

/--
lemma `hull_inf` / 引理 `hull_inf`

English:
lemma hull_inf
  given: (hT : forall p in T, InfPrime p) (a b : α)
  proof: by
  grind [InfPrime.inf_le]

中文:
引理 hull_inf
  条件: (hT : 对任意 p in T, InfPrime p) (a b : α)
  证明: by
  grind [InfPrime.inf_le]

Depends on / 依赖: InfPrime, InfPrime.inf_le, inf_le
-/
lemma hull_inf (hT : forall p in T, InfPrime p) (a b : α) :
    hull T (a ⊓ b) = hull T a union hull T b := by
  grind [InfPrime.inf_le]

variable [OrderTop α]

open Finset in
/--
lemma `hull_finsetInf` / 引理 `hull_finsetInf`

English:
lemma hull_finsetInf
  given: (hT : forall p in T, InfPrime p) (F : Finset α)
  proof: by
  rw [coe_upperClosure]
  induction F using Finset.cons_induction with
  | empty =>
    simp only [coe_empty, mem_empty_iff_false, iUnion_of_empty, iUnion_empty, Set.preimage_empty,
      inf_empty]
    by_contra hf
    rw [← Set.not_nonempty_iff_eq_empty]; rw [not_not] at hf
    obtain ⟨x, hx⟩ := hf
    exact (hT x (Subtype.coe_prop x)).1 (isMax_iff_eq_top.mpr (eq_top_iff.mpr hx))
  | cons a F' _ I4 => simp [hull_inf hT, I4]

中文:
引理 hull_finsetInf
  条件: (hT : 对任意 p in T, InfPrime p) (F : 有限集 α)
  证明: by
  rw [coe_upperClosure]
  induction F using Finset.cons_induction with
  | empty =>
    simp only [coe_empty, mem_empty_iff_false, iUnion_of_empty, iUnion_empty, Set.preimage_empty,
      inf_empty]
    by_contra hf
    rw [← Set.not_nonempty_iff_eq_empty]; rw [not_not] at hf
    obtain ⟨x, hx⟩ := hf
    exact (hT x (Subtype.coe_prop x)).1 (isMax_iff_eq_top.mpr (eq_top_iff.mpr hx))
  | cons a F' _ I4 => simp [hull_inf hT, I4]

Depends on / 依赖: Finset, Finset.cons_induction, Set.not_nonempty_iff_eq_empty, Set.preimage_empty, Subtype, Subtype.coe_prop, coe_empty, coe_prop, coe_upperClosure, cons_induction, eq_top_iff, eq_top_iff.mpr, hull_inf, iUnion_empty, iUnion_of_empty, inf_empty, isMax_iff_eq_top, isMax_iff_eq_top.mpr, mem_empty_iff_false, not_nonempty_iff_eq_empty
-/
lemma hull_finsetInf (hT : forall p in T, InfPrime p) (F : Finset α) :
    hull T (inf F id) = T ↓inter upperClosure (F : Set α) := by
  rw [coe_upperClosure]
  induction F using Finset.cons_induction with
  | empty =>
    simp only [coe_empty, mem_empty_iff_false, iUnion_of_empty, iUnion_empty, Set.preimage_empty,
      inf_empty]
    by_contra hf
    rw [← Set.not_nonempty_iff_eq_empty]; rw [not_not] at hf
    obtain ⟨x, hx⟩ := hf
    exact (hT x (Subtype.coe_prop x)).1 (isMax_iff_eq_top.mpr (eq_top_iff.mpr hx))
  | cons a F' _ I4 => simp [hull_inf hT, I4]

open Finset in
/--
lemma `preimage_upperClosure_compl_finset` / 引理 `preimage_upperClosure_compl_finset`

English:
lemma preimage_upperClosure_compl_finset
  given: (hT : forall p in T, InfPrime p) (F : Finset α)
  proof: by
  rw [Set.preimage_compl]; rw [(hull_finsetInf hT)]

中文:
引理 preimage_upperClosure_compl_finset
  条件: (hT : 对任意 p in T, InfPrime p) (F : 有限集 α)
  证明: by
  rw [Set.preimage_compl]; rw [(hull_finsetInf hT)]

Depends on / 依赖: Set.preimage_compl, hull_finsetInf, preimage_compl
-/
lemma preimage_upperClosure_compl_finset (hT : forall p in T, InfPrime p) (F : Finset α) :
    T ↓inter (upperClosure (F : Set α))ᶜ = (hull T (inf F id))ᶜ := by
  rw [Set.preimage_compl]; rw [(hull_finsetInf hT)]

variable [TopologicalSpace α] [IsLower α]

/--
lemma `isTopologicalBasis_relativeLower` / 引理 `isTopologicalBasis_relativeLower`

English:
lemma isTopologicalBasis_relativeLower
  given: (hT : forall p in T, InfPrime p)
  proof: by
  convert! isTopologicalBasis_subtype Topology.IsLower.isTopologicalBasis (· in T)
  ext R
  simp only [preimage_compl, mem_ofPred_eq, IsLower.lowerBasis, mem_image, exists_exists_and_eq_and]
  constructor <;> intro ha
  · obtain ⟨a, ha'⟩ := ha
    use {a}
    rw [← (Function.Injective.preimage_image Subtype.val_injective R)]; rw [← ha']
    simp only [finite_singleton, upperClosure_singleton, UpperSet.coe_Ici, image_val_compl,
      Subtype.image_preimage_coe, sdiff_self_inter, preimage_sdiff, Subtype.coe_preimage_self,
      true_and]
    exact compl_eq_univ_sdiff (Subtype.val ⁻¹' Ici a)
  · obtain ⟨F, hF⟩ := ha
    lift F to Finset α using hF.1
    use Finset.inf F id
    ext
    simp [hull_finsetInf hT, ← hF.2]

中文:
引理 isTopologicalBasis_relativeLower
  条件: (hT : 对任意 p in T, InfPrime p)
  证明: by
  convert! isTopologicalBasis_subtype Topology.IsLower.isTopologicalBasis (· in T)
  ext R
  simp only [preimage_compl, mem_ofPred_eq, IsLower.lowerBasis, mem_image, exists_exists_and_eq_and]
  constructor <;> intro ha
  · obtain ⟨a, ha'⟩ := ha
    use {a}
    rw [← (Function.Injective.preimage_image Subtype.val_injective R)]; rw [← ha']
    simp only [finite_singleton, upperClosure_singleton, UpperSet.coe_Ici, image_val_compl,
      Subtype.image_preimage_coe, sdiff_self_inter, preimage_sdiff, Subtype.coe_preimage_self,
      true_and]
    exact compl_eq_univ_sdiff (Subtype.val ⁻¹' Ici a)
  · obtain ⟨F, hF⟩ := ha
    lift F to Finset α using hF.1
    use Finset.inf F id
    ext
    simp [hull_finsetInf hT, ← hF.2]

Depends on / 依赖: Function, Function.Injective.preimage_image, Injective, IsLower, IsLower.lowerBasis, Subtype, Subtype.coe_preimage_self, Subtype.image_preimage_coe, Subtype.val_injective, Topology, Topology.IsLower.isTopologicalBasis, UpperSet, UpperSet.coe_Ici, coe_Ici, coe_preimage_self, convert, exists_exists_and_eq_and, finite_singleton, image_preimage_coe, image_val_compl
-/
lemma isTopologicalBasis_relativeLower (hT : forall p in T, InfPrime p) :
    IsTopologicalBasis { S : Set T | exists (a : α), (hull T a)ᶜ = S } := by
  convert! isTopologicalBasis_subtype Topology.IsLower.isTopologicalBasis (· in T)
  ext R
  simp only [preimage_compl, mem_ofPred_eq, IsLower.lowerBasis, mem_image, exists_exists_and_eq_and]
  constructor <;> intro ha
  · obtain ⟨a, ha'⟩ := ha
    use {a}
    rw [← (Function.Injective.preimage_image Subtype.val_injective R)]; rw [← ha']
    simp only [finite_singleton, upperClosure_singleton, UpperSet.coe_Ici, image_val_compl,
      Subtype.image_preimage_coe, sdiff_self_inter, preimage_sdiff, Subtype.coe_preimage_self,
      true_and]
    exact compl_eq_univ_sdiff (Subtype.val ⁻¹' Ici a)
  · obtain ⟨F, hF⟩ := ha
    lift F to Finset α using hF.1
    use Finset.inf F id
    ext
    simp [hull_finsetInf hT, ← hF.2]

end PrimitiveSpectrum

end SemilatticeInf

namespace PrimitiveSpectrum
variable [CompleteLattice α] {T : Set α}

universe v

/--
lemma `hull_iSup` / 引理 `hull_iSup`

English:
lemma hull_iSup
  given: {ι : Sort v} (s : ι -> α)
  statement: hull T (iSup s) = ⋂ i, hull T (s i)
  proof: by aesop

中文:
引理 hull_iSup
  条件: {ι : 类型层 v} (s : ι -> α)
  结论: hull T (iSup s) = ⋂ i, hull T (s i)
  证明: by aesop
-/
lemma hull_iSup {ι : Sort v} (s : ι -> α) : hull T (iSup s) = ⋂ i, hull T (s i) := by aesop

/--
lemma `hull_sSup` / 引理 `hull_sSup`

English:
lemma hull_sSup
  given: (S : Set α)
  statement: hull T (sSup S) = ⋂₀ { hull T a | a in S }
  proof: by aesop

中文:
引理 hull_sSup
  条件: (S : 集合 α)
  结论: hull T (sSup S) = ⋂₀ { hull T a | a in S }
  证明: by aesop
-/
lemma hull_sSup (S : Set α) : hull T (sSup S) = ⋂₀ { hull T a | a in S } := by aesop

/--
lemma `isOpen_iff` / 引理 `isOpen_iff`

English:
lemma isOpen_iff
  statement: [TopologicalSpace α] [IsLower α] (hT : forall p in T, InfPrime p)
  proof: by
  constructor <;> intro h
  · let R := {a : α | (hull T a)ᶜ subseteq S}
    use sSup R
    rw [IsTopologicalBasis.open_eq_sUnion' (isTopologicalBasis_relativeLower hT) h]
    aesop
  · obtain ⟨a, ha⟩ := h
    exact ⟨(Ici a)ᶜ, isClosed_Ici.isOpen_compl, ha.symm⟩

中文:
引理 isOpen_iff
  结论: [拓扑空间 α] [是Lower α] (hT : 对任意 p in T, InfPrime p)
  证明: by
  constructor <;> intro h
  · let R := {a : α | (hull T a)ᶜ subseteq S}
    use sSup R
    rw [IsTopologicalBasis.open_eq_sUnion' (isTopologicalBasis_relativeLower hT) h]
    aesop
  · obtain ⟨a, ha⟩ := h
    exact ⟨(Ici a)ᶜ, isClosed_Ici.isOpen_compl, ha.symm⟩

Depends on / 依赖: IsTopologicalBasis, IsTopologicalBasis.open_eq_sUnion, ha.symm, isClosed_Ici, isClosed_Ici.isOpen_compl, isOpen_compl, isTopologicalBasis_relativeLower, open_eq_sUnion, subseteq
-/
lemma isOpen_iff [TopologicalSpace α] [IsLower α] (hT : forall p in T, InfPrime p)
    (S : Set T) : IsOpen S ↔ exists (a : α), S = (hull T a)ᶜ := by
  constructor <;> intro h
  · let R := {a : α | (hull T a)ᶜ subseteq S}
    use sSup R
    rw [IsTopologicalBasis.open_eq_sUnion' (isTopologicalBasis_relativeLower hT) h]
    aesop
  · obtain ⟨a, ha⟩ := h
    exact ⟨(Ici a)ᶜ, isClosed_Ici.isOpen_compl, ha.symm⟩

/--
lemma `isClosed_iff` / 引理 `isClosed_iff`

English:
lemma isClosed_iff
  statement: [TopologicalSpace α] [IsLower α] (hT : forall p in T, InfPrime p)
  proof: by
  simp only [← isOpen_compl_iff, isOpen_iff hT, compl_inj_iff]

中文:
引理 isClosed_iff
  结论: [拓扑空间 α] [是Lower α] (hT : 对任意 p in T, InfPrime p)
  证明: by
  simp only [← isOpen_compl_iff, isOpen_iff hT, compl_inj_iff]

Depends on / 依赖: compl_inj_iff, isOpen_compl_iff, isOpen_iff
-/
lemma isClosed_iff [TopologicalSpace α] [IsLower α] (hT : forall p in T, InfPrime p)
    {S : Set T} : IsClosed S ↔ exists (a : α), S = hull T a := by
  simp only [← isOpen_compl_iff, isOpen_iff hT, compl_inj_iff]

/--
Definition of `kernel` / `kernel` 的定义

English:
abbreviation kernel
  signature: (S : Set T)
  body: sInf (Subtype.val '' S)

中文:
缩写 kernel
  签名: (S : 集合 T)
  定义体: sInf (Subtype.val '' S)

Depends on / 依赖: Subtype, Subtype.val
-/
abbrev kernel (S : Set T) := sInf (Subtype.val '' S)

open OrderDual in
/--
theorem `gc` / 定理 `gc`

English:
theorem gc
  statement: GaloisConnection (α := Set T) (β := αᵒᵈ)
  proof: fun S a => by
  simp [Set.subset_def]

中文:
定理 gc
  结论: GaloisConnection (α := 集合 T) (β := αᵒᵈ)
  证明: fun S a => by
  simp [Set.subset_def]
-/
theorem gc : GaloisConnection (α := Set T) (β := αᵒᵈ)
    (fun S => toDual (kernel S)) (fun a => hull T (ofDual a)) := fun S a => by
  simp [Set.subset_def]

/--
lemma `gc_closureOperator` / 引理 `gc_closureOperator`

English:
lemma gc_closureOperator
  given: (S : Set T)
  statement: gc.closureOperator S = hull T (kernel S)
  proof: by
  simp only [toDual_sInf, GaloisConnection.closureOperator_apply, ofDual_sSup]
  rw [← preimage_comp]; rw [← OrderDual.toDual_symm_eq]; rw [Equiv.symm_comp_self]; rw [preimage_id_eq]; rw [id_eq]

中文:
引理 gc_closureOperator
  条件: (S : 集合 T)
  结论: gc.closureOperator S = hull T (kernel S)
  证明: by
  simp only [toDual_sInf, GaloisConnection.closureOperator_apply, ofDual_sSup]
  rw [← preimage_comp]; rw [← OrderDual.toDual_symm_eq]; rw [Equiv.symm_comp_self]; rw [preimage_id_eq]; rw [id_eq]

Depends on / 依赖: Equiv.symm_comp_self, GaloisConnection, GaloisConnection.closureOperator_apply, OrderDual, OrderDual.toDual_symm_eq, closureOperator_apply, id_eq, ofDual_sSup, preimage_comp, preimage_id_eq, symm_comp_self, toDual_sInf, toDual_symm_eq
-/
lemma gc_closureOperator (S : Set T) : gc.closureOperator S = hull T (kernel S) := by
  simp only [toDual_sInf, GaloisConnection.closureOperator_apply, ofDual_sSup]
  rw [← preimage_comp]; rw [← OrderDual.toDual_symm_eq]; rw [Equiv.symm_comp_self]; rw [preimage_id_eq]; rw [id_eq]

variable (T)

/--
Definition of `OrderGenerates` / `OrderGenerates` 的定义

English:
definition OrderGenerates
  body: forall (a : α), exists (S : Set T), a = kernel S

中文:
定义 OrderGenerates
  定义体: forall (a : α), exists (S : Set T), a = kernel S

Depends on / 依赖: kernel
-/
def OrderGenerates := forall (a : α), exists (S : Set T), a = kernel S

variable {T}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: (hG : OrderGenerates T)
  body: gc.toGaloisInsertion fun a => by
    obtain ⟨S, rfl⟩ := hG a
    rw [OrderDual.le_toDual]; rw [kernel]; rw [kernel]
exact sInf_le_sInf image_val_mono fun c hcS => by
      rw [hull]; rw [mem_preimage]; rw [mem_Ici]
      exact sInf_le (mem_image_of_mem Subtype.val hcS)

中文:
定义 gi
  签名: (hG : OrderGenerates T)
  定义体: gc.toGaloisInsertion fun a => by
    obtain ⟨S, rfl⟩ := hG a
    rw [OrderDual.le_toDual]; rw [kernel]; rw [kernel]
exact sInf_le_sInf image_val_mono fun c hcS => by
      rw [hull]; rw [mem_preimage]; rw [mem_Ici]
      exact sInf_le (mem_image_of_mem Subtype.val hcS)
-/
def gi (hG : OrderGenerates T) : GaloisInsertion (α := Set T) (β := αᵒᵈ)
    (OrderDual.toDual ∘ kernel)
    (hull T ∘ OrderDual.ofDual) :=
  gc.toGaloisInsertion fun a => by
    obtain ⟨S, rfl⟩ := hG a
    rw [OrderDual.le_toDual]; rw [kernel]; rw [kernel]
exact sInf_le_sInf image_val_mono fun c hcS => by
      rw [hull]; rw [mem_preimage]; rw [mem_Ici]
      exact sInf_le (mem_image_of_mem Subtype.val hcS)

/--
lemma `kernel_hull` / 引理 `kernel_hull`

English:
lemma kernel_hull
  given: (hG : OrderGenerates T) (a : α)
  statement: kernel (hull T a) = a
  proof: by
  conv_rhs => rw [← OrderDual.ofDual_toDual a, ← (gi hG).l_u_eq a]
  rfl

中文:
引理 kernel_hull
  条件: (hG : OrderGenerates T) (a : α)
  结论: kernel (hull T a) = a
  证明: by
  conv_rhs => rw [← OrderDual.ofDual_toDual a, ← (gi hG).l_u_eq a]
  rfl

Depends on / 依赖: OrderDual, OrderDual.ofDual_toDual, conv_rhs, l_u_eq, ofDual_toDual
-/
lemma kernel_hull (hG : OrderGenerates T) (a : α) : kernel (hull T a) = a := by
  conv_rhs => rw [← OrderDual.ofDual_toDual a, ← (gi hG).l_u_eq a]
  rfl

/--
lemma `hull_kernel_of_isClosed` / 引理 `hull_kernel_of_isClosed`

English:
lemma hull_kernel_of_isClosed
  statement: [TopologicalSpace α] [IsLower α]
  proof: by
  obtain ⟨a, ha⟩ := (isClosed_iff hT).mp h
  rw [ha]; rw [kernel_hull hG]

中文:
引理 hull_kernel_of_isClosed
  结论: [拓扑空间 α] [是Lower α]
  证明: by
  obtain ⟨a, ha⟩ := (isClosed_iff hT).mp h
  rw [ha]; rw [kernel_hull hG]

Depends on / 依赖: isClosed_iff, kernel_hull
-/
lemma hull_kernel_of_isClosed [TopologicalSpace α] [IsLower α]
    (hT : forall p in T, InfPrime p) (hG : OrderGenerates T) {C : Set T} (h : IsClosed C) :
    hull T (kernel C) = C := by
  obtain ⟨a, ha⟩ := (isClosed_iff hT).mp h
  rw [ha]; rw [kernel_hull hG]

/--
lemma `closedsGC_closureOperator` / 引理 `closedsGC_closureOperator`

English:
lemma closedsGC_closureOperator
  statement: [TopologicalSpace α] [IsLower α]
  proof: by
  simp only [GaloisConnection.closureOperator_apply, Closeds.coe_closure, closure, le_antisymm_iff]
  constructor
  · exact fun ⦃a⦄ a => a (hull T (kernel S)) ⟨(isClosed_iff hT).mpr ⟨kernel S, rfl⟩,
      image_subset_iff.mp (fun _ hbS => sInf_le hbS)⟩
  · simp_rw [subset_sInter_iff]
    intro R hR
    rw [← (hull_kernel_of_isClosed hT hG hR.1)]; rw [← gc_closureOperator]
    exact ClosureOperator.monotone _ hR.2

中文:
引理 closedsGC_closureOperator
  结论: [拓扑空间 α] [是Lower α]
  证明: by
  simp only [GaloisConnection.closureOperator_apply, Closeds.coe_closure, closure, le_antisymm_iff]
  constructor
  · exact fun ⦃a⦄ a => a (hull T (kernel S)) ⟨(isClosed_iff hT).mpr ⟨kernel S, rfl⟩,
      image_subset_iff.mp (fun _ hbS => sInf_le hbS)⟩
  · simp_rw [subset_sInter_iff]
    intro R hR
    rw [← (hull_kernel_of_isClosed hT hG hR.1)]; rw [← gc_closureOperator]
    exact ClosureOperator.monotone _ hR.2

Depends on / 依赖: Closeds, Closeds.coe_closure, ClosureOperator, ClosureOperator.monotone, GaloisConnection, GaloisConnection.closureOperator_apply, closure, closureOperator, closureOperator_apply, coe_closure, gc_closureOperator, hull_kernel_of_isClosed, image_subset_iff, image_subset_iff.mp, isClosed_iff, kernel, le_antisymm_iff, monotone, sInf_le, simp_rw
-/
lemma closedsGC_closureOperator [TopologicalSpace α] [IsLower α]
    (hT : forall p in T, InfPrime p) (hG : OrderGenerates T) (S : Set T) :
    (TopologicalSpace.Closeds.gc (α := T)).closureOperator S = hull T (kernel S) := by
  simp only [GaloisConnection.closureOperator_apply, Closeds.coe_closure, closure, le_antisymm_iff]
  constructor
  · exact fun ⦃a⦄ a => a (hull T (kernel S)) ⟨(isClosed_iff hT).mpr ⟨kernel S, rfl⟩,
      image_subset_iff.mp (fun _ hbS => sInf_le hbS)⟩
  · simp_rw [subset_sInter_iff]
    intro R hR
    rw [← (hull_kernel_of_isClosed hT hG hR.1)]; rw [← gc_closureOperator]
    exact ClosureOperator.monotone _ hR.2

end PrimitiveSpectrum
