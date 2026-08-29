/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Map
public import Mathlib.Order.Closure
public import Mathlib.Order.CompleteLatticeIntervals

/-!
# Matroid Closure

A flat (`IsFlat`) of a matroid `M` is a combinatorial analogue of a subspace of a vector space,
and is defined to be a subset `F` of the ground set of `M` such that for each basis
`I` for `F`, every set having `I` as a basis is contained in `F`.

The *closure* of a set `X` in a matroid `M` is the intersection of all flats of `M` containing `X`.
This is a combinatorial analogue of the linear span of a set of vectors.

For `M : Matroid α`, this file defines a predicate `M.IsFlat : Set α → Prop` and a function
`M.closure : Set α → Set α` corresponding to these notions, and develops API for the latter.
API for `Matroid.IsFlat` will appear in another file; we include the definition here since
it is used in the definition of `Matroid.closure`.

We also define a predicate `Spanning`, to describe a set whose closure is the entire ground set.

## Main definitions

* For `M : Matroid α` and `F : Set α`, `M.IsFlat F` means that `F` is an isFlat of `M`.
* For `M : Matroid α` and `X : Set α`, `M.closure X` is the closure of `X` in `M`.
* For `M : Matroid α` and `X : ↑(Iic M.E)` (i.e. a bundled subset of `M.E`),
  `M.subtypeClosure X` is the closure of `X`, viewed as a term in `↑(Iic M.E)`.
  This is a `ClosureOperator` on `↑(Iic M.E)`.
* For `M : Matroid α` and `S ⊆ M.E`, `M.Spanning S` means that `S` has closure equal to `M.E`,
  or equivalently that `S` contains an isBase of `M`.

## Implementation details

If `X : Set α` satisfies `X ⊆ M.E`, then it is clear how `M.closure X` should be defined.
But `M.closure X` also needs to be defined for all `X : Set α`,
so a convention is needed for how it handles sets containing junk elements outside `M.E`.
All such choices come with tradeoffs. Provided that `M.closure X` has already been defined
for `X ⊆ M.E`, the two best candidates for extending it to all `X` seem to be:

(1) The function for which `M.closure X = M.closure (X ∩ M.E)` for all `X : Set α`

(2) The function for which `M.closure X = M.closure (X ∩ M.E) ∪ X` for all `X : Set α`

For both options, the function `closure` is monotone and idempotent with no assumptions on `X`.

Choice (1) has the advantage that `M.closure X ⊆ M.E` holds for all `X` without the assumption
that `X ⊆ M.E`, which is very nice for `aesop_mat`. It is also fairly convenient to rewrite
`M.closure X` to `M.closure (X ∩ M.E)` when one needs to work with a subset of the ground set.
Its disadvantage is that the statement `X ⊆ M.closure X` is only true provided that `X ⊆ M.E`.

Choice (2) has the reverse property: we would have `X ⊆ M.closure X` for all `X`,
but the condition `M.closure X ⊆ M.E` requires `X ⊆ M.E` to hold.
It has a couple of other advantages too: it is actually the closure function of a matroid on `α`
with ground set `univ` (specifically, the direct sum of `M` and a free matroid on `M.Eᶜ`),
and because of this, it is an example of a `ClosureOperator` on `α`, which in turn gives access
to nice existing API for both `ClosureOperator` and `GaloisInsertion`.
This also relates to flats; `F ⊆ M.E ∧ ClosureOperator.IsClosed F` is equivalent to `M.IsFlat F`.
(All of this fails for choice (1), since `X ⊆ M.closure X` is required for
a `ClosureOperator`, but isn't true for non-subsets of `M.E`)

The API that choice (2) would offer is very beguiling, but after extensive experimentation in
an external repo, it seems that (1) is far less rough around the edges in practice,
so we go with (1). It may be helpful at some point to define a primed version
`Matroid.closure' : ClosureOperator (Set α)` corresponding to choice (2).
Failing that, the `ClosureOperator`/`GaloisInsertion` API is still available on
the subtype `↑(Iic M.E)` via `Matroid.SubtypeClosure`, albeit less elegantly.

## Naming conventions

In lemma names, the words `spanning` and `isFlat` are used as suffixes,
for instance we have `ground_spanning` rather than `spanning_ground`.
-/

@[expose] public section

assert_not_exists Field

open Set
namespace Matroid

variable {ι α : Type*} {M : Matroid α} {F X Y : Set α} {e f : α}

section IsFlat

/-- A flat is a maximal set having a given basis -/
@[mk_iff]
/--
Definition of `IsFlat` / `IsFlat` 的定义

English:
structure IsFlat
  parameters: (M : Matroid α) (F : Set α)
  axioms and operations (2):
    - subset_of_isBasis_of_isBasis : forall ⦃I X⦄, M.IsBasis I F -> M.IsBasis I X -> X subseteq F
    - subset_ground : F subseteq M.E

中文:
结构 是平坦
  参数: (M : 拟阵 α) (F : 集合 α)
  公理与运算 (2 个):
    - subset_of_isBasis_of_isBasis : 对任意 ⦃I X⦄, M.是基 I F -> M.是基 I X -> X subseteq F
    - subset_ground : F subseteq M.E

Depends on / 依赖: IsFlat, IsFlat.subset_ground, Matroid, subset_ground
-/
structure IsFlat (M : Matroid α) (F : Set α) : Prop where
  subset_of_isBasis_of_isBasis : forall ⦃I X⦄, M.IsBasis I F -> M.IsBasis I X -> X subseteq F
  subset_ground : F subseteq M.E

attribute [aesop unsafe 20% (rule_sets := [Matroid])] IsFlat.subset_ground

/--
lemma `ground_isFlat` / 引理 `ground_isFlat`

English:
lemma ground_isFlat
  given: (M : Matroid α)
  statement: M.IsFlat M.E
  proof: ⟨fun _ _ _ => IsBasis.subset_ground, Subset.rfl⟩

中文:
引理 ground_isFlat
  条件: (M : 拟阵 α)
  结论: M.是平坦 M.E
  证明: ⟨fun _ _ _ => IsBasis.subset_ground, Subset.rfl⟩
-/
@[simp] lemma ground_isFlat (M : Matroid α) : M.IsFlat M.E :=
  ⟨fun _ _ _ => IsBasis.subset_ground, Subset.rfl⟩

/--
lemma `IsFlat.iInter` / 引理 `IsFlat.iInter`

English:
lemma IsFlat.iInter
  statement: {ι : Type*} [Nonempty ι] {Fs : ι -> Set α}
  proof: by
  refine ⟨fun I X hI hIX => subset_iInter fun i => ?_,
    (iInter_subset _ (Classical.arbitrary _)).trans (hFs _).subset_ground⟩
  obtain ⟨J, hIJ, hJ⟩ := hI.indep.subset_isBasis_of_subset (hI.subset.trans (iInter_subset _ i))
  refine subset_union_right.trans ((hFs i).1 (X := Fs i union X) hIJ ?

中文:
引理 是平坦.i整数er
  结论: {ι : 类型} [非空 ι] {Fs : ι -> 集合 α}
  证明: by
  refine ⟨fun I X hI hIX => subset_iInter fun i => ?_,
    (iInter_subset _ (Classical.arbitrary _)).trans (hFs _).subset_ground⟩
  obtain ⟨J, hIJ, hJ⟩ := hI.indep.subset_isBasis_of_subset (hI.subset.trans (iInter_subset _ i))
  refine subset_union_right.trans ((hFs i).1 (X := Fs i union X) hIJ ?

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, convert, hI.indep.subset_isBasis_of_subset, hI.subset.trans, hIJ.indep, hIJ.isBasis_union, hIJ.subset, hIX.isBasis_union_of_subset, iInter_subset, isBasis_union, isBasis_union_of_subset, subset, subset_ground, subset_iInter, subset_isBasis_of_subset, subset_union_right, subset_union_right.trans, union_assoc
-/
lemma IsFlat.iInter {ι : Type*} [Nonempty ι] {Fs : ι -> Set α}
    (hFs : forall i, M.IsFlat (Fs i)) : M.IsFlat (⋂ i, Fs i) := by
  refine ⟨fun I X hI hIX => subset_iInter fun i => ?_,
    (iInter_subset _ (Classical.arbitrary _)).trans (hFs _).subset_ground⟩
  obtain ⟨J, hIJ, hJ⟩ := hI.indep.subset_isBasis_of_subset (hI.subset.trans (iInter_subset _ i))
  refine subset_union_right.trans ((hFs i).1 (X := Fs i union X) hIJ ?_)
  convert! hIJ.isBasis_union (hIX.isBasis_union_of_subset hIJ.indep hJ) using 1
  rw [← union_assoc]; rw [union_eq_self_of_subset_right hIJ.subset]

/--
Definition of `subtypeClosure` / `subtypeClosure` 的定义

English:
definition subtypeClosure
  signature: (M : Matroid α)
  body: ClosureOperator.ofCompletePred (fun F => M.IsFlat F.1) fun s hs => by
    obtain (rfl | hne) := s.eq_empty_or_nonempty
    · simp
    have _ := hne.coe_sort
    convert! IsFlat.iInter (M := M) (Fs := fun (F : s) => F.1.1) (fun F => hs F.1 F.2)
    ext
    aesop

中文:
定义 subtypeClosure
  签名: (M : 拟阵 α)
  定义体: ClosureOperator.ofCompletePred (fun F => M.IsFlat F.1) fun s hs => by
    obtain (rfl | hne) := s.eq_empty_or_nonempty
    · simp
    have _ := hne.coe_sort
    convert! IsFlat.iInter (M := M) (Fs := fun (F : s) => F.1.1) (fun F => hs F.1 F.2)
    ext
    aesop

Depends on / 依赖: ClosureOperator, ClosureOperator.ofCompletePred, IsFlat, IsFlat.iInter, M.IsFlat, coe_sort, convert, eq_empty_or_nonempty, hne.coe_sort, iInter, ofCompletePred, s.eq_empty_or_nonempty
-/
def subtypeClosure (M : Matroid α) : ClosureOperator (Iic M.E) :=
  ClosureOperator.ofCompletePred (fun F => M.IsFlat F.1) fun s hs => by
    obtain (rfl | hne) := s.eq_empty_or_nonempty
    · simp
    have _ := hne.coe_sort
    convert! IsFlat.iInter (M := M) (Fs := fun (F : s) => F.1.1) (fun F => hs F.1 F.2)
    ext
    aesop

/--
lemma `isFlat_iff_isClosed` / 引理 `isFlat_iff_isClosed`

English:
lemma isFlat_iff_isClosed
  statement: M.IsFlat F ↔ exists h : F subseteq M.E, M.subtypeClosure.IsClosed ⟨F, h⟩
  proof: by
  simpa [subtypeClosure] using IsFlat.subset_ground

中文:
引理 isFlat_iff_isClosed
  结论: M.是平坦 F ↔ 存在 h : F subseteq M.E, M.subtypeClosure.是闭集 ⟨F, h⟩
  证明: by
  simpa [subtypeClosure] using IsFlat.subset_ground

Depends on / 依赖: IsFlat, IsFlat.subset_ground, subset_ground, subtypeClosure
-/
lemma isFlat_iff_isClosed : M.IsFlat F ↔ exists h : F subseteq M.E, M.subtypeClosure.IsClosed ⟨F, h⟩ := by
  simpa [subtypeClosure] using IsFlat.subset_ground

/--
lemma `isClosed_iff_isFlat` / 引理 `isClosed_iff_isFlat`

English:
lemma isClosed_iff_isFlat
  given: {F : Iic M.E}
  statement: M.subtypeClosure.IsClosed F ↔ M.IsFlat F
  proof: by
  simp [subtypeClosure]

中文:
引理 isClosed_iff_isFlat
  条件: {F : 左无界右闭区间 M.E}
  结论: M.subtypeClosure.是闭集 F ↔ M.是平坦 F
  证明: by
  simp [subtypeClosure]

Depends on / 依赖: subtypeClosure
-/
lemma isClosed_iff_isFlat {F : Iic M.E} : M.subtypeClosure.IsClosed F ↔ M.IsFlat F := by
  simp [subtypeClosure]

end IsFlat

/--
Definition of `closure` / `closure` 的定义

English:
definition closure
  signature: (M : Matroid α) (X : Set α)
  body: ⋂₀ {F | M.IsFlat F ∧ X inter M.E subseteq F}

中文:
定义 closure
  签名: (M : 拟阵 α) (X : 集合 α)
  定义体: ⋂₀ {F | M.IsFlat F ∧ X inter M.E subseteq F}

Depends on / 依赖: IsFlat, M.IsFlat, subseteq
-/
def closure (M : Matroid α) (X : Set α) : Set α := ⋂₀ {F | M.IsFlat F ∧ X inter M.E subseteq F}

/--
lemma `closure_def` / 引理 `closure_def`

English:
lemma closure_def
  given: (M : Matroid α) (X : Set α)
  statement: M.closure X = ⋂₀ {F | M.IsFlat F ∧ X inter M.E subseteq F}
  proof: rfl

中文:
引理 closure_def
  条件: (M : 拟阵 α) (X : 集合 α)
  结论: M.closure X = ⋂₀ {F | M.是平坦 F ∧ X inter M.E subseteq F}
  证明: rfl
-/
lemma closure_def (M : Matroid α) (X : Set α) : M.closure X = ⋂₀ {F | M.IsFlat F ∧ X inter M.E subseteq F} :=
  rfl

/--
lemma `closure_def'` / 引理 `closure_def'`

English:
lemma closure_def'
  given: (M : Matroid α) (X : Set α) (hX : X subseteq M.E := by aesop_mat)
  proof: by
  rw [closure]; rw [inter_eq_self_of_subset_left hX]

中文:
引理 closure_def'
  条件: (M : 拟阵 α) (X : 集合 α) (hX : X subseteq M.E := by aesop_mat)
  证明: by
  rw [closure]; rw [inter_eq_self_of_subset_left hX]

Depends on / 依赖: IsFlat, M.IsFlat, M.closure, aesop_mat, closure, inter_eq_self_of_subset_left, subseteq
-/
lemma closure_def' (M : Matroid α) (X : Set α) (hX : X subseteq M.E := by aesop_mat) :
    M.closure X = ⋂₀ {F | M.IsFlat F ∧ X subseteq F} := by
  rw [closure]; rw [inter_eq_self_of_subset_left hX]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nonempty {F | M.IsFlat F ∧ X inter M.E subseteq F}
  body: ⟨M.E, M.ground_isFlat, inter_subset_right⟩

中文:
实例 :
  签名: 非空 {F | M.是平坦 F ∧ X inter M.E subseteq F}
  定义体: ⟨M.E, M.ground_isFlat, inter_subset_right⟩

Depends on / 依赖: M.ground_isFlat, ground_isFlat, inter_subset_right
-/
instance : Nonempty {F | M.IsFlat F ∧ X inter M.E subseteq F} := ⟨M.E, M.ground_isFlat, inter_subset_right⟩

/--
lemma `closure_eq_subtypeClosure` / 引理 `closure_eq_subtypeClosure`

English:
lemma closure_eq_subtypeClosure
  given: (M : Matroid α) (X : Set α)
  proof: by
  suffices forall (x : α), (forall (t : Set α), M.IsFlat t -> X inter M.E subseteq t -> x in t) ↔
    (x in M.E ∧ forall a subseteq M.E, X inter M.E subseteq a -> M.IsFlat a -> x in a) by
    simpa [closure, subtypeClosure, Set.ext_iff]
  exact fun x => ⟨fun h => ⟨h _ M.ground_isFlat inter_subset

中文:
引理 closure_eq_subtypeClosure
  条件: (M : 拟阵 α) (X : 集合 α)
  证明: by
  suffices forall (x : α), (forall (t : Set α), M.IsFlat t -> X inter M.E subseteq t -> x in t) ↔
    (x in M.E ∧ forall a subseteq M.E, X inter M.E subseteq a -> M.IsFlat a -> x in a) by
    simpa [closure, subtypeClosure, Set.ext_iff]
  exact fun x => ⟨fun h => ⟨h _ M.ground_isFlat inter_subset

Depends on / 依赖: IsFlat, M.IsFlat, M.ground_isFlat, Set.ext_iff, closure, ext_iff, ground_isFlat, hF.subset_ground, inter_subset_right, subset_ground, subseteq, subtypeClosure
-/
lemma closure_eq_subtypeClosure (M : Matroid α) (X : Set α) :
    M.closure X = M.subtypeClosure ⟨X inter M.E, inter_subset_right⟩ := by
  suffices forall (x : α), (forall (t : Set α), M.IsFlat t -> X inter M.E subseteq t -> x in t) ↔
    (x in M.E ∧ forall a subseteq M.E, X inter M.E subseteq a -> M.IsFlat a -> x in a) by
    simpa [closure, subtypeClosure, Set.ext_iff]
  exact fun x => ⟨fun h => ⟨h _ M.ground_isFlat inter_subset_right, fun F _ hXF hF => h F hF hXF⟩,
    fun ⟨_, h⟩ F hF hXF => h F hF.subset_ground hXF hF⟩

@[aesop unsafe 10% (rule_sets := [Matroid])]
/--
lemma `closure_subset_ground` / 引理 `closure_subset_ground`

English:
lemma closure_subset_ground
  given: (M : Matroid α) (X : Set α)
  statement: M.closure X subseteq M.E
  proof: sInter_subset_of_mem ⟨M.ground_isFlat, inter_subset_right⟩

中文:
引理 closure_subset_ground
  条件: (M : 拟阵 α) (X : 集合 α)
  结论: M.closure X subseteq M.E
  证明: sInter_subset_of_mem ⟨M.ground_isFlat, inter_subset_right⟩

Depends on / 依赖: M.ground_isFlat, ground_isFlat, inter_subset_right, sInter_subset_of_mem
-/
lemma closure_subset_ground (M : Matroid α) (X : Set α) : M.closure X subseteq M.E :=
  sInter_subset_of_mem ⟨M.ground_isFlat, inter_subset_right⟩

/--
lemma `ground_subset_closure_iff` / 引理 `ground_subset_closure_iff`

English:
lemma ground_subset_closure_iff
  statement: M.E subseteq M.closure X ↔ M.closure X = M.E
  proof: by
  simp [M.closure_subset_ground X, subset_antisymm_iff]

中文:
引理 ground_subset_closure_iff
  结论: M.E subseteq M.closure X ↔ M.closure X = M.E
  证明: by
  simp [M.closure_subset_ground X, subset_antisymm_iff]
-/
@[simp] lemma ground_subset_closure_iff : M.E subseteq M.closure X ↔ M.closure X = M.E := by
  simp [M.closure_subset_ground X, subset_antisymm_iff]

/--
lemma `closure_inter_ground` / 引理 `closure_inter_ground`

English:
lemma closure_inter_ground
  given: (M : Matroid α) (X : Set α)
  proof: by
  simp_rw [closure_def, inter_assoc, inter_self]

中文:
引理 closure_inter_ground
  条件: (M : 拟阵 α) (X : 集合 α)
  证明: by
  simp_rw [closure_def, inter_assoc, inter_self]
-/
@[simp] lemma closure_inter_ground (M : Matroid α) (X : Set α) :
    M.closure (X inter M.E) = M.closure X := by
  simp_rw [closure_def, inter_assoc, inter_self]

/--
lemma `inter_ground_subset_closure` / 引理 `inter_ground_subset_closure`

English:
lemma inter_ground_subset_closure
  given: (M : Matroid α) (X : Set α)
  statement: X inter M.E subseteq M.closure X
  proof: by
  simp_rw [closure_def, subset_sInter_iff]; simp

中文:
引理 inter_ground_subset_closure
  条件: (M : 拟阵 α) (X : 集合 α)
  结论: X inter M.E subseteq M.closure X
  证明: by
  simp_rw [closure_def, subset_sInter_iff]; simp

Depends on / 依赖: closure_def, simp_rw, subset_sInter_iff
-/
lemma inter_ground_subset_closure (M : Matroid α) (X : Set α) : X inter M.E subseteq M.closure X := by
  simp_rw [closure_def, subset_sInter_iff]; simp

/--
lemma `mem_closure_iff_forall_mem_isFlat` / 引理 `mem_closure_iff_forall_mem_isFlat`

English:
lemma mem_closure_iff_forall_mem_isFlat
  given: (X : Set α) (hX : X subseteq M.E := by aesop_mat)
  proof: by
  simp_rw [M.closure_def' X, mem_sInter, mem_ofPred, and_imp]

中文:
引理 mem_closure_iff_对任意_mem_isFlat
  条件: (X : 集合 α) (hX : X subseteq M.E := by aesop_mat)
  证明: by
  simp_rw [M.closure_def' X, mem_sInter, mem_ofPred, and_imp]

Depends on / 依赖: IsFlat, M.IsFlat, M.closure, M.closure_def, aesop_mat, and_imp, closure, closure_def, mem_ofPred, mem_sInter, simp_rw, subseteq
-/
lemma mem_closure_iff_forall_mem_isFlat (X : Set α) (hX : X subseteq M.E := by aesop_mat) :
    e in M.closure X ↔ forall F, M.IsFlat F -> X subseteq F -> e in F := by
  simp_rw [M.closure_def' X, mem_sInter, mem_ofPred, and_imp]

/--
lemma `subset_closure_iff_forall_subset_isFlat` / 引理 `subset_closure_iff_forall_subset_isFlat`

English:
lemma subset_closure_iff_forall_subset_isFlat
  given: (X : Set α) (hX : X subseteq M.E := by aesop_mat)
  proof: by
  simp_rw [M.closure_def' X, subset_sInter_iff, mem_ofPred, and_imp]

中文:
引理 subset_closure_iff_对任意_subset_isFlat
  条件: (X : 集合 α) (hX : X subseteq M.E := by aesop_mat)
  证明: by
  simp_rw [M.closure_def' X, subset_sInter_iff, mem_ofPred, and_imp]

Depends on / 依赖: IsFlat, M.IsFlat, M.closure, M.closure_def, aesop_mat, and_imp, closure, closure_def, mem_ofPred, simp_rw, subset_sInter_iff, subseteq
-/
lemma subset_closure_iff_forall_subset_isFlat (X : Set α) (hX : X subseteq M.E := by aesop_mat) :
    Y subseteq M.closure X ↔ forall F, M.IsFlat F -> X subseteq F -> Y subseteq F := by
  simp_rw [M.closure_def' X, subset_sInter_iff, mem_ofPred, and_imp]

/--
lemma `subset_closure` / 引理 `subset_closure`

English:
lemma subset_closure
  given: (M : Matroid α) (X : Set α) (hX : X subseteq M.E := by aesop_mat)
  proof: by
  simp [M.closure_def' X, subset_sInter_iff]

中文:
引理 subset_closure
  条件: (M : 拟阵 α) (X : 集合 α) (hX : X subseteq M.E := by aesop_mat)
  证明: by
  simp [M.closure_def' X, subset_sInter_iff]

Depends on / 依赖: M.closure, M.closure_def, aesop_mat, closure, closure_def, subset_sInter_iff, subseteq
-/
lemma subset_closure (M : Matroid α) (X : Set α) (hX : X subseteq M.E := by aesop_mat) :
    X subseteq M.closure X := by
  simp [M.closure_def' X, subset_sInter_iff]

/--
lemma `IsFlat.closure` / 引理 `IsFlat.closure`

English:
lemma IsFlat.closure
  given: (hF : M.IsFlat F)
  statement: M.closure F = F
  proof: (sInter_subset_of_mem (by simpa)).antisymm (M.subset_closure F)

中文:
引理 是平坦.closure
  条件: (hF : M.是平坦 F)
  结论: M.closure F = F
  证明: (sInter_subset_of_mem (by simpa)).antisymm (M.subset_closure F)

Depends on / 依赖: M.subset_closure, antisymm, sInter_subset_of_mem, subset_closure
-/
lemma IsFlat.closure (hF : M.IsFlat F) : M.closure F = F :=
  (sInter_subset_of_mem (by simpa)).antisymm (M.subset_closure F)

variable (X) in
/--
lemma `isFlat_closure` / 引理 `isFlat_closure`

English:
lemma isFlat_closure
  statement: M.IsFlat (M.closure X)
  proof: by
  rw [closure]; rw [sInter_eq_iInter]; exact .iInter (·.2.1)

中文:
引理 isFlat_closure
  结论: M.是平坦 (M.closure X)
  证明: by
  rw [closure]; rw [sInter_eq_iInter]; exact .iInter (·.2.1)
-/
@[simp] lemma isFlat_closure : M.IsFlat (M.closure X) := by
  rw [closure]; rw [sInter_eq_iInter]; exact .iInter (·.2.1)

/--
lemma `isFlat_iff_closure_eq` / 引理 `isFlat_iff_closure_eq`

English:
lemma isFlat_iff_closure_eq
  statement: M.IsFlat F ↔ M.closure F = F
  proof: ⟨(·.closure), (· ▸ isFlat_closure F)⟩

中文:
引理 isFlat_iff_closure_eq
  结论: M.是平坦 F ↔ M.closure F = F
  证明: ⟨(·.closure), (· ▸ isFlat_closure F)⟩

Depends on / 依赖: closure, isFlat_closure
-/
lemma isFlat_iff_closure_eq : M.IsFlat F ↔ M.closure F = F := ⟨(·.closure), (· ▸ isFlat_closure F)⟩

/--
lemma `closure_ground` / 引理 `closure_ground`

English:
lemma closure_ground
  given: (M : Matroid α)
  statement: M.closure M.E = M.E
  proof: (M.closure_subset_ground M.E).antisymm (M.subset_closure M.E)

中文:
引理 closure_ground
  条件: (M : 拟阵 α)
  结论: M.closure M.E = M.E
  证明: (M.closure_subset_ground M.E).antisymm (M.subset_closure M.E)
-/
@[simp] lemma closure_ground (M : Matroid α) : M.closure M.E = M.E :=
  (M.closure_subset_ground M.E).antisymm (M.subset_closure M.E)

/--
lemma `closure_univ` / 引理 `closure_univ`

English:
lemma closure_univ
  given: (M : Matroid α)
  statement: M.closure univ = M.E
  proof: by
  rw [← closure_inter_ground]; rw [univ_inter]; rw [closure_ground]

@[gcongr]

中文:
引理 closure_univ
  条件: (M : 拟阵 α)
  结论: M.closure univ = M.E
  证明: by
  rw [← closure_inter_ground]; rw [univ_inter]; rw [closure_ground]

@[gcongr]
-/
@[simp] lemma closure_univ (M : Matroid α) : M.closure univ = M.E := by
  rw [← closure_inter_ground]; rw [univ_inter]; rw [closure_ground]

@[gcongr]
/--
lemma `closure_subset_closure` / 引理 `closure_subset_closure`

English:
lemma closure_subset_closure
  given: (M : Matroid α) (h : X subseteq Y)
  statement: M.closure X subseteq M.closure Y
  proof: subset_sInter (fun _ h' => sInter_subset_of_mem
    ⟨h'.1, subset_trans (inter_subset_inter_left _ h) h'.2⟩)

中文:
引理 closure_subset_closure
  条件: (M : 拟阵 α) (h : X subseteq Y)
  结论: M.closure X subseteq M.closure Y
  证明: subset_sInter (fun _ h' => sInter_subset_of_mem
    ⟨h'.1, subset_trans (inter_subset_inter_left _ h) h'.2⟩)

Depends on / 依赖: inter_subset_inter_left, sInter_subset_of_mem, subset_sInter, subset_trans
-/
lemma closure_subset_closure (M : Matroid α) (h : X subseteq Y) : M.closure X subseteq M.closure Y :=
  subset_sInter (fun _ h' => sInter_subset_of_mem
    ⟨h'.1, subset_trans (inter_subset_inter_left _ h) h'.2⟩)

/--
lemma `closure_mono` / 引理 `closure_mono`

English:
lemma closure_mono
  given: (M : Matroid α)
  statement: Monotone M.closure
  proof: fun _ _ => M.closure_subset_closure

中文:
引理 closure_mono
  条件: (M : 拟阵 α)
  结论: 递增 M.closure
  证明: fun _ _ => M.closure_subset_closure

Depends on / 依赖: M.closure_subset_closure, closure_subset_closure
-/
lemma closure_mono (M : Matroid α) : Monotone M.closure :=
  fun _ _ => M.closure_subset_closure

/--
lemma `closure_closure` / 引理 `closure_closure`

English:
lemma closure_closure
  given: (M : Matroid α) (X : Set α)
  statement: M.closure (M.closure X) = M.closure X
  proof: (M.subset_closure _).antisymm' (subset_sInter
    (fun F hF => (closure_subset_closure _ (sInter_subset_of_mem hF)).trans hF.1.closure.subset))

中文:
引理 closure_closure
  条件: (M : 拟阵 α) (X : 集合 α)
  结论: M.closure (M.closure X) = M.closure X
  证明: (M.subset_closure _).antisymm' (subset_sInter
    (fun F hF => (closure_subset_closure _ (sInter_subset_of_mem hF)).trans hF.1.closure.subset))
-/
@[simp] lemma closure_closure (M : Matroid α) (X : Set α) : M.closure (M.closure X) = M.closure X :=
  (M.subset_closure _).antisymm' (subset_sInter
    (fun F hF => (closure_subset_closure _ (sInter_subset_of_mem hF)).trans hF.1.closure.subset))

/--
lemma `closure_subset_closure_of_subset_closure` / 引理 `closure_subset_closure_of_subset_closure`

English:
lemma closure_subset_closure_of_subset_closure
  given: (hXY : X subseteq M.closure Y)
  proof: (M.closure_subset_closure hXY).trans_eq (M.closure_closure Y)

中文:
引理 closure_subset_closure_of_subset_closure
  条件: (hXY : X subseteq M.closure Y)
  证明: (M.closure_subset_closure hXY).trans_eq (M.closure_closure Y)

Depends on / 依赖: M.closure_closure, M.closure_subset_closure, closure_closure, closure_subset_closure, trans_eq
-/
lemma closure_subset_closure_of_subset_closure (hXY : X subseteq M.closure Y) :
    M.closure X subseteq M.closure Y :=
  (M.closure_subset_closure hXY).trans_eq (M.closure_closure Y)

/--
lemma `closure_subset_closure_iff_subset_closure` / 引理 `closure_subset_closure_iff_subset_closure`

English:
lemma closure_subset_closure_iff_subset_closure
  given: (hX : X subseteq M.E := by aesop_mat)
  proof: ⟨(M.subset_closure X).trans, closure_subset_closure_of_subset_closure⟩

中文:
引理 closure_subset_closure_iff_subset_closure
  条件: (hX : X subseteq M.E := by aesop_mat)
  证明: ⟨(M.subset_closure X).trans, closure_subset_closure_of_subset_closure⟩

Depends on / 依赖: M.closure, M.subset_closure, aesop_mat, closure, closure_subset_closure_of_subset_closure, subset_closure, subseteq
-/
lemma closure_subset_closure_iff_subset_closure (hX : X subseteq M.E := by aesop_mat) :
    M.closure X subseteq M.closure Y ↔ X subseteq M.closure Y :=
  ⟨(M.subset_closure X).trans, closure_subset_closure_of_subset_closure⟩

/--
lemma `subset_closure_of_subset` / 引理 `subset_closure_of_subset`

English:
lemma subset_closure_of_subset
  given: (M : Matroid α) (hXY : X subseteq Y) (hY : Y subseteq M.E := by aesop_mat)
  proof: hXY.trans (M.subset_closure Y)

中文:
引理 subset_closure_of_subset
  条件: (M : 拟阵 α) (hXY : X subseteq Y) (hY : Y subseteq M.E := by aesop_mat)
  证明: hXY.trans (M.subset_closure Y)

Depends on / 依赖: M.closure, M.subset_closure, aesop_mat, closure, hXY.trans, subset_closure, subseteq
-/
lemma subset_closure_of_subset (M : Matroid α) (hXY : X subseteq Y) (hY : Y subseteq M.E := by aesop_mat) :
    X subseteq M.closure Y :=
  hXY.trans (M.subset_closure Y)

/--
lemma `subset_closure_of_subset'` / 引理 `subset_closure_of_subset'`

English:
lemma subset_closure_of_subset'
  given: (M : Matroid α) (hXY : X subseteq Y) (hX : X subseteq M.E := by aesop_mat)
  proof: by
  rw [← closure_inter_ground]; exact M.subset_closure_of_subset (subset_inter hXY hX)

中文:
引理 subset_closure_of_subset'
  条件: (M : 拟阵 α) (hXY : X subseteq Y) (hX : X subseteq M.E := by aesop_mat)
  证明: by
  rw [← closure_inter_ground]; exact M.subset_closure_of_subset (subset_inter hXY hX)

Depends on / 依赖: M.closure, M.subset_closure_of_subset, aesop_mat, closure, closure_inter_ground, subset_closure_of_subset, subset_inter, subseteq
-/
lemma subset_closure_of_subset' (M : Matroid α) (hXY : X subseteq Y) (hX : X subseteq M.E := by aesop_mat) :
    X subseteq M.closure Y := by
  rw [← closure_inter_ground]; exact M.subset_closure_of_subset (subset_inter hXY hX)

/--
lemma `exists_of_closure_ssubset` / 引理 `exists_of_closure_ssubset`

English:
lemma exists_of_closure_ssubset
  given: (hXY : M.closure X ⊂ M.closure Y)
  statement: exists e in Y, e ∉ M.closure X
  proof: by
  by_contra! hcon
  exact hXY.not_subset (M.closure_subset_closure_of_subset_closure hcon)

中文:
引理 存在_of_closure_ssubset
  条件: (hXY : M.closure X ⊂ M.closure Y)
  结论: 存在 e in Y, e ∉ M.closure X
  证明: by
  by_contra! hcon
  exact hXY.not_subset (M.closure_subset_closure_of_subset_closure hcon)

Depends on / 依赖: M.closure_subset_closure_of_subset_closure, closure_subset_closure_of_subset_closure, hXY.not_subset, not_subset
-/
lemma exists_of_closure_ssubset (hXY : M.closure X ⊂ M.closure Y) : exists e in Y, e ∉ M.closure X := by
  by_contra! hcon
  exact hXY.not_subset (M.closure_subset_closure_of_subset_closure hcon)

/--
lemma `mem_closure_of_mem` / 引理 `mem_closure_of_mem`

English:
lemma mem_closure_of_mem
  given: (M : Matroid α) (h : e in X) (hX : X subseteq M.E := by aesop_mat)
  proof: (M.subset_closure X) h

中文:
引理 mem_closure_of_mem
  条件: (M : 拟阵 α) (h : e in X) (hX : X subseteq M.E := by aesop_mat)
  证明: (M.subset_closure X) h

Depends on / 依赖: M.closure, M.subset_closure, aesop_mat, closure, subset_closure
-/
lemma mem_closure_of_mem (M : Matroid α) (h : e in X) (hX : X subseteq M.E := by aesop_mat) :
    e in M.closure X :=
  (M.subset_closure X) h

/--
lemma `mem_closure_of_mem'` / 引理 `mem_closure_of_mem'`

English:
lemma mem_closure_of_mem'
  given: (M : Matroid α) (heX : e in X) (h : e in M.E := by aesop_mat)
  proof: by
  rw [← closure_inter_ground]
  exact M.mem_closure_of_mem ⟨heX, h⟩

中文:
引理 mem_closure_of_mem'
  条件: (M : 拟阵 α) (heX : e in X) (h : e in M.E := by aesop_mat)
  证明: by
  rw [← closure_inter_ground]
  exact M.mem_closure_of_mem ⟨heX, h⟩

Depends on / 依赖: M.closure, M.mem_closure_of_mem, aesop_mat, closure, closure_inter_ground, mem_closure_of_mem
-/
lemma mem_closure_of_mem' (M : Matroid α) (heX : e in X) (h : e in M.E := by aesop_mat) :
    e in M.closure X := by
  rw [← closure_inter_ground]
  exact M.mem_closure_of_mem ⟨heX, h⟩

/--
lemma `notMem_of_mem_sdiff_closure` / 引理 `notMem_of_mem_sdiff_closure`

English:
lemma notMem_of_mem_sdiff_closure
  given: (he : e in M.E \ M.closure X)
  statement: e ∉ X
  proof: fun heX => he.2 M.mem_closure_of_mem' heX he.1

@[deprecated (since := "2026-06-03")]
alias notMem_of_mem_diff_closure := notMem_of_mem_sdiff_closure

@[aesop unsafe 10% (rule_sets := [Matroid])]

中文:
引理 notMem_of_mem_sdiff_closure
  条件: (he : e in M.E \ M.closure X)
  结论: e ∉ X
  证明: fun heX => he.2 M.mem_closure_of_mem' heX he.1

@[deprecated (since := "2026-06-03")]
alias notMem_of_mem_diff_closure := notMem_of_mem_sdiff_closure

@[aesop unsafe 10% (rule_sets := [Matroid])]

Depends on / 依赖: M.mem_closure_of_mem, mem_closure_of_mem
-/
lemma notMem_of_mem_sdiff_closure (he : e in M.E \ M.closure X) : e ∉ X :=
fun heX => he.2 M.mem_closure_of_mem' heX he.1

@[deprecated (since := "2026-06-03")]
alias notMem_of_mem_diff_closure := notMem_of_mem_sdiff_closure

@[aesop unsafe 10% (rule_sets := [Matroid])]
/--
lemma `mem_ground_of_mem_closure` / 引理 `mem_ground_of_mem_closure`

English:
lemma mem_ground_of_mem_closure
  given: (he : e in M.closure X)
  statement: e in M.E
  proof: (M.closure_subset_ground _) he

中文:
引理 mem_ground_of_mem_closure
  条件: (he : e in M.closure X)
  结论: e in M.E
  证明: (M.closure_subset_ground _) he

Depends on / 依赖: M.closure_subset_ground, closure_subset_ground
-/
lemma mem_ground_of_mem_closure (he : e in M.closure X) : e in M.E :=
  (M.closure_subset_ground _) he

/--
lemma `closure_iUnion_closure_eq_closure_iUnion` / 引理 `closure_iUnion_closure_eq_closure_iUnion`

English:
lemma closure_iUnion_closure_eq_closure_iUnion
  given: (M : Matroid α) (Xs : ι -> Set α)
  proof: by
  simp_rw [closure_eq_subtypeClosure, iUnion_inter, Subtype.coe_inj]
  convert! M.subtypeClosure.closure_iSup_closure (fun i => ⟨Xs i inter M.E, inter_subset_right⟩) <;>
  simp [← iUnion_inter, subtypeClosure]

中文:
引理 closure_iUnion_closure_eq_closure_iUnion
  条件: (M : 拟阵 α) (Xs : ι -> 集合 α)
  证明: by
  simp_rw [closure_eq_subtypeClosure, iUnion_inter, Subtype.coe_inj]
  convert! M.subtypeClosure.closure_iSup_closure (fun i => ⟨Xs i inter M.E, inter_subset_right⟩) <;>
  simp [← iUnion_inter, subtypeClosure]

Depends on / 依赖: M.subtypeClosure.closure_iSup_closure, Subtype, Subtype.coe_inj, closure_eq_subtypeClosure, closure_iSup_closure, coe_inj, convert, iUnion_inter, inter_subset_right, simp_rw, subtypeClosure
-/
lemma closure_iUnion_closure_eq_closure_iUnion (M : Matroid α) (Xs : ι -> Set α) :
    M.closure (⋃ i, M.closure (Xs i)) = M.closure (⋃ i, Xs i) := by
  simp_rw [closure_eq_subtypeClosure, iUnion_inter, Subtype.coe_inj]
  convert! M.subtypeClosure.closure_iSup_closure (fun i => ⟨Xs i inter M.E, inter_subset_right⟩) <;>
  simp [← iUnion_inter, subtypeClosure]

/--
lemma `closure_iUnion_congr` / 引理 `closure_iUnion_congr`

English:
lemma closure_iUnion_congr
  given: (Xs Ys : ι -> Set α) (h : forall i, M.closure (Xs i) = M.closure (Ys i))
  proof: by
  simp [h, ← M.closure_iUnion_closure_eq_closure_iUnion]

中文:
引理 closure_iUnion_congr
  条件: (Xs Ys : ι -> 集合 α) (h : 对任意 i, M.closure (Xs i) = M.closure (Ys i))
  证明: by
  simp [h, ← M.closure_iUnion_closure_eq_closure_iUnion]

Depends on / 依赖: M.closure_iUnion_closure_eq_closure_iUnion, closure_iUnion_closure_eq_closure_iUnion
-/
lemma closure_iUnion_congr (Xs Ys : ι -> Set α) (h : forall i, M.closure (Xs i) = M.closure (Ys i)) :
    M.closure (⋃ i, Xs i) = M.closure (⋃ i, Ys i) := by
  simp [h, ← M.closure_iUnion_closure_eq_closure_iUnion]

/--
lemma `closure_biUnion_closure_eq_closure_sUnion` / 引理 `closure_biUnion_closure_eq_closure_sUnion`

English:
lemma closure_biUnion_closure_eq_closure_sUnion
  given: (M : Matroid α) (Xs : Set (Set α))
  proof: by
  rw [sUnion_eq_iUnion]; rw [biUnion_eq_iUnion]; rw [closure_iUnion_closure_eq_closure_iUnion]

中文:
引理 closure_biUnion_closure_eq_closure_sUnion
  条件: (M : 拟阵 α) (Xs : 集合 (集合 α))
  证明: by
  rw [sUnion_eq_iUnion]; rw [biUnion_eq_iUnion]; rw [closure_iUnion_closure_eq_closure_iUnion]

Depends on / 依赖: biUnion_eq_iUnion, closure_iUnion_closure_eq_closure_iUnion, fixInduction, fixInduction_spec, sUnion_eq_iUnion
-/
lemma closure_biUnion_closure_eq_closure_sUnion (M : Matroid α) (Xs : Set (Set α)) :
    M.closure (⋃ X in Xs, M.closure X) = M.closure (⋃₀ Xs) := by
  rw [sUnion_eq_iUnion]; rw [biUnion_eq_iUnion]; rw [closure_iUnion_closure_eq_closure_iUnion]

/--
lemma `closure_biUnion_closure_eq_closure_biUnion` / 引理 `closure_biUnion_closure_eq_closure_biUnion`

English:
lemma closure_biUnion_closure_eq_closure_biUnion
  given: (M : Matroid α) (Xs : ι -> Set α) (A : Set ι)
  proof: by
  rw [biUnion_eq_iUnion]; rw [M.closure_iUnion_closure_eq_closure_iUnion]; rw [biUnion_eq_iUnion]

中文:
引理 closure_biUnion_closure_eq_closure_biUnion
  条件: (M : 拟阵 α) (Xs : ι -> 集合 α) (A : 集合 ι)
  证明: by
  rw [biUnion_eq_iUnion]; rw [M.closure_iUnion_closure_eq_closure_iUnion]; rw [biUnion_eq_iUnion]

Depends on / 依赖: M.closure_iUnion_closure_eq_closure_iUnion, biUnion_eq_iUnion, closure_iUnion_closure_eq_closure_iUnion, fixInduction, fixInduction_spec
-/
lemma closure_biUnion_closure_eq_closure_biUnion (M : Matroid α) (Xs : ι -> Set α) (A : Set ι) :
    M.closure (⋃ i in A, M.closure (Xs i)) = M.closure (⋃ i in A, Xs i) := by
  rw [biUnion_eq_iUnion]; rw [M.closure_iUnion_closure_eq_closure_iUnion]; rw [biUnion_eq_iUnion]

/--
lemma `closure_biUnion_congr` / 引理 `closure_biUnion_congr`

English:
lemma closure_biUnion_congr
  statement: (M : Matroid α) (Xs Ys : ι -> Set α) (A : Set ι)
  proof: by
  rw [← closure_biUnion_closure_eq_closure_biUnion]; rw [iUnion₂_congr h]; rw [closure_biUnion_closure_eq_closure_biUnion]

中文:
引理 closure_biUnion_congr
  结论: (M : 拟阵 α) (Xs Ys : ι -> 集合 α) (A : 集合 ι)
  证明: by
  rw [← closure_biUnion_closure_eq_closure_biUnion]; rw [iUnion₂_congr h]; rw [closure_biUnion_closure_eq_closure_biUnion]

Depends on / 依赖: closure_biUnion_closure_eq_closure_biUnion
-/
lemma closure_biUnion_congr (M : Matroid α) (Xs Ys : ι -> Set α) (A : Set ι)
    (h : forall i in A, M.closure (Xs i) = M.closure (Ys i)) :
    M.closure (⋃ i in A, Xs i) = M.closure (⋃ i in A, Ys i) := by
  rw [← closure_biUnion_closure_eq_closure_biUnion]; rw [iUnion₂_congr h]; rw [closure_biUnion_closure_eq_closure_biUnion]

/--
lemma `closure_closure_union_closure_eq_closure_union` / 引理 `closure_closure_union_closure_eq_closure_union`

English:
lemma closure_closure_union_closure_eq_closure_union
  given: (M : Matroid α) (X Y : Set α)
  proof: by
  rw [eq_comm]; rw [union_eq_iUnion]; rw [← closure_iUnion_closure_eq_closure_iUnion]; rw [union_eq_iUnion]
  simp_rw [Bool.cond_eq_ite, apply_ite]

中文:
引理 closure_closure_union_closure_eq_closure_union
  条件: (M : 拟阵 α) (X Y : 集合 α)
  证明: by
  rw [eq_comm]; rw [union_eq_iUnion]; rw [← closure_iUnion_closure_eq_closure_iUnion]; rw [union_eq_iUnion]
  simp_rw [Bool.cond_eq_ite, apply_ite]

Depends on / 依赖: Bool.cond_eq_ite, apply_ite, closure_iUnion_closure_eq_closure_iUnion, cond_eq_ite, eq_comm, simp_rw, union_eq_iUnion
-/
lemma closure_closure_union_closure_eq_closure_union (M : Matroid α) (X Y : Set α) :
    M.closure (M.closure X union M.closure Y) = M.closure (X union Y) := by
  rw [eq_comm]; rw [union_eq_iUnion]; rw [← closure_iUnion_closure_eq_closure_iUnion]; rw [union_eq_iUnion]
  simp_rw [Bool.cond_eq_ite, apply_ite]

/--
lemma `closure_union_closure_right_eq` / 引理 `closure_union_closure_right_eq`

English:
lemma closure_union_closure_right_eq
  given: (M : Matroid α) (X Y : Set α)
  proof: by
  rw [← closure_closure_union_closure_eq_closure_union]; rw [closure_closure]; rw [closure_closure_union_closure_eq_closure_union]

中文:
引理 closure_union_closure_right_eq
  条件: (M : 拟阵 α) (X Y : 集合 α)
  证明: by
  rw [← closure_closure_union_closure_eq_closure_union]; rw [closure_closure]; rw [closure_closure_union_closure_eq_closure_union]
-/
@[simp] lemma closure_union_closure_right_eq (M : Matroid α) (X Y : Set α) :
    M.closure (X union M.closure Y) = M.closure (X union Y) := by
  rw [← closure_closure_union_closure_eq_closure_union]; rw [closure_closure]; rw [closure_closure_union_closure_eq_closure_union]

/--
lemma `closure_union_closure_left_eq` / 引理 `closure_union_closure_left_eq`

English:
lemma closure_union_closure_left_eq
  given: (M : Matroid α) (X Y : Set α)
  proof: by
  rw [← closure_closure_union_closure_eq_closure_union]; rw [closure_closure]; rw [closure_closure_union_closure_eq_closure_union]

中文:
引理 closure_union_closure_left_eq
  条件: (M : 拟阵 α) (X Y : 集合 α)
  证明: by
  rw [← closure_closure_union_closure_eq_closure_union]; rw [closure_closure]; rw [closure_closure_union_closure_eq_closure_union]
-/
@[simp] lemma closure_union_closure_left_eq (M : Matroid α) (X Y : Set α) :
    M.closure (M.closure X union Y) = M.closure (X union Y) := by
  rw [← closure_closure_union_closure_eq_closure_union]; rw [closure_closure]; rw [closure_closure_union_closure_eq_closure_union]

/--
lemma `closure_insert_closure_eq_closure_insert` / 引理 `closure_insert_closure_eq_closure_insert`

English:
lemma closure_insert_closure_eq_closure_insert
  given: (M : Matroid α) (e : α) (X : Set α)
  proof: by
  simp_rw [← singleton_union, closure_union_closure_right_eq]

中文:
引理 closure_insert_closure_eq_closure_insert
  条件: (M : 拟阵 α) (e : α) (X : 集合 α)
  证明: by
  simp_rw [← singleton_union, closure_union_closure_right_eq]
-/
@[simp] lemma closure_insert_closure_eq_closure_insert (M : Matroid α) (e : α) (X : Set α) :
    M.closure (insert e (M.closure X)) = M.closure (insert e X) := by
  simp_rw [← singleton_union, closure_union_closure_right_eq]

/--
lemma `closure_union_congr_left` / 引理 `closure_union_congr_left`

English:
lemma closure_union_congr_left
  given: {X' : Set α} (h : M.closure X = M.closure X')
  proof: by
  rw [← M.closure_union_closure_left_eq]; rw [h]; rw [M.closure_union_closure_left_eq]

中文:
引理 closure_union_congr_left
  条件: {X' : 集合 α} (h : M.closure X = M.closure X')
  证明: by
  rw [← M.closure_union_closure_left_eq]; rw [h]; rw [M.closure_union_closure_left_eq]

Depends on / 依赖: M.closure_union_closure_left_eq, closure_union_closure_left_eq
-/
lemma closure_union_congr_left {X' : Set α} (h : M.closure X = M.closure X') :
    M.closure (X union Y) = M.closure (X' union Y) := by
  rw [← M.closure_union_closure_left_eq]; rw [h]; rw [M.closure_union_closure_left_eq]

/--
lemma `closure_union_congr_right` / 引理 `closure_union_congr_right`

English:
lemma closure_union_congr_right
  given: {Y' : Set α} (h : M.closure Y = M.closure Y')
  proof: by
  rw [← M.closure_union_closure_right_eq]; rw [h]; rw [M.closure_union_closure_right_eq]

中文:
引理 closure_union_congr_right
  条件: {Y' : 集合 α} (h : M.closure Y = M.closure Y')
  证明: by
  rw [← M.closure_union_closure_right_eq]; rw [h]; rw [M.closure_union_closure_right_eq]

Depends on / 依赖: M.closure_union_closure_right_eq, closure_union_closure_right_eq
-/
lemma closure_union_congr_right {Y' : Set α} (h : M.closure Y = M.closure Y') :
    M.closure (X union Y) = M.closure (X union Y') := by
  rw [← M.closure_union_closure_right_eq]; rw [h]; rw [M.closure_union_closure_right_eq]

/--
lemma `closure_insert_congr_right` / 引理 `closure_insert_congr_right`

English:
lemma closure_insert_congr_right
  given: (h : M.closure X = M.closure Y)
  proof: by
  simp [← union_singleton, closure_union_congr_left h]

中文:
引理 closure_insert_congr_right
  条件: (h : M.closure X = M.closure Y)
  证明: by
  simp [← union_singleton, closure_union_congr_left h]

Depends on / 依赖: closure_union_congr_left, union_singleton
-/
lemma closure_insert_congr_right (h : M.closure X = M.closure Y) :
    M.closure (insert e X) = M.closure (insert e Y) := by
  simp [← union_singleton, closure_union_congr_left h]

/--
lemma `closure_union_closure_empty_eq` / 引理 `closure_union_closure_empty_eq`

English:
lemma closure_union_closure_empty_eq
  given: (M : Matroid α) (X : Set α)
  proof: union_eq_self_of_subset_right (M.closure_subset_closure (empty_subset _))

中文:
引理 closure_union_closure_empty_eq
  条件: (M : 拟阵 α) (X : 集合 α)
  证明: union_eq_self_of_subset_right (M.closure_subset_closure (empty_subset _))
-/
@[simp] lemma closure_union_closure_empty_eq (M : Matroid α) (X : Set α) :
    M.closure X union M.closure ∅ = M.closure X :=
  union_eq_self_of_subset_right (M.closure_subset_closure (empty_subset _))

/--
lemma `closure_empty_union_closure_eq` / 引理 `closure_empty_union_closure_eq`

English:
lemma closure_empty_union_closure_eq
  given: (M : Matroid α) (X : Set α)
  proof: union_eq_self_of_subset_left (M.closure_subset_closure (empty_subset _))

中文:
引理 closure_empty_union_closure_eq
  条件: (M : 拟阵 α) (X : 集合 α)
  证明: union_eq_self_of_subset_left (M.closure_subset_closure (empty_subset _))
-/
@[simp] lemma closure_empty_union_closure_eq (M : Matroid α) (X : Set α) :
    M.closure ∅ union M.closure X = M.closure X :=
  union_eq_self_of_subset_left (M.closure_subset_closure (empty_subset _))

/--
lemma `closure_insert_eq_of_mem_closure` / 引理 `closure_insert_eq_of_mem_closure`

English:
lemma closure_insert_eq_of_mem_closure
  given: (he : e in M.closure X)
  proof: by
  rw [← closure_insert_closure_eq_closure_insert]; rw [insert_eq_of_mem he]; rw [closure_closure]

中文:
引理 closure_insert_eq_of_mem_closure
  条件: (he : e in M.closure X)
  证明: by
  rw [← closure_insert_closure_eq_closure_insert]; rw [insert_eq_of_mem he]; rw [closure_closure]

Depends on / 依赖: closure_closure, closure_insert_closure_eq_closure_insert, insert_eq_of_mem
-/
lemma closure_insert_eq_of_mem_closure (he : e in M.closure X) :
    M.closure (insert e X) = M.closure X := by
  rw [← closure_insert_closure_eq_closure_insert]; rw [insert_eq_of_mem he]; rw [closure_closure]

/--
lemma `mem_closure_self` / 引理 `mem_closure_self`

English:
lemma mem_closure_self
  given: (M : Matroid α) (e : α) (he : e in M.E := by aesop_mat)
  statement: e in M.closure {e}
  proof: mem_closure_of_mem' M rfl

中文:
引理 mem_closure_self
  条件: (M : 拟阵 α) (e : α) (he : e in M.E := by aesop_mat)
  结论: e in M.closure {e}
  证明: mem_closure_of_mem' M rfl

Depends on / 依赖: M.closure, aesop_mat, closure, mem_closure_of_mem
-/
lemma mem_closure_self (M : Matroid α) (e : α) (he : e in M.E := by aesop_mat) : e in M.closure {e} :=
  mem_closure_of_mem' M rfl

section Indep

variable {ι : Sort*} {I J B : Set α} {x : α}

/--
lemma `Indep.closure_eq_setOfPred_isBasis_insert` / 引理 `Indep.closure_eq_setOfPred_isBasis_insert`

English:
lemma Indep.closure_eq_setOfPred_isBasis_insert
  given: (hI : M.Indep I)
  proof: by
  set F := {x | M.IsBasis I (insert x I)}
  have hIF : M.IsBasis I F := hI.isBasis_setOfPred_insert_isBasis
  have hF : M.IsFlat F := by
    refine ⟨fun J X hJF hJX e heX => show M.IsBasis _ _ from ?_, hIF.subset_ground⟩
    exact (hIF.isBasis_of_isBasis_of_subset_of_subset (hJX.isBasis_union hJF

中文:
引理 Indep.closure_eq_setOfPred_isBasis_insert
  条件: (hI : M.Indep I)
  证明: by
  set F := {x | M.IsBasis I (insert x I)}
  have hIF : M.IsBasis I F := hI.isBasis_setOfPred_insert_isBasis
  have hF : M.IsFlat F := by
    refine ⟨fun J X hJF hJX e heX => show M.IsBasis _ _ from ?_, hIF.subset_ground⟩
    exact (hIF.isBasis_of_isBasis_of_subset_of_subset (hJX.isBasis_union hJF

Depends on / 依赖: IsBasis, IsFlat, M.IsBasis, M.IsFlat, Or.inl, closure_def, hI.isBasis_setOfPred_insert_isBasis, hIF.isBasis_of_isBasis_of_subset_of_subset, hIF.subset.trans, hIF.subset_ground, hJF.subset, hJX.isBasis_union, insert, insert_subset, isBasis_of_isBasis_of_subset_of_subset, isBasis_setOfPred_insert_isBasis, isBasis_subset, isBasis_union, subset, subset_antisymm_iff
-/
lemma Indep.closure_eq_setOfPred_isBasis_insert (hI : M.Indep I) :
    M.closure I = {x | M.IsBasis I (insert x I)} := by
  set F := {x | M.IsBasis I (insert x I)}
  have hIF : M.IsBasis I F := hI.isBasis_setOfPred_insert_isBasis
  have hF : M.IsFlat F := by
    refine ⟨fun J X hJF hJX e heX => show M.IsBasis _ _ from ?_, hIF.subset_ground⟩
    exact (hIF.isBasis_of_isBasis_of_subset_of_subset (hJX.isBasis_union hJF) hJF.subset
      (hIF.subset.trans subset_union_right)).isBasis_subset (subset_insert _ _)
      (insert_subset (Or.inl heX) (hIF.subset.trans subset_union_right))
  rw [subset_antisymm_iff]; rw [closure_def]; rw [subset_sInter_iff]; rw [and_iff_right (sInter_subset_of_mem _)]
  · rintro F' ⟨hF', hIF'⟩ e (he : M.IsBasis I (insert e I))
    rw [inter_eq_left.mpr (hIF.subset.trans hIF.subset_ground)] at hIF'
    obtain ⟨J, hJ, hIJ⟩ := hI.subset_isBasis_of_subset hIF' hF'.2
    exact (hF'.1 hJ (he.isBasis_union_of_subset hJ.indep hIJ)) (Or.inr (mem_insert _ _))
  exact ⟨hF, inter_subset_left.trans hIF.subset⟩

@[deprecated (since := "2026-07-09")]
alias Indep.closure_eq_setOf_isBasis_insert := Indep.closure_eq_setOfPred_isBasis_insert

/--
lemma `Indep.insert_isBasis_iff_mem_closure` / 引理 `Indep.insert_isBasis_iff_mem_closure`

English:
lemma Indep.insert_isBasis_iff_mem_closure
  given: (hI : M.Indep I)
  proof: by
  rw [hI.closure_eq_setOfPred_isBasis_insert]; rw [mem_ofPred]

中文:
引理 Indep.insert_isBasis_iff_mem_closure
  条件: (hI : M.Indep I)
  证明: by
  rw [hI.closure_eq_setOfPred_isBasis_insert]; rw [mem_ofPred]

Depends on / 依赖: closure_eq_setOfPred_isBasis_insert, hI.closure_eq_setOfPred_isBasis_insert, mem_ofPred
-/
lemma Indep.insert_isBasis_iff_mem_closure (hI : M.Indep I) :
    M.IsBasis I (insert e I) ↔ e in M.closure I := by
  rw [hI.closure_eq_setOfPred_isBasis_insert]; rw [mem_ofPred]

/--
lemma `Indep.isBasis_closure` / 引理 `Indep.isBasis_closure`

English:
lemma Indep.isBasis_closure
  given: (hI : M.Indep I)
  statement: M.IsBasis I (M.closure I)
  proof: by
  rw [hI.closure_eq_setOfPred_isBasis_insert]; exact hI.isBasis_setOfPred_insert_isBasis

中文:
引理 Indep.isBasis_closure
  条件: (hI : M.Indep I)
  结论: M.是基 I (M.closure I)
  证明: by
  rw [hI.closure_eq_setOfPred_isBasis_insert]; exact hI.isBasis_setOfPred_insert_isBasis

Depends on / 依赖: closure_eq_setOfPred_isBasis_insert, hI.closure_eq_setOfPred_isBasis_insert, hI.isBasis_setOfPred_insert_isBasis, isBasis_setOfPred_insert_isBasis
-/
lemma Indep.isBasis_closure (hI : M.Indep I) : M.IsBasis I (M.closure I) := by
  rw [hI.closure_eq_setOfPred_isBasis_insert]; exact hI.isBasis_setOfPred_insert_isBasis

/--
lemma `IsBasis.closure_eq_closure` / 引理 `IsBasis.closure_eq_closure`

English:
lemma IsBasis.closure_eq_closure
  given: (h : M.IsBasis I X)
  statement: M.closure I = M.closure X
  proof: by
  refine subset_antisymm (M.closure_subset_closure h.subset) ?_
  rw [← M.closure_closure I]; rw [h.indep.closure_eq_setOfPred_isBasis_insert]
  exact M.closure_subset_closure fun e he => (h.isBasis_subset (subset_insert _ _)
    (insert_subset he h.subset))

中文:
引理 是基.closure_eq_closure
  条件: (h : M.是基 I X)
  结论: M.closure I = M.closure X
  证明: by
  refine subset_antisymm (M.closure_subset_closure h.subset) ?_
  rw [← M.closure_closure I]; rw [h.indep.closure_eq_setOfPred_isBasis_insert]
  exact M.closure_subset_closure fun e he => (h.isBasis_subset (subset_insert _ _)
    (insert_subset he h.subset))

Depends on / 依赖: M.closure_closure, M.closure_subset_closure, closure_closure, closure_eq_setOfPred_isBasis_insert, closure_subset_closure, h.indep.closure_eq_setOfPred_isBasis_insert, h.isBasis_subset, h.subset, insert_subset, isBasis_subset, subset, subset_antisymm, subset_insert
-/
lemma IsBasis.closure_eq_closure (h : M.IsBasis I X) : M.closure I = M.closure X := by
  refine subset_antisymm (M.closure_subset_closure h.subset) ?_
  rw [← M.closure_closure I]; rw [h.indep.closure_eq_setOfPred_isBasis_insert]
  exact M.closure_subset_closure fun e he => (h.isBasis_subset (subset_insert _ _)
    (insert_subset he h.subset))

/--
lemma `IsBasis.closure_eq_right` / 引理 `IsBasis.closure_eq_right`

English:
lemma IsBasis.closure_eq_right
  given: (h : M.IsBasis I (M.closure X))
  statement: M.closure I = M.closure X
  proof: M.closure_closure X ▸ h.closure_eq_closure

中文:
引理 是基.closure_eq_right
  条件: (h : M.是基 I (M.closure X))
  结论: M.closure I = M.closure X
  证明: M.closure_closure X ▸ h.closure_eq_closure

Depends on / 依赖: M.closure_closure, closure_closure, closure_eq_closure, h.closure_eq_closure
-/
lemma IsBasis.closure_eq_right (h : M.IsBasis I (M.closure X)) : M.closure I = M.closure X :=
  M.closure_closure X ▸ h.closure_eq_closure

/--
lemma `IsBasis'.closure_eq_closure` / 引理 `IsBasis'.closure_eq_closure`

English:
lemma IsBasis'.closure_eq_closure
  given: (h : M.IsBasis' I X)
  statement: M.closure I = M.closure X
  proof: by
  rw [← closure_inter_ground _ X]; rw [h.isBasis_inter_ground.closure_eq_closure]

中文:
引理 是基'.closure_eq_closure
  条件: (h : M.是基' I X)
  结论: M.closure I = M.closure X
  证明: by
  rw [← closure_inter_ground _ X]; rw [h.isBasis_inter_ground.closure_eq_closure]
-/
lemma IsBasis'.closure_eq_closure (h : M.IsBasis' I X) : M.closure I = M.closure X := by
  rw [← closure_inter_ground _ X]; rw [h.isBasis_inter_ground.closure_eq_closure]

/--
lemma `IsBasis.subset_closure` / 引理 `IsBasis.subset_closure`

English:
lemma IsBasis.subset_closure
  given: (h : M.IsBasis I X)
  statement: X subseteq M.closure I
  proof: by
  rw [← closure_subset_closure_iff_subset_closure]; rw [h.closure_eq_closure]

中文:
引理 是基.subset_closure
  条件: (h : M.是基 I X)
  结论: X subseteq M.closure I
  证明: by
  rw [← closure_subset_closure_iff_subset_closure]; rw [h.closure_eq_closure]

Depends on / 依赖: closure_eq_closure, closure_subset_closure_iff_subset_closure, h.closure_eq_closure
-/
lemma IsBasis.subset_closure (h : M.IsBasis I X) : X subseteq M.closure I := by
  rw [← closure_subset_closure_iff_subset_closure]; rw [h.closure_eq_closure]

/--
lemma `IsBasis'.isBasis_closure_right` / 引理 `IsBasis'.isBasis_closure_right`

English:
lemma IsBasis'.isBasis_closure_right
  given: (h : M.IsBasis' I X)
  statement: M.IsBasis I (M.closure X)
  proof: by
  rw [← h.closure_eq_closure]; exact h.indep.isBasis_closure

中文:
引理 是基'.isBasis_closure_right
  条件: (h : M.是基' I X)
  结论: M.是基 I (M.closure X)
  证明: by
  rw [← h.closure_eq_closure]; exact h.indep.isBasis_closure
-/
lemma IsBasis'.isBasis_closure_right (h : M.IsBasis' I X) : M.IsBasis I (M.closure X) := by
  rw [← h.closure_eq_closure]; exact h.indep.isBasis_closure

/--
lemma `IsBasis.isBasis_closure_right` / 引理 `IsBasis.isBasis_closure_right`

English:
lemma IsBasis.isBasis_closure_right
  given: (h : M.IsBasis I X)
  statement: M.IsBasis I (M.closure X)
  proof: h.isBasis'.isBasis_closure_right

中文:
引理 是基.isBasis_closure_right
  条件: (h : M.是基 I X)
  结论: M.是基 I (M.closure X)
  证明: h.isBasis'.isBasis_closure_right

Depends on / 依赖: h.isBasis, isBasis, isBasis_closure_right
-/
lemma IsBasis.isBasis_closure_right (h : M.IsBasis I X) : M.IsBasis I (M.closure X) :=
  h.isBasis'.isBasis_closure_right

/--
lemma `Indep.mem_closure_iff` / 引理 `Indep.mem_closure_iff`

English:
lemma Indep.mem_closure_iff
  given: (hI : M.Indep I)
  proof: by
  rwa [hI.closure_eq_setOfPred_isBasis_insert, mem_ofPred, isBasis_insert_iff]

中文:
引理 Indep.mem_closure_iff
  条件: (hI : M.Indep I)
  证明: by
  rwa [hI.closure_eq_setOfPred_isBasis_insert, mem_ofPred, isBasis_insert_iff]

Depends on / 依赖: closure_eq_setOfPred_isBasis_insert, hI.closure_eq_setOfPred_isBasis_insert, isBasis_insert_iff, mem_ofPred
-/
lemma Indep.mem_closure_iff (hI : M.Indep I) :
    x in M.closure I ↔ M.Dep (insert x I) ∨ x in I := by
  rwa [hI.closure_eq_setOfPred_isBasis_insert, mem_ofPred, isBasis_insert_iff]

/--
lemma `Indep.mem_closure_iff'` / 引理 `Indep.mem_closure_iff'`

English:
lemma Indep.mem_closure_iff'
  given: (hI : M.Indep I)
  proof: by
  rw [hI.mem_closure_iff]; rw [dep_iff]; rw [insert_subset_iff]; rw [and_iff_left hI.subset_ground]; rw [imp_iff_not_or]
  have := hI.subset_ground
  aesop

中文:
引理 Indep.mem_closure_iff'
  条件: (hI : M.Indep I)
  证明: by
  rw [hI.mem_closure_iff]; rw [dep_iff]; rw [insert_subset_iff]; rw [and_iff_left hI.subset_ground]; rw [imp_iff_not_or]
  have := hI.subset_ground
  aesop

Depends on / 依赖: and_iff_left, dep_iff, hI.mem_closure_iff, hI.subset_ground, imp_iff_not_or, insert_subset_iff, mem_closure_iff, subset_ground
-/
lemma Indep.mem_closure_iff' (hI : M.Indep I) :
    x in M.closure I ↔ x in M.E ∧ (M.Indep (insert x I) -> x in I) := by
  rw [hI.mem_closure_iff]; rw [dep_iff]; rw [insert_subset_iff]; rw [and_iff_left hI.subset_ground]; rw [imp_iff_not_or]
  have := hI.subset_ground
  aesop

/--
lemma `Indep.insert_dep_iff` / 引理 `Indep.insert_dep_iff`

English:
lemma Indep.insert_dep_iff
  given: (hI : M.Indep I)
  statement: M.Dep (insert e I) ↔ e in M.closure I \ I
  proof: by
  rw [mem_sdiff]; rw [hI.mem_closure_iff]; rw [or_and_right]; rw [and_not_self_iff]; rw [or_false]; rw [iff_self_and]; rw [imp_not_comm]
  intro heI; rw [insert_eq_of_mem heI]; exact hI.not_dep

中文:
引理 Indep.insert_dep_iff
  条件: (hI : M.Indep I)
  结论: M.Dep (insert e I) ↔ e in M.closure I \ I
  证明: by
  rw [mem_sdiff]; rw [hI.mem_closure_iff]; rw [or_and_right]; rw [and_not_self_iff]; rw [or_false]; rw [iff_self_and]; rw [imp_not_comm]
  intro heI; rw [insert_eq_of_mem heI]; exact hI.not_dep

Depends on / 依赖: and_not_self_iff, hI.mem_closure_iff, hI.not_dep, iff_self_and, imp_not_comm, insert_eq_of_mem, mem_closure_iff, mem_sdiff, not_dep, or_and_right, or_false
-/
lemma Indep.insert_dep_iff (hI : M.Indep I) : M.Dep (insert e I) ↔ e in M.closure I \ I := by
  rw [mem_sdiff]; rw [hI.mem_closure_iff]; rw [or_and_right]; rw [and_not_self_iff]; rw [or_false]; rw [iff_self_and]; rw [imp_not_comm]
  intro heI; rw [insert_eq_of_mem heI]; exact hI.not_dep

/--
lemma `Indep.mem_closure_iff_of_notMem` / 引理 `Indep.mem_closure_iff_of_notMem`

English:
lemma Indep.mem_closure_iff_of_notMem
  given: (hI : M.Indep I) (heI : e ∉ I)
  proof: by
  rw [hI.insert_dep_iff]; rw [mem_sdiff]; rw [and_iff_left heI]

中文:
引理 Indep.mem_closure_iff_of_notMem
  条件: (hI : M.Indep I) (heI : e ∉ I)
  证明: by
  rw [hI.insert_dep_iff]; rw [mem_sdiff]; rw [and_iff_left heI]

Depends on / 依赖: and_iff_left, hI.insert_dep_iff, insert_dep_iff, mem_sdiff
-/
lemma Indep.mem_closure_iff_of_notMem (hI : M.Indep I) (heI : e ∉ I) :
    e in M.closure I ↔ M.Dep (insert e I) := by
  rw [hI.insert_dep_iff]; rw [mem_sdiff]; rw [and_iff_left heI]

/--
lemma `Indep.notMem_closure_iff` / 引理 `Indep.notMem_closure_iff`

English:
lemma Indep.notMem_closure_iff
  given: (hI : M.Indep I) (he : e in M.E := by aesop_mat)
  proof: by
  rw [hI.mem_closure_iff]; rw [dep_iff]; rw [insert_subset_iff]; rw [and_iff_right he]; rw [and_iff_left hI.subset_ground]; tauto

中文:
引理 Indep.notMem_closure_iff
  条件: (hI : M.Indep I) (he : e in M.E := by aesop_mat)
  证明: by
  rw [hI.mem_closure_iff]; rw [dep_iff]; rw [insert_subset_iff]; rw [and_iff_right he]; rw [and_iff_left hI.subset_ground]; tauto

Depends on / 依赖: M.Indep, M.closure, aesop_mat, and_iff_left, and_iff_right, closure, dep_iff, hI.mem_closure_iff, hI.subset_ground, insert, insert_subset_iff, mem_closure_iff, subset_ground
-/
lemma Indep.notMem_closure_iff (hI : M.Indep I) (he : e in M.E := by aesop_mat) :
    e ∉ M.closure I ↔ M.Indep (insert e I) ∧ e ∉ I := by
  rw [hI.mem_closure_iff]; rw [dep_iff]; rw [insert_subset_iff]; rw [and_iff_right he]; rw [and_iff_left hI.subset_ground]; tauto

/--
lemma `Indep.notMem_closure_iff_of_notMem` / 引理 `Indep.notMem_closure_iff_of_notMem`

English:
lemma Indep.notMem_closure_iff_of_notMem
  statement: (hI : M.Indep I) (heI : e ∉ I)
  proof: by
  rw [hI.notMem_closure_iff]; rw [and_iff_left heI]

中文:
引理 Indep.notMem_closure_iff_of_notMem
  结论: (hI : M.Indep I) (heI : e ∉ I)
  证明: by
  rw [hI.notMem_closure_iff]; rw [and_iff_left heI]

Depends on / 依赖: M.Indep, M.closure, aesop_mat, and_iff_left, closure, hI.notMem_closure_iff, insert, notMem_closure_iff
-/
lemma Indep.notMem_closure_iff_of_notMem (hI : M.Indep I) (heI : e ∉ I)
    (he : e in M.E := by aesop_mat) : e ∉ M.closure I ↔ M.Indep (insert e I) := by
  rw [hI.notMem_closure_iff]; rw [and_iff_left heI]

/--
lemma `Indep.insert_indep_iff_of_notMem` / 引理 `Indep.insert_indep_iff_of_notMem`

English:
lemma Indep.insert_indep_iff_of_notMem
  given: (hI : M.Indep I) (heI : e ∉ I)
  proof: by
  rw [mem_sdiff]; rw [hI.mem_closure_iff_of_notMem heI]; rw [dep_iff]; rw [not_and]; rw [not_imp_not]; rw [insert_subset_iff]; rw [and_iff_left hI.subset_ground]
  exact ⟨fun h => ⟨h.subset_ground (mem_insert e I), fun _ => h⟩, fun h => h.2 h.1⟩

中文:
引理 Indep.insert_indep_iff_of_notMem
  条件: (hI : M.Indep I) (heI : e ∉ I)
  证明: by
  rw [mem_sdiff]; rw [hI.mem_closure_iff_of_notMem heI]; rw [dep_iff]; rw [not_and]; rw [not_imp_not]; rw [insert_subset_iff]; rw [and_iff_left hI.subset_ground]
  exact ⟨fun h => ⟨h.subset_ground (mem_insert e I), fun _ => h⟩, fun h => h.2 h.1⟩

Depends on / 依赖: and_iff_left, dep_iff, h.subset_ground, hI.mem_closure_iff_of_notMem, hI.subset_ground, insert_subset_iff, mem_closure_iff_of_notMem, mem_insert, mem_sdiff, not_and, not_imp_not, subset_ground
-/
lemma Indep.insert_indep_iff_of_notMem (hI : M.Indep I) (heI : e ∉ I) :
    M.Indep (insert e I) ↔ e in M.E \ M.closure I := by
  rw [mem_sdiff]; rw [hI.mem_closure_iff_of_notMem heI]; rw [dep_iff]; rw [not_and]; rw [not_imp_not]; rw [insert_subset_iff]; rw [and_iff_left hI.subset_ground]
  exact ⟨fun h => ⟨h.subset_ground (mem_insert e I), fun _ => h⟩, fun h => h.2 h.1⟩

/--
lemma `Indep.insert_indep_iff` / 引理 `Indep.insert_indep_iff`

English:
lemma Indep.insert_indep_iff
  given: (hI : M.Indep I)
  proof: by
  obtain (h | h) := em (e in I)
  · simp_rw [insert_eq_of_mem h, iff_true_intro hI, true_iff, iff_true_intro h, or_true]
  rw [hI.insert_indep_iff_of_notMem h]; rw [or_iff_left h]

中文:
引理 Indep.insert_indep_iff
  条件: (hI : M.Indep I)
  证明: by
  obtain (h | h) := em (e in I)
  · simp_rw [insert_eq_of_mem h, iff_true_intro hI, true_iff, iff_true_intro h, or_true]
  rw [hI.insert_indep_iff_of_notMem h]; rw [or_iff_left h]

Depends on / 依赖: hI.insert_indep_iff_of_notMem, iff_true_intro, insert_eq_of_mem, insert_indep_iff_of_notMem, or_iff_left, or_true, simp_rw, true_iff
-/
lemma Indep.insert_indep_iff (hI : M.Indep I) :
    M.Indep (insert e I) ↔ e in M.E \ M.closure I ∨ e in I := by
  obtain (h | h) := em (e in I)
  · simp_rw [insert_eq_of_mem h, iff_true_intro hI, true_iff, iff_true_intro h, or_true]
  rw [hI.insert_indep_iff_of_notMem h]; rw [or_iff_left h]

/--
lemma `insert_indep_iff` / 引理 `insert_indep_iff`

English:
lemma insert_indep_iff
  statement: M.Indep (insert e I) ↔ M.Indep I ∧ (e ∉ I -> e in M.E \ M.closure I)
  proof: by
  by_cases hI : M.Indep I
  · rw [hI.insert_indep_iff, and_iff_right hI, or_iff_not_imp_right]
  simp [hI, show ¬ M.Indep (insert e I) from fun h => hI <| h.subset <| subset_insert _ _]

中文:
引理 insert_indep_iff
  结论: M.Indep (insert e I) ↔ M.Indep I ∧ (e ∉ I -> e in M.E \ M.closure I)
  证明: by
  by_cases hI : M.Indep I
  · rw [hI.insert_indep_iff, and_iff_right hI, or_iff_not_imp_right]
  simp [hI, show ¬ M.Indep (insert e I) from fun h => hI <| h.subset <| subset_insert _ _]

Depends on / 依赖: M.Indep, and_iff_right, h.subset, hI.insert_indep_iff, insert, insert_indep_iff, or_iff_not_imp_right, subset, subset_insert
-/
lemma insert_indep_iff : M.Indep (insert e I) ↔ M.Indep I ∧ (e ∉ I -> e in M.E \ M.closure I) := by
  by_cases hI : M.Indep I
  · rw [hI.insert_indep_iff, and_iff_right hI, or_iff_not_imp_right]
  simp [hI, show ¬ M.Indep (insert e I) from fun h => hI <| h.subset <| subset_insert _ _]

/--
lemma `Indep.insert_sdiff_indep_iff` / 引理 `Indep.insert_sdiff_indep_iff`

English:
lemma Indep.insert_sdiff_indep_iff
  given: (hI : M.Indep (I \ {e})) (heI : e in I)
  proof: by
  obtain rfl | hne := eq_or_ne e f
  · simp [hI, heI]
  rw [← insert_sdiff_singleton_comm hne.symm]; rw [hI.insert_indep_iff]; rw [mem_sdiff_singleton]; rw [and_iff_left hne.symm]

@[deprecated (since := "2026-06-03")]
alias Indep.insert_diff_indep_iff := Indep.insert_sdiff_indep_iff

中文:
引理 Indep.insert_sdiff_indep_iff
  条件: (hI : M.Indep (I \ {e})) (heI : e in I)
  证明: by
  obtain rfl | hne := eq_or_ne e f
  · simp [hI, heI]
  rw [← insert_sdiff_singleton_comm hne.symm]; rw [hI.insert_indep_iff]; rw [mem_sdiff_singleton]; rw [and_iff_left hne.symm]

@[deprecated (since := "2026-06-03")]
alias Indep.insert_diff_indep_iff := Indep.insert_sdiff_indep_iff

Depends on / 依赖: and_iff_left, eq_or_ne, hI.insert_indep_iff, hne.symm, insert_indep_iff, insert_sdiff_singleton_comm, mem_sdiff_singleton
-/
lemma Indep.insert_sdiff_indep_iff (hI : M.Indep (I \ {e})) (heI : e in I) :
    M.Indep (insert f I \ {e}) ↔ f in M.E \ M.closure (I \ {e}) ∨ f in I := by
  obtain rfl | hne := eq_or_ne e f
  · simp [hI, heI]
  rw [← insert_sdiff_singleton_comm hne.symm]; rw [hI.insert_indep_iff]; rw [mem_sdiff_singleton]; rw [and_iff_left hne.symm]

@[deprecated (since := "2026-06-03")]
alias Indep.insert_diff_indep_iff := Indep.insert_sdiff_indep_iff

/--
lemma `Indep.isBasis_of_subset_of_subset_closure` / 引理 `Indep.isBasis_of_subset_of_subset_closure`

English:
lemma Indep.isBasis_of_subset_of_subset_closure
  statement: (hI : M.Indep I) (hIX : I subseteq X)
  proof: hI.isBasis_closure.isBasis_subset hIX hXI

中文:
引理 Indep.isBasis_of_subset_of_subset_closure
  结论: (hI : M.Indep I) (hIX : I subseteq X)
  证明: hI.isBasis_closure.isBasis_subset hIX hXI

Depends on / 依赖: hI.isBasis_closure.isBasis_subset, isBasis_closure, isBasis_subset
-/
lemma Indep.isBasis_of_subset_of_subset_closure (hI : M.Indep I) (hIX : I subseteq X)
    (hXI : X subseteq M.closure I) : M.IsBasis I X :=
  hI.isBasis_closure.isBasis_subset hIX hXI

/--
lemma `isBasis_iff_indep_subset_closure` / 引理 `isBasis_iff_indep_subset_closure`

English:
lemma isBasis_iff_indep_subset_closure
  statement: M.IsBasis I X ↔ M.Indep I ∧ I subseteq X ∧ X subseteq M.closure I
  proof: ⟨fun h => ⟨h.indep, h.subset, h.subset_closure⟩,
    fun h => h.1.isBasis_of_subset_of_subset_closure h.2.1 h.2.2⟩

中文:
引理 isBasis_iff_indep_subset_closure
  结论: M.是基 I X ↔ M.Indep I ∧ I subseteq X ∧ X subseteq M.closure I
  证明: ⟨fun h => ⟨h.indep, h.subset, h.subset_closure⟩,
    fun h => h.1.isBasis_of_subset_of_subset_closure h.2.1 h.2.2⟩

Depends on / 依赖: h.indep, h.subset, h.subset_closure, isBasis_of_subset_of_subset_closure, subset, subset_closure
-/
lemma isBasis_iff_indep_subset_closure : M.IsBasis I X ↔ M.Indep I ∧ I subseteq X ∧ X subseteq M.closure I :=
  ⟨fun h => ⟨h.indep, h.subset, h.subset_closure⟩,
    fun h => h.1.isBasis_of_subset_of_subset_closure h.2.1 h.2.2⟩

/--
lemma `Indep.isBase_of_ground_subset_closure` / 引理 `Indep.isBase_of_ground_subset_closure`

English:
lemma Indep.isBase_of_ground_subset_closure
  given: (hI : M.Indep I) (h : M.E subseteq M.closure I)
  proof: by
  rw [← isBasis_ground_iff]; exact hI.isBasis_of_subset_of_subset_closure hI.subset_ground h

中文:
引理 Indep.isBase_of_ground_subset_closure
  条件: (hI : M.Indep I) (h : M.E subseteq M.closure I)
  证明: by
  rw [← isBasis_ground_iff]; exact hI.isBasis_of_subset_of_subset_closure hI.subset_ground h

Depends on / 依赖: hI.isBasis_of_subset_of_subset_closure, hI.subset_ground, isBasis_ground_iff, isBasis_of_subset_of_subset_closure, subset_ground
-/
lemma Indep.isBase_of_ground_subset_closure (hI : M.Indep I) (h : M.E subseteq M.closure I) :
    M.IsBase I := by
  rw [← isBasis_ground_iff]; exact hI.isBasis_of_subset_of_subset_closure hI.subset_ground h

/--
lemma `IsBase.closure_eq` / 引理 `IsBase.closure_eq`

English:
lemma IsBase.closure_eq
  given: (hB : M.IsBase B)
  statement: M.closure B = M.E
  proof: by
  rw [← isBasis_ground_iff] at hB; rw [hB.closure_eq_closure, closure_ground]

中文:
引理 IsBase.closure_eq
  条件: (hB : M.IsBase B)
  结论: M.closure B = M.E
  证明: by
  rw [← isBasis_ground_iff] at hB; rw [hB.closure_eq_closure, closure_ground]

Depends on / 依赖: closure_eq_closure, closure_ground, hB.closure_eq_closure, isBasis_ground_iff
-/
lemma IsBase.closure_eq (hB : M.IsBase B) : M.closure B = M.E := by
  rw [← isBasis_ground_iff] at hB; rw [hB.closure_eq_closure, closure_ground]

/--
lemma `IsBase.closure_of_superset` / 引理 `IsBase.closure_of_superset`

English:
lemma IsBase.closure_of_superset
  given: (hB : M.IsBase B) (hBX : B subseteq X)
  statement: M.closure X = M.E
  proof: (M.closure_subset_ground _).antisymm (hB.closure_eq ▸ M.closure_subset_closure hBX)

中文:
引理 IsBase.closure_of_superset
  条件: (hB : M.IsBase B) (hBX : B subseteq X)
  结论: M.closure X = M.E
  证明: (M.closure_subset_ground _).antisymm (hB.closure_eq ▸ M.closure_subset_closure hBX)

Depends on / 依赖: M.closure_subset_closure, M.closure_subset_ground, antisymm, closure_eq, closure_subset_closure, closure_subset_ground, hB.closure_eq
-/
lemma IsBase.closure_of_superset (hB : M.IsBase B) (hBX : B subseteq X) : M.closure X = M.E :=
  (M.closure_subset_ground _).antisymm (hB.closure_eq ▸ M.closure_subset_closure hBX)

/--
lemma `isBase_iff_indep_closure_eq` / 引理 `isBase_iff_indep_closure_eq`

English:
lemma isBase_iff_indep_closure_eq
  statement: M.IsBase B ↔ M.Indep B ∧ M.closure B = M.E
  proof: by
  rw [← isBasis_ground_iff]; rw [isBasis_iff_indep_subset_closure]; rw [and_congr_right_iff]
  exact fun hI => ⟨fun h => (M.closure_subset_ground _).antisymm h.2,
    fun h => ⟨(M.subset_closure B).trans_eq h, h.symm.subset⟩⟩

中文:
引理 isBase_iff_indep_closure_eq
  结论: M.IsBase B ↔ M.Indep B ∧ M.closure B = M.E
  证明: by
  rw [← isBasis_ground_iff]; rw [isBasis_iff_indep_subset_closure]; rw [and_congr_right_iff]
  exact fun hI => ⟨fun h => (M.closure_subset_ground _).antisymm h.2,
    fun h => ⟨(M.subset_closure B).trans_eq h, h.symm.subset⟩⟩

Depends on / 依赖: M.closure_subset_ground, M.subset_closure, and_congr_right_iff, antisymm, closure_subset_ground, h.symm.subset, isBasis_ground_iff, isBasis_iff_indep_subset_closure, subset, subset_closure, trans_eq
-/
lemma isBase_iff_indep_closure_eq : M.IsBase B ↔ M.Indep B ∧ M.closure B = M.E := by
  rw [← isBasis_ground_iff]; rw [isBasis_iff_indep_subset_closure]; rw [and_congr_right_iff]
  exact fun hI => ⟨fun h => (M.closure_subset_ground _).antisymm h.2,
    fun h => ⟨(M.subset_closure B).trans_eq h, h.symm.subset⟩⟩

/--
lemma `IsBase.exchange_base_of_notMem_closure` / 引理 `IsBase.exchange_base_of_notMem_closure`

English:
lemma IsBase.exchange_base_of_notMem_closure
  statement: (hB : M.IsBase B) (he : e in B)
  proof: by
  obtain rfl | hne := eq_or_ne f e
  · simpa [he]
  have ⟨hi, hfB⟩ : M.Indep (insert f (B \ {e})) ∧ f ∉ B := by
    simpa [(hB.indep.sdiff _).notMem_closure_iff, hne] using hf
  exact hB.exchange_isBase_of_indep hfB hi

中文:
引理 IsBase.exchange_base_of_notMem_closure
  结论: (hB : M.IsBase B) (he : e in B)
  证明: by
  obtain rfl | hne := eq_or_ne f e
  · simpa [he]
  have ⟨hi, hfB⟩ : M.Indep (insert f (B \ {e})) ∧ f ∉ B := by
    simpa [(hB.indep.sdiff _).notMem_closure_iff, hne] using hf
  exact hB.exchange_isBase_of_indep hfB hi

Depends on / 依赖: IsBase, M.Indep, M.IsBase, aesop_mat, eq_or_ne, exchange_isBase_of_indep, hB.exchange_isBase_of_indep, hB.indep.sdiff, insert, notMem_closure_iff
-/
lemma IsBase.exchange_base_of_notMem_closure (hB : M.IsBase B) (he : e in B)
    (hf : f ∉ M.closure (B \ {e})) (hfE : f in M.E := by aesop_mat) :
    M.IsBase (insert f (B \ {e})) := by
  obtain rfl | hne := eq_or_ne f e
  · simpa [he]
  have ⟨hi, hfB⟩ : M.Indep (insert f (B \ {e})) ∧ f ∉ B := by
    simpa [(hB.indep.sdiff _).notMem_closure_iff, hne] using hf
  exact hB.exchange_isBase_of_indep hfB hi

/--
lemma `Indep.isBase_iff_ground_subset_closure` / 引理 `Indep.isBase_iff_ground_subset_closure`

English:
lemma Indep.isBase_iff_ground_subset_closure
  given: (hI : M.Indep I)
  statement: M.IsBase I ↔ M.E subseteq M.closure I
  proof: ⟨fun h => h.closure_eq.symm.subset, hI.isBase_of_ground_subset_closure⟩

中文:
引理 Indep.isBase_iff_ground_subset_closure
  条件: (hI : M.Indep I)
  结论: M.IsBase I ↔ M.E subseteq M.closure I
  证明: ⟨fun h => h.closure_eq.symm.subset, hI.isBase_of_ground_subset_closure⟩

Depends on / 依赖: closure_eq, h.closure_eq.symm.subset, hI.isBase_of_ground_subset_closure, isBase_of_ground_subset_closure, subset
-/
lemma Indep.isBase_iff_ground_subset_closure (hI : M.Indep I) : M.IsBase I ↔ M.E subseteq M.closure I :=
  ⟨fun h => h.closure_eq.symm.subset, hI.isBase_of_ground_subset_closure⟩

/--
lemma `Indep.closure_inter_eq_self_of_subset` / 引理 `Indep.closure_inter_eq_self_of_subset`

English:
lemma Indep.closure_inter_eq_self_of_subset
  given: (hI : M.Indep I) (hJI : J subseteq I)
  proof: by
  have hJ := hI.subset hJI
  rw [subset_antisymm_iff]; rw [and_iff_left (subset_inter (M.subset_closure _) hJI)]
  rintro e ⟨heJ, heI⟩
  exact hJ.isBasis_closure.mem_of_insert_indep heJ (hI.subset (insert_subset heI hJI))

中文:
引理 Indep.closure_inter_eq_self_of_subset
  条件: (hI : M.Indep I) (hJI : J subseteq I)
  证明: by
  have hJ := hI.subset hJI
  rw [subset_antisymm_iff]; rw [and_iff_left (subset_inter (M.subset_closure _) hJI)]
  rintro e ⟨heJ, heI⟩
  exact hJ.isBasis_closure.mem_of_insert_indep heJ (hI.subset (insert_subset heI hJI))

Depends on / 依赖: M.subset_closure, and_iff_left, hI.subset, hJ.isBasis_closure.mem_of_insert_indep, insert_subset, isBasis_closure, mem_of_insert_indep, subset, subset_antisymm_iff, subset_closure, subset_inter
-/
lemma Indep.closure_inter_eq_self_of_subset (hI : M.Indep I) (hJI : J subseteq I) :
    M.closure J inter I = J := by
  have hJ := hI.subset hJI
  rw [subset_antisymm_iff]; rw [and_iff_left (subset_inter (M.subset_closure _) hJI)]
  rintro e ⟨heJ, heI⟩
  exact hJ.isBasis_closure.mem_of_insert_indep heJ (hI.subset (insert_subset heI hJI))

/--
lemma `Indep.closure_sInter_eq_biInter_closure_of_forall_subset` / 引理 `Indep.closure_sInter_eq_biInter_closure_of_forall_subset`

English:
lemma Indep.closure_sInter_eq_biInter_closure_of_forall_subset
  statement: {Js : Set (Set α)} (hI : M.Indep I)
  proof: by
  rw [subset_antisymm_iff]; rw [subset_iInter₂_iff]
  have hiX : ⋂₀ Js subseteq I := (sInter_subset_of_mem hne.some_mem).trans (hIs _ hne.some_mem)
  have hiI := hI.subset hiX
  refine ⟨ fun X hX => M.closure_subset_closure (sInter_subset_of_mem hX),
    fun e he => by_contra fun he' => ?_⟩
  rw 

中文:
引理 Indep.closure_s整数er_eq_bi整数er_closure_of_对任意_subset
  结论: {Js : 集合 (集合 α)} (hI : M.Indep I)
  证明: by
  rw [subset_antisymm_iff]; rw [subset_iInter₂_iff]
  have hiX : ⋂₀ Js subseteq I := (sInter_subset_of_mem hne.some_mem).trans (hIs _ hne.some_mem)
  have hiI := hI.subset hiX
  refine ⟨ fun X hX => M.closure_subset_closure (sInter_subset_of_mem hX),
    fun e he => by_contra fun he' => ?_⟩
  rw 

Depends on / 依赖: M.closure_subset_closure, M.closure_subset_ground, closure_inter_eq, closure_subset_closure, closure_subset_ground, hI.closure_inter_eq, hI.subset, hiI.subset_ground, hne.some_mem, mem_closure_of_mem, sInter_subset_of_mem, some_mem, subset, subset_antisymm_iff, subset_ground, subseteq
-/
lemma Indep.closure_sInter_eq_biInter_closure_of_forall_subset {Js : Set (Set α)} (hI : M.Indep I)
    (hne : Js.Nonempty) (hIs : forall J in Js, J subseteq I) : M.closure (⋂₀ Js) = (⋂ J in Js, M.closure J) := by
  rw [subset_antisymm_iff]; rw [subset_iInter₂_iff]
  have hiX : ⋂₀ Js subseteq I := (sInter_subset_of_mem hne.some_mem).trans (hIs _ hne.some_mem)
  have hiI := hI.subset hiX
  refine ⟨ fun X hX => M.closure_subset_closure (sInter_subset_of_mem hX),
    fun e he => by_contra fun he' => ?_⟩
  rw [mem_iInter₂] at he
  have heEI : e in M.E \ I := by
    refine ⟨M.closure_subset_ground _ (he _ hne.some_mem), fun heI => he' ?_⟩
    refine mem_closure_of_mem _ (fun X hX' => ?_) hiI.subset_ground
    rw [← hI.closure_inter_eq_self_of_subset (hIs X hX')]
    exact ⟨he X hX', heI⟩
  rw [hiI.notMem_closure_iff_of_notMem (notMem_subset hiX heEI.2)] at he'
  obtain ⟨J, hJI, heJ⟩ := he'.subset_isBasis_of_subset (insert_subset_insert hiX)
    (insert_subset heEI.1 hI.subset_ground)
  have hIb : M.IsBasis I (insert e I) := by
    rw [hI.insert_isBasis_iff_mem_closure]
    exact (M.closure_subset_closure (hIs _ hne.some_mem)) (he _ hne.some_mem)
  obtain ⟨f, hfIJ, hfb⟩ := hJI.exchange hIb ⟨heJ (mem_insert e _), heEI.2⟩
  obtain rfl := hI.eq_of_isBasis (hfb.isBasis_subset (insert_subset hfIJ.1
    (by (rw [sdiff_subset_iff, singleton_union]; exact hJI.subset))) (subset_insert _ _))
  refine hfIJ.2 (heJ (mem_insert_of_mem _ fun X hX' => by_contra fun hfX => ?_))
  obtain (hd | heX) := ((hI.subset (hIs X hX')).mem_closure_iff).mp (he _ hX')
  · refine (hJI.indep.subset (insert_subset (heJ (mem_insert _ _)) ?_)).not_dep hd
    specialize hIs _ hX'
    rw [← singleton_union]; rw [← sdiff_subset_iff]; rw [sdiff_singleton_eq_self hfX] at hIs
    exact hIs.trans sdiff_subset
  exact heEI.2 (hIs _ hX' heX)

/--
lemma `closure_iInter_eq_iInter_closure_of_iUnion_indep` / 引理 `closure_iInter_eq_iInter_closure_of_iUnion_indep`

English:
lemma closure_iInter_eq_iInter_closure_of_iUnion_indep
  statement: [hι : Nonempty ι] (Is : ι -> Set α)
  proof: by
  convert!
    h.closure_sInter_eq_biInter_closure_of_forall_subset (range_nonempty Is)
      (by simp [subset_iUnion])
  simp

中文:
引理 closure_i整数er_eq_i整数er_closure_of_iUnion_indep
  结论: [hι : 非空 ι] (Is : ι -> 集合 α)
  证明: by
  convert!
    h.closure_sInter_eq_biInter_closure_of_forall_subset (range_nonempty Is)
      (by simp [subset_iUnion])
  simp

Depends on / 依赖: closure_sInter_eq_biInter_closure_of_forall_subset, convert, h.closure_sInter_eq_biInter_closure_of_forall_subset, range_nonempty, subset_iUnion
-/
lemma closure_iInter_eq_iInter_closure_of_iUnion_indep [hι : Nonempty ι] (Is : ι -> Set α)
    (h : M.Indep (⋃ i, Is i)) : M.closure (⋂ i, Is i) = (⋂ i, M.closure (Is i)) := by
  convert!
    h.closure_sInter_eq_biInter_closure_of_forall_subset (range_nonempty Is)
      (by simp [subset_iUnion])
  simp

/--
lemma `closure_sInter_eq_biInter_closure_of_sUnion_indep` / 引理 `closure_sInter_eq_biInter_closure_of_sUnion_indep`

English:
lemma closure_sInter_eq_biInter_closure_of_sUnion_indep
  statement: (Is : Set (Set α)) (hIs : Is.Nonempty)
  proof: h.closure_sInter_eq_biInter_closure_of_forall_subset hIs (fun _ => subset_sUnion_of_mem)

中文:
引理 closure_s整数er_eq_bi整数er_closure_of_sUnion_indep
  结论: (Is : 集合 (集合 α)) (hIs : Is.非空)
  证明: h.closure_sInter_eq_biInter_closure_of_forall_subset hIs (fun _ => subset_sUnion_of_mem)

Depends on / 依赖: closure_sInter_eq_biInter_closure_of_forall_subset, h.closure_sInter_eq_biInter_closure_of_forall_subset, subset_sUnion_of_mem
-/
lemma closure_sInter_eq_biInter_closure_of_sUnion_indep (Is : Set (Set α)) (hIs : Is.Nonempty)
    (h : M.Indep (⋃₀ Is)) : M.closure (⋂₀ Is) = (⋂ I in Is, M.closure I) :=
  h.closure_sInter_eq_biInter_closure_of_forall_subset hIs (fun _ => subset_sUnion_of_mem)

/--
lemma `closure_biInter_eq_biInter_closure_of_biUnion_indep` / 引理 `closure_biInter_eq_biInter_closure_of_biUnion_indep`

English:
lemma closure_biInter_eq_biInter_closure_of_biUnion_indep
  statement: {ι : Type*} {A : Set ι} (hA : A.Nonempty)
  proof: by
  have := hA.coe_sort
  convert! closure_iInter_eq_iInter_closure_of_iUnion_indep (Is := fun i : A => I i) (by simpa) <;>
  simp

中文:
引理 closure_bi整数er_eq_bi整数er_closure_of_biUnion_indep
  结论: {ι : 类型} {A : 集合 ι} (hA : A.非空)
  证明: by
  have := hA.coe_sort
  convert! closure_iInter_eq_iInter_closure_of_iUnion_indep (Is := fun i : A => I i) (by simpa) <;>
  simp

Depends on / 依赖: closure_iInter_eq_iInter_closure_of_iUnion_indep, coe_sort, convert, hA.coe_sort
-/
lemma closure_biInter_eq_biInter_closure_of_biUnion_indep {ι : Type*} {A : Set ι} (hA : A.Nonempty)
    {I : ι -> Set α} (h : M.Indep (⋃ i in A, I i)) :
    M.closure (⋂ i in A, I i) = ⋂ i in A, M.closure (I i) := by
  have := hA.coe_sort
  convert! closure_iInter_eq_iInter_closure_of_iUnion_indep (Is := fun i : A => I i) (by simpa) <;>
  simp

/--
lemma `Indep.closure_iInter_eq_biInter_closure_of_forall_subset` / 引理 `Indep.closure_iInter_eq_biInter_closure_of_forall_subset`

English:
lemma Indep.closure_iInter_eq_biInter_closure_of_forall_subset
  statement: [Nonempty ι] {Js : ι -> Set α}
  proof: closure_iInter_eq_iInter_closure_of_iUnion_indep _ (hI.subset <| by simpa)

中文:
引理 Indep.closure_i整数er_eq_bi整数er_closure_of_对任意_subset
  结论: [非空 ι] {Js : ι -> 集合 α}
  证明: closure_iInter_eq_iInter_closure_of_iUnion_indep _ (hI.subset <| by simpa)

Depends on / 依赖: closure_iInter_eq_iInter_closure_of_iUnion_indep, hI.subset, subset
-/
lemma Indep.closure_iInter_eq_biInter_closure_of_forall_subset [Nonempty ι] {Js : ι -> Set α}
    (hI : M.Indep I) (hJs : forall i, Js i subseteq I) : M.closure (⋂ i, Js i) = ⋂ i, M.closure (Js i) :=
  closure_iInter_eq_iInter_closure_of_iUnion_indep _ (hI.subset <| by simpa)

/--
lemma `Indep.closure_inter_eq_inter_closure` / 引理 `Indep.closure_inter_eq_inter_closure`

English:
lemma Indep.closure_inter_eq_inter_closure
  given: (h : M.Indep (I union J))
  proof: by
  rw [inter_eq_iInter]; rw [closure_iInter_eq_iInter_closure_of_iUnion_indep]; rw [inter_eq_iInter]
  · exact iInter_congr (by simp)
  rwa [← union_eq_iUnion]

中文:
引理 Indep.closure_inter_eq_inter_closure
  条件: (h : M.Indep (I union J))
  证明: by
  rw [inter_eq_iInter]; rw [closure_iInter_eq_iInter_closure_of_iUnion_indep]; rw [inter_eq_iInter]
  · exact iInter_congr (by simp)
  rwa [← union_eq_iUnion]

Depends on / 依赖: closure_iInter_eq_iInter_closure_of_iUnion_indep, iInter_congr, inter_eq_iInter, union_eq_iUnion
-/
lemma Indep.closure_inter_eq_inter_closure (h : M.Indep (I union J)) :
    M.closure (I inter J) = M.closure I inter M.closure J := by
  rw [inter_eq_iInter]; rw [closure_iInter_eq_iInter_closure_of_iUnion_indep]; rw [inter_eq_iInter]
  · exact iInter_congr (by simp)
  rwa [← union_eq_iUnion]

/--
lemma `Indep.inter_isBasis_biInter` / 引理 `Indep.inter_isBasis_biInter`

English:
lemma Indep.inter_isBasis_biInter
  statement: {ι : Type*} (hI : M.Indep I) {X : ι -> Set α} {A : Set ι}
  proof: by
  refine (hI.inter_left _).isBasis_of_subset_of_subset_closure inter_subset_left ?_
  simp_rw [← biInter_inter hA,
  closure_biInter_eq_biInter_closure_of_biUnion_indep hA (I := fun i => (X i) inter I)
      (hI.subset (by simp)), subset_iInter_iff]
  exact fun i hiA => (biInter_subset_of_mem hiA

中文:
引理 Indep.inter_isBasis_bi整数er
  结论: {ι : 类型} (hI : M.Indep I) {X : ι -> 集合 α} {A : 集合 ι}
  证明: by
  refine (hI.inter_left _).isBasis_of_subset_of_subset_closure inter_subset_left ?_
  simp_rw [← biInter_inter hA,
  closure_biInter_eq_biInter_closure_of_biUnion_indep hA (I := fun i => (X i) inter I)
      (hI.subset (by simp)), subset_iInter_iff]
  exact fun i hiA => (biInter_subset_of_mem hiA

Depends on / 依赖: biInter_inter, biInter_subset_of_mem, closure_biInter_eq_biInter_closure_of_biUnion_indep, hI.inter_left, hI.subset, inter_left, inter_subset_left, isBasis_of_subset_of_subset_closure, simp_rw, subset, subset_closure, subset_iInter_iff
-/
lemma Indep.inter_isBasis_biInter {ι : Type*} (hI : M.Indep I) {X : ι -> Set α} {A : Set ι}
    (hA : A.Nonempty) (h : forall i in A, M.IsBasis ((X i) inter I) (X i)) :
    M.IsBasis ((⋂ i in A, X i) inter I) (⋂ i in A, X i) := by
  refine (hI.inter_left _).isBasis_of_subset_of_subset_closure inter_subset_left ?_
  simp_rw [← biInter_inter hA,
  closure_biInter_eq_biInter_closure_of_biUnion_indep hA (I := fun i => (X i) inter I)
      (hI.subset (by simp)), subset_iInter_iff]
  exact fun i hiA => (biInter_subset_of_mem hiA).trans (h i hiA).subset_closure

/--
lemma `Indep.inter_isBasis_iInter` / 引理 `Indep.inter_isBasis_iInter`

English:
lemma Indep.inter_isBasis_iInter
  statement: [Nonempty ι] {X : ι -> Set α} (hI : M.Indep I)
  proof: by
  convert!
    hI.inter_isBasis_biInter (ι := PLift ι) univ_nonempty (X := fun i => X i.down)
      (by simpa using fun (i : PLift ι) => h i.down) <;>
  · simp only [mem_univ, iInter_true]
    exact (iInter_plift_down X).symm

中文:
引理 Indep.inter_isBasis_i整数er
  结论: [非空 ι] {X : ι -> 集合 α} (hI : M.Indep I)
  证明: by
  convert!
    hI.inter_isBasis_biInter (ι := PLift ι) univ_nonempty (X := fun i => X i.down)
      (by simpa using fun (i : PLift ι) => h i.down) <;>
  · simp only [mem_univ, iInter_true]
    exact (iInter_plift_down X).symm

Depends on / 依赖: convert, hI.inter_isBasis_biInter, i.down, iInter_plift_down, iInter_true, inter_isBasis_biInter, mem_univ, univ_nonempty
-/
lemma Indep.inter_isBasis_iInter [Nonempty ι] {X : ι -> Set α} (hI : M.Indep I)
    (h : forall i, M.IsBasis ((X i) inter I) (X i)) : M.IsBasis ((⋂ i, X i) inter I) (⋂ i, X i) := by
  convert!
    hI.inter_isBasis_biInter (ι := PLift ι) univ_nonempty (X := fun i => X i.down)
      (by simpa using fun (i : PLift ι) => h i.down) <;>
  · simp only [mem_univ, iInter_true]
    exact (iInter_plift_down X).symm

/--
lemma `Indep.inter_isBasis_sInter` / 引理 `Indep.inter_isBasis_sInter`

English:
lemma Indep.inter_isBasis_sInter
  statement: {Xs : Set (Set α)} (hI : M.Indep I) (hXs : Xs.Nonempty)
  proof: by
  rw [sInter_eq_biInter]
  exact hI.inter_isBasis_biInter hXs h

中文:
引理 Indep.inter_isBasis_s整数er
  结论: {Xs : 集合 (集合 α)} (hI : M.Indep I) (hXs : Xs.非空)
  证明: by
  rw [sInter_eq_biInter]
  exact hI.inter_isBasis_biInter hXs h

Depends on / 依赖: hI.inter_isBasis_biInter, inter_isBasis_biInter, sInter_eq_biInter
-/
lemma Indep.inter_isBasis_sInter {Xs : Set (Set α)} (hI : M.Indep I) (hXs : Xs.Nonempty)
    (h : forall X in Xs, M.IsBasis (X inter I) X) : M.IsBasis (⋂₀ Xs inter I) (⋂₀ Xs) := by
  rw [sInter_eq_biInter]
  exact hI.inter_isBasis_biInter hXs h

/--
lemma `isBasis_iff_isBasis_closure_of_subset` / 引理 `isBasis_iff_isBasis_closure_of_subset`

English:
lemma isBasis_iff_isBasis_closure_of_subset
  given: (hIX : I subseteq X) (hX : X subseteq M.E := by aesop_mat)
  proof: ⟨fun h => h.isBasis_closure_right, fun h => h.isBasis_subset hIX (M.subset_closure X hX)⟩

中文:
引理 isBasis_iff_isBasis_closure_of_subset
  条件: (hIX : I subseteq X) (hX : X subseteq M.E := by aesop_mat)
  证明: ⟨fun h => h.isBasis_closure_right, fun h => h.isBasis_subset hIX (M.subset_closure X hX)⟩

Depends on / 依赖: IsBasis, M.IsBasis, M.closure, M.subset_closure, aesop_mat, closure, h.isBasis_closure_right, h.isBasis_subset, isBasis_closure_right, isBasis_subset, subset_closure
-/
lemma isBasis_iff_isBasis_closure_of_subset (hIX : I subseteq X) (hX : X subseteq M.E := by aesop_mat) :
    M.IsBasis I X ↔ M.IsBasis I (M.closure X) :=
  ⟨fun h => h.isBasis_closure_right, fun h => h.isBasis_subset hIX (M.subset_closure X hX)⟩

/--
lemma `isBasis_iff_isBasis_closure_of_subset'` / 引理 `isBasis_iff_isBasis_closure_of_subset'`

English:
lemma isBasis_iff_isBasis_closure_of_subset'
  given: (hIX : I subseteq X)
  proof: ⟨fun h => ⟨h.isBasis_closure_right, h.subset_ground⟩,
    fun h => h.1.isBasis_subset hIX (M.subset_closure X h.2)⟩

中文:
引理 isBasis_iff_isBasis_closure_of_subset'
  条件: (hIX : I subseteq X)
  证明: ⟨fun h => ⟨h.isBasis_closure_right, h.subset_ground⟩,
    fun h => h.1.isBasis_subset hIX (M.subset_closure X h.2)⟩

Depends on / 依赖: M.subset_closure, h.isBasis_closure_right, h.subset_ground, isBasis_closure_right, isBasis_subset, subset_closure, subset_ground
-/
lemma isBasis_iff_isBasis_closure_of_subset' (hIX : I subseteq X) :
    M.IsBasis I X ↔ M.IsBasis I (M.closure X) ∧ X subseteq M.E :=
  ⟨fun h => ⟨h.isBasis_closure_right, h.subset_ground⟩,
    fun h => h.1.isBasis_subset hIX (M.subset_closure X h.2)⟩

/--
lemma `isBasis'_iff_isBasis_closure` / 引理 `isBasis'_iff_isBasis_closure`

English:
lemma isBasis'_iff_isBasis_closure
  statement: M.IsBasis' I X ↔ M.IsBasis I (M.closure X) ∧ I subseteq X
  proof: by
  rw [← closure_inter_ground]; rw [isBasis'_iff_isBasis_inter_ground]
  exact ⟨fun h => ⟨h.isBasis_closure_right, h.subset.trans inter_subset_left⟩,
    fun h => h.1.isBasis_subset (subset_inter h.2 h.1.indep.subset_ground) (M.subset_closure _)⟩

中文:
引理 isBasis'_iff_isBasis_closure
  结论: M.是基' I X ↔ M.是基 I (M.closure X) ∧ I subseteq X
  证明: by
  rw [← closure_inter_ground]; rw [isBasis'_iff_isBasis_inter_ground]
  exact ⟨fun h => ⟨h.isBasis_closure_right, h.subset.trans inter_subset_left⟩,
    fun h => h.1.isBasis_subset (subset_inter h.2 h.1.indep.subset_ground) (M.subset_closure _)⟩
-/
lemma isBasis'_iff_isBasis_closure : M.IsBasis' I X ↔ M.IsBasis I (M.closure X) ∧ I subseteq X := by
  rw [← closure_inter_ground]; rw [isBasis'_iff_isBasis_inter_ground]
  exact ⟨fun h => ⟨h.isBasis_closure_right, h.subset.trans inter_subset_left⟩,
    fun h => h.1.isBasis_subset (subset_inter h.2 h.1.indep.subset_ground) (M.subset_closure _)⟩

/--
lemma `exists_isBasis_inter_ground_isBasis_closure` / 引理 `exists_isBasis_inter_ground_isBasis_closure`

English:
lemma exists_isBasis_inter_ground_isBasis_closure
  given: (M : Matroid α) (X : Set α)
  proof: by
  obtain ⟨I, hI⟩ := M.exists_isBasis (X inter M.E)
  have hI' := hI.isBasis_closure_right; rw [closure_inter_ground] at hI'
  exact ⟨_, hI, hI'⟩

中文:
引理 存在_isBasis_inter_ground_isBasis_closure
  条件: (M : 拟阵 α) (X : 集合 α)
  证明: by
  obtain ⟨I, hI⟩ := M.exists_isBasis (X inter M.E)
  have hI' := hI.isBasis_closure_right; rw [closure_inter_ground] at hI'
  exact ⟨_, hI, hI'⟩

Depends on / 依赖: M.exists_isBasis, closure_inter_ground, exists_isBasis, hI.isBasis_closure_right, isBasis_closure_right
-/
lemma exists_isBasis_inter_ground_isBasis_closure (M : Matroid α) (X : Set α) :
    exists I, M.IsBasis I (X inter M.E) ∧ M.IsBasis I (M.closure X) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis (X inter M.E)
  have hI' := hI.isBasis_closure_right; rw [closure_inter_ground] at hI'
  exact ⟨_, hI, hI'⟩

/--
lemma `IsBasis.isBasis_of_closure_eq_closure` / 引理 `IsBasis.isBasis_of_closure_eq_closure`

English:
lemma IsBasis.isBasis_of_closure_eq_closure
  statement: (hI : M.IsBasis I X) (hY : I subseteq Y)
  proof: by
  refine hI.indep.isBasis_of_subset_of_subset_closure hY ?_
  rw [hI.closure_eq_closure]; rw [h]
  exact M.subset_closure Y

中文:
引理 是基.isBasis_of_closure_eq_closure
  结论: (hI : M.是基 I X) (hY : I subseteq Y)
  证明: by
  refine hI.indep.isBasis_of_subset_of_subset_closure hY ?_
  rw [hI.closure_eq_closure]; rw [h]
  exact M.subset_closure Y

Depends on / 依赖: IsBasis, M.IsBasis, M.subset_closure, aesop_mat, closure_eq_closure, hI.closure_eq_closure, hI.indep.isBasis_of_subset_of_subset_closure, isBasis_of_subset_of_subset_closure, subset_closure
-/
lemma IsBasis.isBasis_of_closure_eq_closure (hI : M.IsBasis I X) (hY : I subseteq Y)
    (h : M.closure X = M.closure Y) (hYE : Y subseteq M.E := by aesop_mat) : M.IsBasis I Y := by
  refine hI.indep.isBasis_of_subset_of_subset_closure hY ?_
  rw [hI.closure_eq_closure]; rw [h]
  exact M.subset_closure Y

/--
lemma `isBasis_union_iff_indep_closure` / 引理 `isBasis_union_iff_indep_closure`

English:
lemma isBasis_union_iff_indep_closure
  statement: M.IsBasis I (I union X) ↔ M.Indep I ∧ X subseteq M.closure I
  proof: ⟨fun h => ⟨h.indep, subset_union_right.trans h.subset_closure⟩, fun ⟨hI, hXI⟩ =>
    hI.isBasis_closure.isBasis_subset subset_union_left (union_subset (M.subset_closure I) hXI)⟩

中文:
引理 isBasis_union_iff_indep_closure
  结论: M.是基 I (I union X) ↔ M.Indep I ∧ X subseteq M.closure I
  证明: ⟨fun h => ⟨h.indep, subset_union_right.trans h.subset_closure⟩, fun ⟨hI, hXI⟩ =>
    hI.isBasis_closure.isBasis_subset subset_union_left (union_subset (M.subset_closure I) hXI)⟩

Depends on / 依赖: M.subset_closure, h.indep, h.subset_closure, hI.isBasis_closure.isBasis_subset, isBasis_closure, isBasis_subset, subset_closure, subset_union_left, subset_union_right, subset_union_right.trans, union_subset
-/
lemma isBasis_union_iff_indep_closure : M.IsBasis I (I union X) ↔ M.Indep I ∧ X subseteq M.closure I :=
  ⟨fun h => ⟨h.indep, subset_union_right.trans h.subset_closure⟩, fun ⟨hI, hXI⟩ =>
    hI.isBasis_closure.isBasis_subset subset_union_left (union_subset (M.subset_closure I) hXI)⟩

/--
lemma `isBasis_iff_indep_closure` / 引理 `isBasis_iff_indep_closure`

English:
lemma isBasis_iff_indep_closure
  statement: M.IsBasis I X ↔ M.Indep I ∧ X subseteq M.closure I ∧ I subseteq X
  proof: ⟨fun h => ⟨h.indep, h.subset_closure, h.subset⟩, fun h =>
    (isBasis_union_iff_indep_closure.mpr ⟨h.1, h.2.1⟩).isBasis_subset h.2.2 subset_union_right⟩

中文:
引理 isBasis_iff_indep_closure
  结论: M.是基 I X ↔ M.Indep I ∧ X subseteq M.closure I ∧ I subseteq X
  证明: ⟨fun h => ⟨h.indep, h.subset_closure, h.subset⟩, fun h =>
    (isBasis_union_iff_indep_closure.mpr ⟨h.1, h.2.1⟩).isBasis_subset h.2.2 subset_union_right⟩

Depends on / 依赖: h.indep, h.subset, h.subset_closure, isBasis_subset, isBasis_union_iff_indep_closure, isBasis_union_iff_indep_closure.mpr, subset, subset_closure, subset_union_right
-/
lemma isBasis_iff_indep_closure : M.IsBasis I X ↔ M.Indep I ∧ X subseteq M.closure I ∧ I subseteq X :=
  ⟨fun h => ⟨h.indep, h.subset_closure, h.subset⟩, fun h =>
    (isBasis_union_iff_indep_closure.mpr ⟨h.1, h.2.1⟩).isBasis_subset h.2.2 subset_union_right⟩

/--
lemma `Indep.inter_isBasis_closure_iff_subset_closure_inter` / 引理 `Indep.inter_isBasis_closure_iff_subset_closure_inter`

English:
lemma Indep.inter_isBasis_closure_iff_subset_closure_inter
  given: {X : Set α} (hI : M.Indep I)
  proof: ⟨IsBasis.subset_closure, (hI.inter_left X).isBasis_of_subset_of_subset_closure inter_subset_left⟩

中文:
引理 Indep.inter_isBasis_closure_iff_subset_closure_inter
  条件: {X : 集合 α} (hI : M.Indep I)
  证明: ⟨IsBasis.subset_closure, (hI.inter_left X).isBasis_of_subset_of_subset_closure inter_subset_left⟩

Depends on / 依赖: IsBasis, IsBasis.subset_closure, hI.inter_left, inter_left, inter_subset_left, isBasis_of_subset_of_subset_closure, subset_closure
-/
lemma Indep.inter_isBasis_closure_iff_subset_closure_inter {X : Set α} (hI : M.Indep I) :
    M.IsBasis (X inter I) X ↔ X subseteq M.closure (X inter I) :=
  ⟨IsBasis.subset_closure, (hI.inter_left X).isBasis_of_subset_of_subset_closure inter_subset_left⟩

/--
lemma `IsBasis.closure_inter_isBasis_closure` / 引理 `IsBasis.closure_inter_isBasis_closure`

English:
lemma IsBasis.closure_inter_isBasis_closure
  given: (h : M.IsBasis (X inter I) X) (hI : M.Indep I)
  proof: by
  rw [hI.inter_isBasis_closure_iff_subset_closure_inter] at h ⊢
  exact (M.closure_subset_closure_of_subset_closure h).trans (M.closure_subset_closure
    (inter_subset_inter_left _ (h.trans (M.closure_subset_closure inter_subset_left))))

中文:
引理 是基.closure_inter_isBasis_closure
  条件: (h : M.是基 (X inter I) X) (hI : M.Indep I)
  证明: by
  rw [hI.inter_isBasis_closure_iff_subset_closure_inter] at h ⊢
  exact (M.closure_subset_closure_of_subset_closure h).trans (M.closure_subset_closure
    (inter_subset_inter_left _ (h.trans (M.closure_subset_closure inter_subset_left))))

Depends on / 依赖: M.closure_subset_closure, M.closure_subset_closure_of_subset_closure, closure_subset_closure, closure_subset_closure_of_subset_closure, h.trans, hI.inter_isBasis_closure_iff_subset_closure_inter, inter_isBasis_closure_iff_subset_closure_inter, inter_subset_inter_left, inter_subset_left
-/
lemma IsBasis.closure_inter_isBasis_closure (h : M.IsBasis (X inter I) X) (hI : M.Indep I) :
    M.IsBasis (M.closure X inter I) (M.closure X) := by
  rw [hI.inter_isBasis_closure_iff_subset_closure_inter] at h ⊢
  exact (M.closure_subset_closure_of_subset_closure h).trans (M.closure_subset_closure
    (inter_subset_inter_left _ (h.trans (M.closure_subset_closure inter_subset_left))))

/--
lemma `IsBasis.eq_of_closure_subset` / 引理 `IsBasis.eq_of_closure_subset`

English:
lemma IsBasis.eq_of_closure_subset
  given: (hI : M.IsBasis I X) (hJI : J subseteq I) (hJ : X subseteq M.closure J)
  proof: by
  rw [← hI.indep.closure_inter_eq_self_of_subset hJI]; rw [inter_eq_self_of_subset_right]
  exact hI.subset.trans hJ

中文:
引理 是基.eq_of_closure_subset
  条件: (hI : M.是基 I X) (hJI : J subseteq I) (hJ : X subseteq M.closure J)
  证明: by
  rw [← hI.indep.closure_inter_eq_self_of_subset hJI]; rw [inter_eq_self_of_subset_right]
  exact hI.subset.trans hJ

Depends on / 依赖: closure_inter_eq_self_of_subset, hI.indep.closure_inter_eq_self_of_subset, hI.subset.trans, inter_eq_self_of_subset_right, subset
-/
lemma IsBasis.eq_of_closure_subset (hI : M.IsBasis I X) (hJI : J subseteq I) (hJ : X subseteq M.closure J) :
    J = I := by
  rw [← hI.indep.closure_inter_eq_self_of_subset hJI]; rw [inter_eq_self_of_subset_right]
  exact hI.subset.trans hJ

/--
lemma `IsBasis.insert_isBasis_insert_of_notMem_closure` / 引理 `IsBasis.insert_isBasis_insert_of_notMem_closure`

English:
lemma IsBasis.insert_isBasis_insert_of_notMem_closure
  statement: (hIX : M.IsBasis I X) (heI : e ∉ M.closure I)
  proof: hIX.insert_isBasis_insert hIX.indep.insert_indep_iff.2 .inl ⟨heE, heI⟩

中文:
引理 是基.insert_isBasis_insert_of_notMem_closure
  结论: (hIX : M.是基 I X) (heI : e ∉ M.closure I)
  证明: hIX.insert_isBasis_insert hIX.indep.insert_indep_iff.2 .inl ⟨heE, heI⟩

Depends on / 依赖: IsBasis, M.IsBasis, aesop_mat, hIX.indep.insert_indep_iff, hIX.insert_isBasis_insert, insert, insert_indep_iff, insert_isBasis_insert
-/
lemma IsBasis.insert_isBasis_insert_of_notMem_closure (hIX : M.IsBasis I X) (heI : e ∉ M.closure I)
    (heE : e in M.E := by aesop_mat) : M.IsBasis (insert e I) (insert e X) :=
hIX.insert_isBasis_insert hIX.indep.insert_indep_iff.2 .inl ⟨heE, heI⟩

/--
lemma `empty_isBasis_iff` / 引理 `empty_isBasis_iff`

English:
lemma empty_isBasis_iff
  statement: M.IsBasis ∅ X ↔ X subseteq M.closure ∅
  proof: by
  rw [isBasis_iff_indep_closure]; rw [and_iff_right M.empty_indep]; rw [and_iff_left (empty_subset _)]

中文:
引理 empty_isBasis_iff
  结论: M.是基 ∅ X ↔ X subseteq M.closure ∅
  证明: by
  rw [isBasis_iff_indep_closure]; rw [and_iff_right M.empty_indep]; rw [and_iff_left (empty_subset _)]
-/
@[simp] lemma empty_isBasis_iff : M.IsBasis ∅ X ↔ X subseteq M.closure ∅ := by
  rw [isBasis_iff_indep_closure]; rw [and_iff_right M.empty_indep]; rw [and_iff_left (empty_subset _)]

/--
lemma `indep_iff_forall_notMem_closure_sdiff` / 引理 `indep_iff_forall_notMem_closure_sdiff`

English:
lemma indep_iff_forall_notMem_closure_sdiff
  given: (hI : I subseteq M.E := by aesop_mat)
  proof: by
  use fun h e heI he => ((h.closure_inter_eq_self_of_subset sdiff_subset).subset ⟨he, heI⟩).2 rfl
  intro h
  obtain ⟨J, hJ⟩ := M.exists_isBasis I
  convert! hJ.indep
  refine hJ.subset.antisymm' (fun e he => by_contra fun heJ => h he ?_)
  exact mem_of_mem_of_subset
    (hJ.subset_closure he) (M

中文:
引理 indep_iff_对任意_notMem_closure_sdiff
  条件: (hI : I subseteq M.E := by aesop_mat)
  证明: by
  use fun h e heI he => ((h.closure_inter_eq_self_of_subset sdiff_subset).subset ⟨he, heI⟩).2 rfl
  intro h
  obtain ⟨J, hJ⟩ := M.exists_isBasis I
  convert! hJ.indep
  refine hJ.subset.antisymm' (fun e he => by_contra fun heJ => h he ?_)
  exact mem_of_mem_of_subset
    (hJ.subset_closure he) (M

Depends on / 依赖: M.Indep, M.closure, M.closure_subset_closure, M.exists_isBasis, aesop_mat, antisymm, closure, closure_inter_eq_self_of_subset, closure_subset_closure, convert, exists_isBasis, h.closure_inter_eq_self_of_subset, hJ.indep, hJ.subset, hJ.subset.antisymm, hJ.subset_closure, mem_of_mem_of_subset, sdiff_subset, subset, subset_closure
-/
lemma indep_iff_forall_notMem_closure_sdiff (hI : I subseteq M.E := by aesop_mat) :
    M.Indep I ↔ forall ⦃e⦄, e in I -> e ∉ M.closure (I \ {e}) := by
  use fun h e heI he => ((h.closure_inter_eq_self_of_subset sdiff_subset).subset ⟨he, heI⟩).2 rfl
  intro h
  obtain ⟨J, hJ⟩ := M.exists_isBasis I
  convert! hJ.indep
  refine hJ.subset.antisymm' (fun e he => by_contra fun heJ => h he ?_)
  exact mem_of_mem_of_subset
    (hJ.subset_closure he) (M.closure_subset_closure (subset_sdiff_singleton hJ.subset heJ))

@[deprecated (since := "2026-06-03")]
alias indep_iff_forall_notMem_closure_diff := indep_iff_forall_notMem_closure_sdiff

/--
lemma `indep_iff_forall_notMem_closure_sdiff'` / 引理 `indep_iff_forall_notMem_closure_sdiff'`

English:
lemma indep_iff_forall_notMem_closure_sdiff'
  proof: ⟨fun h => ⟨h.subset_ground, (indep_iff_forall_notMem_closure_sdiff h.subset_ground).mp h⟩, fun h =>
    (indep_iff_forall_notMem_closure_sdiff h.1).mpr h.2⟩

@[deprecated (since := "2026-06-03")]
alias indep_iff_forall_notMem_closure_diff' := indep_iff_forall_notMem_closure_sdiff'

中文:
引理 indep_iff_对任意_notMem_closure_sdiff'
  证明: ⟨fun h => ⟨h.subset_ground, (indep_iff_forall_notMem_closure_sdiff h.subset_ground).mp h⟩, fun h =>
    (indep_iff_forall_notMem_closure_sdiff h.1).mpr h.2⟩

@[deprecated (since := "2026-06-03")]
alias indep_iff_forall_notMem_closure_diff' := indep_iff_forall_notMem_closure_sdiff'

Depends on / 依赖: h.subset_ground, indep_iff_forall_notMem_closure_sdiff, subset_ground
-/
lemma indep_iff_forall_notMem_closure_sdiff' :
    M.Indep I ↔ I subseteq M.E ∧ forall e in I, e ∉ M.closure (I \ {e}) :=
  ⟨fun h => ⟨h.subset_ground, (indep_iff_forall_notMem_closure_sdiff h.subset_ground).mp h⟩, fun h =>
    (indep_iff_forall_notMem_closure_sdiff h.1).mpr h.2⟩

@[deprecated (since := "2026-06-03")]
alias indep_iff_forall_notMem_closure_diff' := indep_iff_forall_notMem_closure_sdiff'

/--
lemma `Indep.notMem_closure_sdiff_of_mem` / 引理 `Indep.notMem_closure_sdiff_of_mem`

English:
lemma Indep.notMem_closure_sdiff_of_mem
  given: (hI : M.Indep I) (he : e in I)
  statement: e ∉ M.closure (I \ {e})
  proof: (indep_iff_forall_notMem_closure_sdiff'.1 hI).2 e he

@[deprecated (since := "2026-06-03")]
alias Indep.notMem_closure_diff_of_mem := Indep.notMem_closure_sdiff_of_mem

中文:
引理 Indep.notMem_closure_sdiff_of_mem
  条件: (hI : M.Indep I) (he : e in I)
  结论: e ∉ M.closure (I \ {e})
  证明: (indep_iff_forall_notMem_closure_sdiff'.1 hI).2 e he

@[deprecated (since := "2026-06-03")]
alias Indep.notMem_closure_diff_of_mem := Indep.notMem_closure_sdiff_of_mem

Depends on / 依赖: indep_iff_forall_notMem_closure_sdiff
-/
lemma Indep.notMem_closure_sdiff_of_mem (hI : M.Indep I) (he : e in I) : e ∉ M.closure (I \ {e}) :=
  (indep_iff_forall_notMem_closure_sdiff'.1 hI).2 e he

@[deprecated (since := "2026-06-03")]
alias Indep.notMem_closure_diff_of_mem := Indep.notMem_closure_sdiff_of_mem

/--
lemma `Indep.closure_insert_sdiff_eq_of_mem_closure` / 引理 `Indep.closure_insert_sdiff_eq_of_mem_closure`

English:
lemma Indep.closure_insert_sdiff_eq_of_mem_closure
  statement: (hI : M.Indep I) (hf : f in M.closure I)
  proof: by
  apply subset_antisymm <;> apply closure_subset_closure_of_subset_closure
  · simp only [subset_def, mem_sdiff, mem_insert_iff, mem_singleton_iff]
    rintro a (rfl | haI)
    exacts [hf, M.subset_closure _ hI.subset_ground haI]
  · intro a haI
    obtain rfl | ne := eq_or_ne a e
    exacts [he,

中文:
引理 Indep.closure_insert_sdiff_eq_of_mem_closure
  结论: (hI : M.Indep I) (hf : f in M.closure I)
  证明: by
  apply subset_antisymm <;> apply closure_subset_closure_of_subset_closure
  · simp only [subset_def, mem_sdiff, mem_insert_iff, mem_singleton_iff]
    rintro a (rfl | haI)
    exacts [hf, M.subset_closure _ hI.subset_ground haI]
  · intro a haI
    obtain rfl | ne := eq_or_ne a e
    exacts [he,

Depends on / 依赖: M.mem_closure_of_mem, M.subset_closure, closure_subset_closure_of_subset_closure, eq_or_ne, exacts, hI.subset_ground, mem_closure_of_mem, mem_insert_iff, mem_sdiff, mem_singleton_iff, subset_antisymm, subset_closure, subset_def, subset_ground
-/
lemma Indep.closure_insert_sdiff_eq_of_mem_closure (hI : M.Indep I) (hf : f in M.closure I)
    (he : e in M.closure (insert f I \ {e})) : M.closure (insert f I \ {e}) = M.closure I := by
  apply subset_antisymm <;> apply closure_subset_closure_of_subset_closure
  · simp only [subset_def, mem_sdiff, mem_insert_iff, mem_singleton_iff]
    rintro a (rfl | haI)
    exacts [hf, M.subset_closure _ hI.subset_ground haI]
  · intro a haI
    obtain rfl | ne := eq_or_ne a e
    exacts [he, M.mem_closure_of_mem' ⟨.inr haI, ne⟩ (hI.subset_ground haI)]

@[deprecated (since := "2026-06-03")]
alias Indep.closure_insert_diff_eq_of_mem_closure := Indep.closure_insert_sdiff_eq_of_mem_closure

/--
lemma `Indep.indep_insert_sdiff_of_mem_closure` / 引理 `Indep.indep_insert_sdiff_of_mem_closure`

English:
lemma Indep.indep_insert_sdiff_of_mem_closure
  statement: (hI : M.Indep I) (hfI : f in M.closure I)
  proof: by
  simp only [mem_insert_iff] at heI
  obtain rfl | heI := heI
  · exact hI.subset (by simp)
  rw [Indep.insert_sdiff_indep_iff (hI.subset (sdiff_subset ..)) heI]
  refine .inl ⟨mem_ground_of_mem_closure hfI, fun h => hI.notMem_closure_sdiff_of_mem heI ?_⟩
  exact closure_insert_eq_of_mem_closure 

中文:
引理 Indep.indep_insert_sdiff_of_mem_closure
  结论: (hI : M.Indep I) (hfI : f in M.closure I)
  证明: by
  simp only [mem_insert_iff] at heI
  obtain rfl | heI := heI
  · exact hI.subset (by simp)
  rw [Indep.insert_sdiff_indep_iff (hI.subset (sdiff_subset ..)) heI]
  refine .inl ⟨mem_ground_of_mem_closure hfI, fun h => hI.notMem_closure_sdiff_of_mem heI ?_⟩
  exact closure_insert_eq_of_mem_closure 

Depends on / 依赖: Indep.insert_sdiff_indep_iff, M.closure_subset_closure, closure_insert_eq_of_mem_closure, closure_subset_closure, hI.notMem_closure_sdiff_of_mem, hI.subset, insert_sdiff_indep_iff, mem_ground_of_mem_closure, mem_insert_iff, notMem_closure_sdiff_of_mem, sdiff_subset, subset
-/
lemma Indep.indep_insert_sdiff_of_mem_closure (hI : M.Indep I) (hfI : f in M.closure I)
    (he : e in M.closure (insert f I \ {e})) (heI : e in insert f I) :
    M.Indep (insert f I \ {e}) := by
  simp only [mem_insert_iff] at heI
  obtain rfl | heI := heI
  · exact hI.subset (by simp)
  rw [Indep.insert_sdiff_indep_iff (hI.subset (sdiff_subset ..)) heI]
  refine .inl ⟨mem_ground_of_mem_closure hfI, fun h => hI.notMem_closure_sdiff_of_mem heI ?_⟩
  exact closure_insert_eq_of_mem_closure h ▸ M.closure_subset_closure (by intro; simp_all) he

@[deprecated (since := "2026-06-03")]
alias Indep.indep_insert_diff_of_mem_closure := Indep.indep_insert_sdiff_of_mem_closure

/--
lemma `IsBasis.isBasis_insert_sdiff_of_mem_closure` / 引理 `IsBasis.isBasis_insert_sdiff_of_mem_closure`

English:
lemma IsBasis.isBasis_insert_sdiff_of_mem_closure
  statement: (hB : M.IsBasis B X)
  proof: by
  rw [isBasis_iff_indep_closure] at hB ⊢
  exact ⟨hB.1.indep_insert_sdiff_of_mem_closure (hB.2.1 hfX) he heB, hB.2.1.trans_eq
    (hB.1.closure_insert_sdiff_eq_of_mem_closure (hB.2.1 hfX) he).symm, sdiff_subset.trans
    (insert_subset hfX hB.2.2)⟩

@[deprecated (since := "2026-06-03")]
alias IsB

中文:
引理 是基.isBasis_insert_sdiff_of_mem_closure
  结论: (hB : M.是基 B X)
  证明: by
  rw [isBasis_iff_indep_closure] at hB ⊢
  exact ⟨hB.1.indep_insert_sdiff_of_mem_closure (hB.2.1 hfX) he heB, hB.2.1.trans_eq
    (hB.1.closure_insert_sdiff_eq_of_mem_closure (hB.2.1 hfX) he).symm, sdiff_subset.trans
    (insert_subset hfX hB.2.2)⟩

@[deprecated (since := "2026-06-03")]
alias IsB

Depends on / 依赖: closure_insert_sdiff_eq_of_mem_closure, indep_insert_sdiff_of_mem_closure, insert_subset, isBasis_iff_indep_closure, sdiff_subset, sdiff_subset.trans, trans_eq
-/
lemma IsBasis.isBasis_insert_sdiff_of_mem_closure (hB : M.IsBasis B X)
    (he : e in M.closure (insert f B \ {e})) (heB : e in insert f B) (hfX : f in X) :
    M.IsBasis (insert f B \ {e}) X := by
  rw [isBasis_iff_indep_closure] at hB ⊢
  exact ⟨hB.1.indep_insert_sdiff_of_mem_closure (hB.2.1 hfX) he heB, hB.2.1.trans_eq
    (hB.1.closure_insert_sdiff_eq_of_mem_closure (hB.2.1 hfX) he).symm, sdiff_subset.trans
    (insert_subset hfX hB.2.2)⟩

@[deprecated (since := "2026-06-03")]
alias IsBasis.isBasis_insert_diff_of_mem_closure := IsBasis.isBasis_insert_sdiff_of_mem_closure

/--
lemma `IsBase.isBase_insert_sdiff_of_mem_closure` / 引理 `IsBase.isBase_insert_sdiff_of_mem_closure`

English:
lemma IsBase.isBase_insert_sdiff_of_mem_closure
  statement: (hB : M.IsBase B)
  proof: by
  rw [← isBasis_ground_iff] at hB ⊢
  by_cases hf : f in M.E
  · exact hB.isBasis_insert_sdiff_of_mem_closure he heB hf
  obtain rfl | heB := heB
  · simpa [show e ∉ B from fun h => hf (hB.1.1.2 h)] using hB
  rw [← closure_inter_ground] at he
  cases hB.indep.notMem_closure_sdiff_of_mem heB (M.c

中文:
引理 IsBase.isBase_insert_sdiff_of_mem_closure
  结论: (hB : M.IsBase B)
  证明: by
  rw [← isBasis_ground_iff] at hB ⊢
  by_cases hf : f in M.E
  · exact hB.isBasis_insert_sdiff_of_mem_closure he heB hf
  obtain rfl | heB := heB
  · simpa [show e ∉ B from fun h => hf (hB.1.1.2 h)] using hB
  rw [← closure_inter_ground] at he
  cases hB.indep.notMem_closure_sdiff_of_mem heB (M.c

Depends on / 依赖: M.closure_subset_closure, closure_inter_ground, closure_subset_closure, hB.indep.notMem_closure_sdiff_of_mem, hB.isBasis_insert_sdiff_of_mem_closure, isBasis_ground_iff, isBasis_insert_sdiff_of_mem_closure, notMem_closure_sdiff_of_mem
-/
lemma IsBase.isBase_insert_sdiff_of_mem_closure (hB : M.IsBase B)
    (he : e in M.closure (insert f B \ {e})) (heB : e in insert f B) :
    M.IsBase (insert f B \ {e}) := by
  rw [← isBasis_ground_iff] at hB ⊢
  by_cases hf : f in M.E
  · exact hB.isBasis_insert_sdiff_of_mem_closure he heB hf
  obtain rfl | heB := heB
  · simpa [show e ∉ B from fun h => hf (hB.1.1.2 h)] using hB
  rw [← closure_inter_ground] at he
  cases hB.indep.notMem_closure_sdiff_of_mem heB (M.closure_subset_closure (by intro; aesop) he)

@[deprecated (since := "2026-06-03")]
alias IsBase.isBase_insert_diff_of_mem_closure := IsBase.isBase_insert_sdiff_of_mem_closure

/--
lemma `indep_iff_forall_closure_sdiff_ne` / 引理 `indep_iff_forall_closure_sdiff_ne`

English:
lemma indep_iff_forall_closure_sdiff_ne
  proof: by
  rw [indep_iff_forall_notMem_closure_sdiff']
  refine ⟨fun ⟨hIE, h⟩ e heI h_eq => h e heI (h_eq.symm.subset (M.mem_closure_of_mem heI)),
    fun h => ⟨fun e heI => by_contra fun heE => h heI ?_,fun e heI hin => h heI ?_⟩⟩
  · rw [← closure_inter_ground, inter_comm, inter_sdiff_distrib_left,
    

中文:
引理 indep_iff_对任意_closure_sdiff_ne
  证明: by
  rw [indep_iff_forall_notMem_closure_sdiff']
  refine ⟨fun ⟨hIE, h⟩ e heI h_eq => h e heI (h_eq.symm.subset (M.mem_closure_of_mem heI)),
    fun h => ⟨fun e heI => by_contra fun heE => h heI ?_,fun e heI hin => h heI ?_⟩⟩
  · rw [← closure_inter_ground, inter_comm, inter_sdiff_distrib_left,
    

Depends on / 依赖: M.mem_closure_of_mem, closure_insert_closure_eq_closure_insert, closure_inter_ground, h_eq, h_eq.symm.subset, indep_iff_forall_notMem_closure_sdiff, insert, insert_eq_of_mem, inter_comm, inter_sdiff_distrib_left, inter_singleton_eq_empty, inter_singleton_eq_empty.mpr, mem_closure_of_mem, nth_rw, sdiff_empty, subset
-/
lemma indep_iff_forall_closure_sdiff_ne :
    M.Indep I ↔ forall ⦃e⦄, e in I -> M.closure (I \ {e}) != M.closure I := by
  rw [indep_iff_forall_notMem_closure_sdiff']
  refine ⟨fun ⟨hIE, h⟩ e heI h_eq => h e heI (h_eq.symm.subset (M.mem_closure_of_mem heI)),
    fun h => ⟨fun e heI => by_contra fun heE => h heI ?_,fun e heI hin => h heI ?_⟩⟩
  · rw [← closure_inter_ground, inter_comm, inter_sdiff_distrib_left,
      inter_singleton_eq_empty.mpr heE, sdiff_empty, inter_comm, closure_inter_ground]
  nth_rw 2 [show I = insert e (I \ {e}) by simp [heI]]
  rw [← closure_insert_closure_eq_closure_insert]; rw [insert_eq_of_mem hin]; rw [closure_closure]

@[deprecated (since := "2026-06-03")]
alias indep_iff_forall_closure_diff_ne := indep_iff_forall_closure_sdiff_ne

/--
lemma `Indep.union_indep_iff_forall_notMem_closure_right` / 引理 `Indep.union_indep_iff_forall_notMem_closure_right`

English:
lemma Indep.union_indep_iff_forall_notMem_closure_right
  given: (hI : M.Indep I) (hJ : M.Indep J)
  proof: by
  refine ⟨fun h e heJ hecl => h.notMem_closure_sdiff_of_mem (.inr heJ.1) ?_, fun h => ?_⟩
  · rwa [union_sdiff_distrib, sdiff_singleton_eq_self heJ.2]
  obtain ⟨K, hKIJ, hK⟩ := hI.subset_isBasis_of_subset (show I subseteq I union J from subset_union_left)
  obtain rfl | hssu := hKIJ.subset.eq_or_

中文:
引理 Indep.union_indep_iff_对任意_notMem_closure_right
  条件: (hI : M.Indep I) (hJ : M.Indep J)
  证明: by
  refine ⟨fun h e heJ hecl => h.notMem_closure_sdiff_of_mem (.inr heJ.1) ?_, fun h => ?_⟩
  · rwa [union_sdiff_distrib, sdiff_singleton_eq_self heJ.2]
  obtain ⟨K, hKIJ, hK⟩ := hI.subset_isBasis_of_subset (show I subseteq I union J from subset_union_left)
  obtain rfl | hssu := hKIJ.subset.eq_or_

Depends on / 依赖: eq_or_ssubset, exists_of_ssubset, h.notMem_closure_sdiff_of_mem, hI.subset_isBasis_of_subset, hKIJ.indep, hKIJ.subset.eq_or_ssubset, notMem_closure_sdiff_of_mem, notMem_subset, sdiff_singleton_eq_self, subset, subset_isBasis_of_subset, subset_union_left, subseteq, union_comm, union_sdiff_distrib, union_sdiff_right
-/
lemma Indep.union_indep_iff_forall_notMem_closure_right (hI : M.Indep I) (hJ : M.Indep J) :
    M.Indep (I union J) ↔ forall e in J \ I, e ∉ M.closure (I union (J \ {e})) := by
  refine ⟨fun h e heJ hecl => h.notMem_closure_sdiff_of_mem (.inr heJ.1) ?_, fun h => ?_⟩
  · rwa [union_sdiff_distrib, sdiff_singleton_eq_self heJ.2]
  obtain ⟨K, hKIJ, hK⟩ := hI.subset_isBasis_of_subset (show I subseteq I union J from subset_union_left)
  obtain rfl | hssu := hKIJ.subset.eq_or_ssubset
  · exact hKIJ.indep
  exfalso
  obtain ⟨e, heI, heK⟩ := exists_of_ssubset hssu
  have heJI : e in J \ I := by
    rw [← union_sdiff_right]; rw [union_comm]
    exact ⟨heI, notMem_subset hK heK⟩
  refine h _ heJI ?_
  rw [← sdiff_singleton_eq_self heJI.2]; rw [← union_sdiff_distrib]
exact M.closure_subset_closure (subset_sdiff_singleton hKIJ.subset heK) hKIJ.subset_closure heI

/--
lemma `Indep.union_indep_iff_forall_notMem_closure_left` / 引理 `Indep.union_indep_iff_forall_notMem_closure_left`

English:
lemma Indep.union_indep_iff_forall_notMem_closure_left
  given: (hI : M.Indep I) (hJ : M.Indep J)
  proof: by
  simp_rw [union_comm I J, hJ.union_indep_iff_forall_notMem_closure_right hI, union_comm]

中文:
引理 Indep.union_indep_iff_对任意_notMem_closure_left
  条件: (hI : M.Indep I) (hJ : M.Indep J)
  证明: by
  simp_rw [union_comm I J, hJ.union_indep_iff_forall_notMem_closure_right hI, union_comm]

Depends on / 依赖: hJ.union_indep_iff_forall_notMem_closure_right, simp_rw, union_comm, union_indep_iff_forall_notMem_closure_right
-/
lemma Indep.union_indep_iff_forall_notMem_closure_left (hI : M.Indep I) (hJ : M.Indep J) :
    M.Indep (I union J) ↔ forall e in I \ J, e ∉ M.closure ((I \ {e}) union J) := by
  simp_rw [union_comm I J, hJ.union_indep_iff_forall_notMem_closure_right hI, union_comm]

/--
lemma `Indep.closure_ssubset_closure` / 引理 `Indep.closure_ssubset_closure`

English:
lemma Indep.closure_ssubset_closure
  given: (hI : M.Indep I) (hJI : J ⊂ I)
  statement: M.closure J ⊂ M.closure I
  proof: by
  obtain ⟨e, heI, heJ⟩ := exists_of_ssubset hJI
exact (M.closure_subset_closure hJI.subset).ssubset_of_not_subset fun hss => heJ
    (hI.closure_inter_eq_self_of_subset hJI.subset).subset ⟨hss (M.mem_closure_of_mem heI), heI⟩

中文:
引理 Indep.closure_ssubset_closure
  条件: (hI : M.Indep I) (hJI : J ⊂ I)
  结论: M.closure J ⊂ M.closure I
  证明: by
  obtain ⟨e, heI, heJ⟩ := exists_of_ssubset hJI
exact (M.closure_subset_closure hJI.subset).ssubset_of_not_subset fun hss => heJ
    (hI.closure_inter_eq_self_of_subset hJI.subset).subset ⟨hss (M.mem_closure_of_mem heI), heI⟩

Depends on / 依赖: M.closure_subset_closure, M.mem_closure_of_mem, closure_inter_eq_self_of_subset, closure_subset_closure, exists_of_ssubset, hI.closure_inter_eq_self_of_subset, hJI.subset, mem_closure_of_mem, ssubset_of_not_subset, subset
-/
lemma Indep.closure_ssubset_closure (hI : M.Indep I) (hJI : J ⊂ I) : M.closure J ⊂ M.closure I := by
  obtain ⟨e, heI, heJ⟩ := exists_of_ssubset hJI
exact (M.closure_subset_closure hJI.subset).ssubset_of_not_subset fun hss => heJ
    (hI.closure_inter_eq_self_of_subset hJI.subset).subset ⟨hss (M.mem_closure_of_mem heI), heI⟩

/--
lemma `indep_iff_forall_closure_ssubset_of_ssubset` / 引理 `indep_iff_forall_closure_ssubset_of_ssubset`

English:
lemma indep_iff_forall_closure_ssubset_of_ssubset
  given: (hI : I subseteq M.E := by aesop_mat)
  proof: by
  refine ⟨fun h _ => h.closure_ssubset_closure,
    fun h => (indep_iff_forall_notMem_closure_sdiff hI).2 fun e heI hecl => ?_⟩
  refine (h (sdiff_singleton_ssubset.2 heI)).ne ?_
  rw [show I = insert e (I \ {e}) by simp [heI], ← closure_insert_closure_eq_closure_insert,
    insert_eq_of_mem hecl

中文:
引理 indep_iff_对任意_closure_ssubset_of_ssubset
  条件: (hI : I subseteq M.E := by aesop_mat)
  证明: by
  refine ⟨fun h _ => h.closure_ssubset_closure,
    fun h => (indep_iff_forall_notMem_closure_sdiff hI).2 fun e heI hecl => ?_⟩
  refine (h (sdiff_singleton_ssubset.2 heI)).ne ?_
  rw [show I = insert e (I \ {e}) by simp [heI], ← closure_insert_closure_eq_closure_insert,
    insert_eq_of_mem hecl

Depends on / 依赖: M.Indep, M.closure, aesop_mat, closure, closure_insert_closure_eq_closure_insert, closure_ssubset_closure, h.closure_ssubset_closure, indep_iff_forall_notMem_closure_sdiff, insert, insert_eq_of_mem, sdiff_singleton_ssubset
-/
lemma indep_iff_forall_closure_ssubset_of_ssubset (hI : I subseteq M.E := by aesop_mat) :
    M.Indep I ↔ forall ⦃J⦄, J ⊂ I -> M.closure J ⊂ M.closure I := by
  refine ⟨fun h _ => h.closure_ssubset_closure,
    fun h => (indep_iff_forall_notMem_closure_sdiff hI).2 fun e heI hecl => ?_⟩
  refine (h (sdiff_singleton_ssubset.2 heI)).ne ?_
  rw [show I = insert e (I \ {e}) by simp [heI], ← closure_insert_closure_eq_closure_insert,
    insert_eq_of_mem hecl]
  simp

/--
lemma `Indep.closure_sdiff_ssubset` / 引理 `Indep.closure_sdiff_ssubset`

English:
lemma Indep.closure_sdiff_ssubset
  given: (hI : M.Indep I) (hX : (I inter X).Nonempty)
  proof: by
refine hI.closure_ssubset_closure sdiff_subset.ssubset_of_ne fun h => ?_
  rw [sdiff_eq_left]; rw [disjoint_iff_inter_eq_empty] at h
  simp [h] at hX

@[deprecated (since := "2026-06-03")]
alias Indep.closure_diff_ssubset := Indep.closure_sdiff_ssubset

中文:
引理 Indep.closure_sdiff_ssubset
  条件: (hI : M.Indep I) (hX : (I inter X).非空)
  证明: by
refine hI.closure_ssubset_closure sdiff_subset.ssubset_of_ne fun h => ?_
  rw [sdiff_eq_left]; rw [disjoint_iff_inter_eq_empty] at h
  simp [h] at hX

@[deprecated (since := "2026-06-03")]
alias Indep.closure_diff_ssubset := Indep.closure_sdiff_ssubset

Depends on / 依赖: closure_ssubset_closure, disjoint_iff_inter_eq_empty, hI.closure_ssubset_closure, sdiff_eq_left, sdiff_subset, sdiff_subset.ssubset_of_ne, ssubset_of_ne
-/
lemma Indep.closure_sdiff_ssubset (hI : M.Indep I) (hX : (I inter X).Nonempty) :
    M.closure (I \ X) ⊂ M.closure I := by
refine hI.closure_ssubset_closure sdiff_subset.ssubset_of_ne fun h => ?_
  rw [sdiff_eq_left]; rw [disjoint_iff_inter_eq_empty] at h
  simp [h] at hX

@[deprecated (since := "2026-06-03")]
alias Indep.closure_diff_ssubset := Indep.closure_sdiff_ssubset

/--
lemma `Indep.closure_sdiff_singleton_ssubset` / 引理 `Indep.closure_sdiff_singleton_ssubset`

English:
lemma Indep.closure_sdiff_singleton_ssubset
  given: (hI : M.Indep I) (he : e in I)
  proof: hI.closure_ssubset_closure by simpa

@[deprecated (since := "2026-06-03")]
alias Indep.closure_diff_singleton_ssubset := Indep.closure_sdiff_singleton_ssubset

中文:
引理 Indep.closure_sdiff_singleton_ssubset
  条件: (hI : M.Indep I) (he : e in I)
  证明: hI.closure_ssubset_closure by simpa

@[deprecated (since := "2026-06-03")]
alias Indep.closure_diff_singleton_ssubset := Indep.closure_sdiff_singleton_ssubset

Depends on / 依赖: closure_ssubset_closure, hI.closure_ssubset_closure
-/
lemma Indep.closure_sdiff_singleton_ssubset (hI : M.Indep I) (he : e in I) :
    M.closure (I \ {e}) ⊂ M.closure I :=
hI.closure_ssubset_closure by simpa

@[deprecated (since := "2026-06-03")]
alias Indep.closure_diff_singleton_ssubset := Indep.closure_sdiff_singleton_ssubset

end Indep

section insert

/--
lemma `mem_closure_insert` / 引理 `mem_closure_insert`

English:
lemma mem_closure_insert
  given: (he : e ∉ M.closure X) (hef : e in M.closure (insert f X))
  proof: by
  rw [← closure_inter_ground] at *
  have hfE : f in M.E := by
    by_contra! hfE; rw [insert_inter_of_notMem hfE] at hef; exact he hef
  have heE : e in M.E := (M.closure_subset_ground _) hef
  rw [insert_inter_of_mem hfE] at hef; rw [insert_inter_of_mem heE]
  obtain ⟨I, hI⟩ := M.exists_isBasis

中文:
引理 mem_closure_insert
  条件: (he : e ∉ M.closure X) (hef : e in M.closure (insert f X))
  证明: by
  rw [← closure_inter_ground] at *
  have hfE : f in M.E := by
    by_contra! hfE; rw [insert_inter_of_notMem hfE] at hef; exact he hef
  have heE : e in M.E := (M.closure_subset_ground _) hef
  rw [insert_inter_of_mem hfE] at hef; rw [insert_inter_of_mem heE]
  obtain ⟨I, hI⟩ := M.exists_isBasis

Depends on / 依赖: M.closure_subset_ground, M.exists_isBasis, closure_eq_closure, closure_insert_closure_eq_closure_insert, closure_inter_ground, closure_subset_ground, exists_isBasis, hI.closure_eq_closure, hI.indep.notMem_closure_iff, insert_inter_of_mem, insert_inter_of_notMem, notMem_closure_iff
-/
lemma mem_closure_insert (he : e ∉ M.closure X) (hef : e in M.closure (insert f X)) :
    f in M.closure (insert e X) := by
  rw [← closure_inter_ground] at *
  have hfE : f in M.E := by
    by_contra! hfE; rw [insert_inter_of_notMem hfE] at hef; exact he hef
  have heE : e in M.E := (M.closure_subset_ground _) hef
  rw [insert_inter_of_mem hfE] at hef; rw [insert_inter_of_mem heE]
  obtain ⟨I, hI⟩ := M.exists_isBasis (X inter M.E)
  rw [← hI.closure_eq_closure]; rw [hI.indep.notMem_closure_iff] at he
  rw [← closure_insert_closure_eq_closure_insert]; rw [← hI.closure_eq_closure]; rw [closure_insert_closure_eq_closure_insert]; rw [he.1.mem_closure_iff] at *
  rw [or_iff_not_imp_left]; rw [dep_iff]; rw [insert_comm]; rw [and_iff_left (insert_subset heE (insert_subset hfE hI.indep.subset_ground))]; rw [not_not]
  intro h
  rw [(h.subset (subset_insert _ _)).mem_closure_iff]; rw [or_iff_right (h.not_dep)]; rw [mem_insert_iff]; rw [or_iff_left he.2] at hef
  subst hef; apply mem_insert

/--
lemma `closure_exchange` / 引理 `closure_exchange`

English:
lemma closure_exchange
  given: (he : e in M.closure (insert f X) \ M.closure X)
  proof: ⟨mem_closure_insert he.2 he.1, fun hf => by
    rwa [closure_insert_eq_of_mem_closure hf, sdiff_self, iff_false_intro (notMem_empty _)] at he⟩

中文:
引理 closure_exchange
  条件: (he : e in M.closure (insert f X) \ M.closure X)
  证明: ⟨mem_closure_insert he.2 he.1, fun hf => by
    rwa [closure_insert_eq_of_mem_closure hf, sdiff_self, iff_false_intro (notMem_empty _)] at he⟩

Depends on / 依赖: closure_insert_eq_of_mem_closure, iff_false_intro, mem_closure_insert, notMem_empty, sdiff_self
-/
lemma closure_exchange (he : e in M.closure (insert f X) \ M.closure X) :
    f in M.closure (insert e X) \ M.closure X :=
  ⟨mem_closure_insert he.2 he.1, fun hf => by
    rwa [closure_insert_eq_of_mem_closure hf, sdiff_self, iff_false_intro (notMem_empty _)] at he⟩

/--
lemma `closure_exchange_iff` / 引理 `closure_exchange_iff`

English:
lemma closure_exchange_iff
  proof: ⟨closure_exchange, closure_exchange⟩

中文:
引理 closure_exchange_iff
  证明: ⟨closure_exchange, closure_exchange⟩

Depends on / 依赖: closure_exchange
-/
lemma closure_exchange_iff :
    e in M.closure (insert f X) \ M.closure X ↔ f in M.closure (insert e X) \ M.closure X :=
  ⟨closure_exchange, closure_exchange⟩

/--
lemma `closure_insert_congr` / 引理 `closure_insert_congr`

English:
lemma closure_insert_congr
  given: (he : e in M.closure (insert f X) \ M.closure X)
  proof: by
  have hf := closure_exchange he
  rw [eq_comm]; rw [← closure_closure]; rw [← insert_eq_of_mem he.1]; rw [closure_insert_closure_eq_closure_insert]; rw [insert_comm]; rw [← closure_closure]; rw [← closure_insert_closure_eq_closure_insert]; rw [insert_eq_of_mem hf.1]; rw [closure_closure]; rw [cl

中文:
引理 closure_insert_congr
  条件: (he : e in M.closure (insert f X) \ M.closure X)
  证明: by
  have hf := closure_exchange he
  rw [eq_comm]; rw [← closure_closure]; rw [← insert_eq_of_mem he.1]; rw [closure_insert_closure_eq_closure_insert]; rw [insert_comm]; rw [← closure_closure]; rw [← closure_insert_closure_eq_closure_insert]; rw [insert_eq_of_mem hf.1]; rw [closure_closure]; rw [cl

Depends on / 依赖: closure_closure, closure_exchange, closure_insert_closure_eq_closure_insert, eq_comm, insert_comm, insert_eq_of_mem
-/
lemma closure_insert_congr (he : e in M.closure (insert f X) \ M.closure X) :
    M.closure (insert e X) = M.closure (insert f X) := by
  have hf := closure_exchange he
  rw [eq_comm]; rw [← closure_closure]; rw [← insert_eq_of_mem he.1]; rw [closure_insert_closure_eq_closure_insert]; rw [insert_comm]; rw [← closure_closure]; rw [← closure_insert_closure_eq_closure_insert]; rw [insert_eq_of_mem hf.1]; rw [closure_closure]; rw [closure_closure]

/--
lemma `closure_sdiff_eq_self` / 引理 `closure_sdiff_eq_self`

English:
lemma closure_sdiff_eq_self
  given: (h : Y subseteq M.closure (X \ Y))
  statement: M.closure (X \ Y) = M.closure X
  proof: by
  rw [← sdiff_union_inter X Y]; rw [← closure_union_closure_left_eq]; rw [union_eq_self_of_subset_right (inter_subset_right.trans h)]; rw [closure_closure]; rw [sdiff_union_inter]

@[deprecated (since := "2026-06-03")] alias closure_diff_eq_self := closure_sdiff_eq_self

中文:
引理 closure_sdiff_eq_self
  条件: (h : Y subseteq M.closure (X \ Y))
  结论: M.closure (X \ Y) = M.closure X
  证明: by
  rw [← sdiff_union_inter X Y]; rw [← closure_union_closure_left_eq]; rw [union_eq_self_of_subset_right (inter_subset_right.trans h)]; rw [closure_closure]; rw [sdiff_union_inter]

@[deprecated (since := "2026-06-03")] alias closure_diff_eq_self := closure_sdiff_eq_self

Depends on / 依赖: closure_closure, closure_union_closure_left_eq, inter_subset_right, inter_subset_right.trans, sdiff_union_inter, union_eq_self_of_subset_right
-/
lemma closure_sdiff_eq_self (h : Y subseteq M.closure (X \ Y)) : M.closure (X \ Y) = M.closure X := by
  rw [← sdiff_union_inter X Y]; rw [← closure_union_closure_left_eq]; rw [union_eq_self_of_subset_right (inter_subset_right.trans h)]; rw [closure_closure]; rw [sdiff_union_inter]

@[deprecated (since := "2026-06-03")] alias closure_diff_eq_self := closure_sdiff_eq_self

/--
lemma `closure_sdiff_singleton_eq_closure` / 引理 `closure_sdiff_singleton_eq_closure`

English:
lemma closure_sdiff_singleton_eq_closure
  given: (h : e in M.closure (X \ {e}))
  proof: closure_sdiff_eq_self (by simpa)

@[deprecated (since := "2026-06-03")]
alias closure_diff_singleton_eq_closure := closure_sdiff_singleton_eq_closure

中文:
引理 closure_sdiff_singleton_eq_closure
  条件: (h : e in M.closure (X \ {e}))
  证明: closure_sdiff_eq_self (by simpa)

@[deprecated (since := "2026-06-03")]
alias closure_diff_singleton_eq_closure := closure_sdiff_singleton_eq_closure

Depends on / 依赖: closure_sdiff_eq_self
-/
lemma closure_sdiff_singleton_eq_closure (h : e in M.closure (X \ {e})) :
    M.closure (X \ {e}) = M.closure X :=
  closure_sdiff_eq_self (by simpa)

@[deprecated (since := "2026-06-03")]
alias closure_diff_singleton_eq_closure := closure_sdiff_singleton_eq_closure

/--
lemma `subset_closure_sdiff_iff_closure_eq` / 引理 `subset_closure_sdiff_iff_closure_eq`

English:
lemma subset_closure_sdiff_iff_closure_eq
  given: (h : Y subseteq X) (hY : Y subseteq M.E := by aesop_mat)
  proof: ⟨closure_sdiff_eq_self, fun h' => (M.subset_closure_of_subset' h).trans h'.symm.subset⟩

@[deprecated (since := "2026-06-03")]
alias subset_closure_diff_iff_closure_eq := subset_closure_sdiff_iff_closure_eq

中文:
引理 subset_closure_sdiff_iff_closure_eq
  条件: (h : Y subseteq X) (hY : Y subseteq M.E := by aesop_mat)
  证明: ⟨closure_sdiff_eq_self, fun h' => (M.subset_closure_of_subset' h).trans h'.symm.subset⟩

@[deprecated (since := "2026-06-03")]
alias subset_closure_diff_iff_closure_eq := subset_closure_sdiff_iff_closure_eq

Depends on / 依赖: M.closure, M.subset_closure_of_subset, aesop_mat, closure, closure_sdiff_eq_self, subset, subset_closure_of_subset, subseteq, symm.subset
-/
lemma subset_closure_sdiff_iff_closure_eq (h : Y subseteq X) (hY : Y subseteq M.E := by aesop_mat) :
    Y subseteq M.closure (X \ Y) ↔ M.closure (X \ Y) = M.closure X :=
  ⟨closure_sdiff_eq_self, fun h' => (M.subset_closure_of_subset' h).trans h'.symm.subset⟩

@[deprecated (since := "2026-06-03")]
alias subset_closure_diff_iff_closure_eq := subset_closure_sdiff_iff_closure_eq

/--
lemma `mem_closure_sdiff_singleton_iff_closure` / 引理 `mem_closure_sdiff_singleton_iff_closure`

English:
lemma mem_closure_sdiff_singleton_iff_closure
  given: (he : e in X) (heE : e in M.E := by aesop_mat)
  proof: by
  simpa using subset_closure_sdiff_iff_closure_eq (Y := {e}) (X := X) (by simpa)

@[deprecated (since := "2026-06-03")]
alias mem_closure_diff_singleton_iff_closure := mem_closure_sdiff_singleton_iff_closure

中文:
引理 mem_closure_sdiff_singleton_iff_closure
  条件: (he : e in X) (heE : e in M.E := by aesop_mat)
  证明: by
  simpa using subset_closure_sdiff_iff_closure_eq (Y := {e}) (X := X) (by simpa)

@[deprecated (since := "2026-06-03")]
alias mem_closure_diff_singleton_iff_closure := mem_closure_sdiff_singleton_iff_closure

Depends on / 依赖: M.closure, aesop_mat, closure, subset_closure_sdiff_iff_closure_eq
-/
lemma mem_closure_sdiff_singleton_iff_closure (he : e in X) (heE : e in M.E := by aesop_mat) :
    e in M.closure (X \ {e}) ↔ M.closure (X \ {e}) = M.closure X := by
  simpa using subset_closure_sdiff_iff_closure_eq (Y := {e}) (X := X) (by simpa)

@[deprecated (since := "2026-06-03")]
alias mem_closure_diff_singleton_iff_closure := mem_closure_sdiff_singleton_iff_closure

end insert

/--
lemma `ext_closure` / 引理 `ext_closure`

English:
lemma ext_closure
  given: {M₁ M₂ : Matroid α} (h : forall X, M₁.closure X = M₂.closure X)
  statement: M₁ = M₂
  proof: ext_indep (by simpa using h univ)
    (fun _ _ => by simp_rw [indep_iff_forall_closure_sdiff_ne, h])

中文:
引理 ext_closure
  条件: {M₁ M₂ : 拟阵 α} (h : 对任意 X, M₁.closure X = M₂.closure X)
  结论: M₁ = M₂
  证明: ext_indep (by simpa using h univ)
    (fun _ _ => by simp_rw [indep_iff_forall_closure_sdiff_ne, h])

Depends on / 依赖: ext_indep, indep_iff_forall_closure_sdiff_ne, simp_rw
-/
lemma ext_closure {M₁ M₂ : Matroid α} (h : forall X, M₁.closure X = M₂.closure X) : M₁ = M₂ :=
  ext_indep (by simpa using h univ)
    (fun _ _ => by simp_rw [indep_iff_forall_closure_sdiff_ne, h])


section Spanning

variable {S T I B : Set α}

/-- A set is `spanning` in `M` if its closure is equal to `M.E`, or equivalently if it contains
a base of `M`. -/
@[mk_iff]
/--
Definition of `Spanning` / `Spanning` 的定义

English:
structure Spanning
  parameters: (M : Matroid α) (S : Set α)
  axioms and operations (2):
    - closure_eq : M.closure S = M.E
    - subset_ground : S subseteq M.E

中文:
结构 生成
  参数: (M : 拟阵 α) (S : 集合 α)
  公理与运算 (2 个):
    - closure_eq : M.closure S = M.E
    - subset_ground : S subseteq M.E

Depends on / 依赖: Matroid, Spanning, Spanning.subset_ground, subset_ground
-/
structure Spanning (M : Matroid α) (S : Set α) : Prop where
  closure_eq : M.closure S = M.E
  subset_ground : S subseteq M.E

attribute [aesop unsafe 10% (rule_sets := [Matroid])] Spanning.subset_ground

/--
lemma `spanning_iff_closure_eq` / 引理 `spanning_iff_closure_eq`

English:
lemma spanning_iff_closure_eq
  given: (hS : S subseteq M.E := by aesop_mat)
  proof: by
  rw [spanning_iff]; rw [and_iff_left hS]

中文:
引理 spanning_iff_closure_eq
  条件: (hS : S subseteq M.E := by aesop_mat)
  证明: by
  rw [spanning_iff]; rw [and_iff_left hS]

Depends on / 依赖: M.Spanning, M.closure, Spanning, aesop_mat, and_iff_left, closure, spanning_iff
-/
lemma spanning_iff_closure_eq (hS : S subseteq M.E := by aesop_mat) :
    M.Spanning S ↔ M.closure S = M.E := by
  rw [spanning_iff]; rw [and_iff_left hS]

/--
lemma `closure_spanning_iff` / 引理 `closure_spanning_iff`

English:
lemma closure_spanning_iff
  given: (hS : S subseteq M.E := by aesop_mat)
  proof: by
  rw [spanning_iff_closure_eq]; rw [closure_closure]; rw [← spanning_iff_closure_eq]

中文:
引理 closure_spanning_iff
  条件: (hS : S subseteq M.E := by aesop_mat)
  证明: by
  rw [spanning_iff_closure_eq]; rw [closure_closure]; rw [← spanning_iff_closure_eq]
-/
@[simp] lemma closure_spanning_iff (hS : S subseteq M.E := by aesop_mat) :
    M.Spanning (M.closure S) ↔ M.Spanning S := by
  rw [spanning_iff_closure_eq]; rw [closure_closure]; rw [← spanning_iff_closure_eq]

/--
lemma `spanning_iff_ground_subset_closure` / 引理 `spanning_iff_ground_subset_closure`

English:
lemma spanning_iff_ground_subset_closure
  given: (hS : S subseteq M.E := by aesop_mat)
  proof: by
  rw [spanning_iff_closure_eq]; rw [subset_antisymm_iff]; rw [and_iff_right (closure_subset_ground _ _)]

中文:
引理 spanning_iff_ground_subset_closure
  条件: (hS : S subseteq M.E := by aesop_mat)
  证明: by
  rw [spanning_iff_closure_eq]; rw [subset_antisymm_iff]; rw [and_iff_right (closure_subset_ground _ _)]

Depends on / 依赖: M.Spanning, M.closure, Spanning, aesop_mat, and_iff_right, closure, closure_subset_ground, spanning_iff_closure_eq, subset_antisymm_iff, subseteq
-/
lemma spanning_iff_ground_subset_closure (hS : S subseteq M.E := by aesop_mat) :
    M.Spanning S ↔ M.E subseteq M.closure S := by
  rw [spanning_iff_closure_eq]; rw [subset_antisymm_iff]; rw [and_iff_right (closure_subset_ground _ _)]

/--
lemma `not_spanning_iff_closure_ssubset` / 引理 `not_spanning_iff_closure_ssubset`

English:
lemma not_spanning_iff_closure_ssubset
  given: (hS : S subseteq M.E := by aesop_mat)
  proof: by
  rw [spanning_iff_closure_eq]; rw [ssubset_iff_subset_ne]; rw [iff_and_self]; rw [iff_true_intro (M.closure_subset_ground _)]
  exact fun _ => trivial

中文:
引理 not_spanning_iff_closure_ssubset
  条件: (hS : S subseteq M.E := by aesop_mat)
  证明: by
  rw [spanning_iff_closure_eq]; rw [ssubset_iff_subset_ne]; rw [iff_and_self]; rw [iff_true_intro (M.closure_subset_ground _)]
  exact fun _ => trivial

Depends on / 依赖: M.Spanning, M.closure, M.closure_subset_ground, Spanning, aesop_mat, closure, closure_subset_ground, iff_and_self, iff_true_intro, spanning_iff_closure_eq, ssubset_iff_subset_ne
-/
lemma not_spanning_iff_closure_ssubset (hS : S subseteq M.E := by aesop_mat) :
    ¬M.Spanning S ↔ M.closure S ⊂ M.E := by
  rw [spanning_iff_closure_eq]; rw [ssubset_iff_subset_ne]; rw [iff_and_self]; rw [iff_true_intro (M.closure_subset_ground _)]
  exact fun _ => trivial

/--
lemma `Spanning.superset` / 引理 `Spanning.superset`

English:
lemma Spanning.superset
  given: (hS : M.Spanning S) (hST : S subseteq T) (hT : T subseteq M.E := by aesop_mat)
  proof: ⟨(M.closure_subset_ground _).antisymm
    (by rw [← hS.closure_eq]; exact M.closure_subset_closure hST), hT⟩

中文:
引理 生成.superset
  条件: (hS : M.生成 S) (hST : S subseteq T) (hT : T subseteq M.E := by aesop_mat)
  证明: ⟨(M.closure_subset_ground _).antisymm
    (by rw [← hS.closure_eq]; exact M.closure_subset_closure hST), hT⟩

Depends on / 依赖: M.Spanning, M.closure_subset_closure, M.closure_subset_ground, Spanning, aesop_mat, antisymm, closure_eq, closure_subset_closure, closure_subset_ground, hS.closure_eq
-/
lemma Spanning.superset (hS : M.Spanning S) (hST : S subseteq T) (hT : T subseteq M.E := by aesop_mat) :
    M.Spanning T :=
  ⟨(M.closure_subset_ground _).antisymm
    (by rw [← hS.closure_eq]; exact M.closure_subset_closure hST), hT⟩

/--
lemma `Spanning.closure_eq_of_superset` / 引理 `Spanning.closure_eq_of_superset`

English:
lemma Spanning.closure_eq_of_superset
  given: (hS : M.Spanning S) (hST : S subseteq T)
  statement: M.closure T = M.E
  proof: by
  rw [← closure_inter_ground]; rw [← spanning_iff_closure_eq]
  exact hS.superset (subset_inter hST hS.subset_ground)

中文:
引理 生成.closure_eq_of_superset
  条件: (hS : M.生成 S) (hST : S subseteq T)
  结论: M.closure T = M.E
  证明: by
  rw [← closure_inter_ground]; rw [← spanning_iff_closure_eq]
  exact hS.superset (subset_inter hST hS.subset_ground)

Depends on / 依赖: closure_inter_ground, hS.subset_ground, hS.superset, spanning_iff_closure_eq, subset_ground, subset_inter, superset
-/
lemma Spanning.closure_eq_of_superset (hS : M.Spanning S) (hST : S subseteq T) : M.closure T = M.E := by
  rw [← closure_inter_ground]; rw [← spanning_iff_closure_eq]
  exact hS.superset (subset_inter hST hS.subset_ground)

/--
lemma `Spanning.union_left` / 引理 `Spanning.union_left`

English:
lemma Spanning.union_left
  given: (hS : M.Spanning S) (hX : X subseteq M.E := by aesop_mat)
  statement: M.Spanning (S union X)
  proof: hS.superset subset_union_left

中文:
引理 生成.union_left
  条件: (hS : M.生成 S) (hX : X subseteq M.E := by aesop_mat)
  结论: M.生成 (S union X)
  证明: hS.superset subset_union_left

Depends on / 依赖: M.Spanning, Spanning, aesop_mat, hS.superset, subset_union_left, superset
-/
lemma Spanning.union_left (hS : M.Spanning S) (hX : X subseteq M.E := by aesop_mat) : M.Spanning (S union X) :=
  hS.superset subset_union_left

/--
lemma `Spanning.union_right` / 引理 `Spanning.union_right`

English:
lemma Spanning.union_right
  given: (hS : M.Spanning S) (hX : X subseteq M.E := by aesop_mat)
  proof: hS.superset subset_union_right

中文:
引理 生成.union_right
  条件: (hS : M.生成 S) (hX : X subseteq M.E := by aesop_mat)
  证明: hS.superset subset_union_right

Depends on / 依赖: M.Spanning, Spanning, aesop_mat, hS.superset, subset_union_right, superset
-/
lemma Spanning.union_right (hS : M.Spanning S) (hX : X subseteq M.E := by aesop_mat) :
    M.Spanning (X union S) :=
  hS.superset subset_union_right

/--
lemma `IsBase.spanning` / 引理 `IsBase.spanning`

English:
lemma IsBase.spanning
  given: (hB : M.IsBase B)
  statement: M.Spanning B
  proof: ⟨hB.closure_eq, hB.subset_ground⟩

中文:
引理 IsBase.spanning
  条件: (hB : M.IsBase B)
  结论: M.生成 B
  证明: ⟨hB.closure_eq, hB.subset_ground⟩

Depends on / 依赖: closure_eq, hB.closure_eq, hB.subset_ground, subset_ground
-/
lemma IsBase.spanning (hB : M.IsBase B) : M.Spanning B :=
  ⟨hB.closure_eq, hB.subset_ground⟩

/--
lemma `ground_spanning` / 引理 `ground_spanning`

English:
lemma ground_spanning
  given: (M : Matroid α)
  statement: M.Spanning M.E
  proof: ⟨M.closure_ground, rfl.subset⟩

中文:
引理 ground_spanning
  条件: (M : 拟阵 α)
  结论: M.生成 M.E
  证明: ⟨M.closure_ground, rfl.subset⟩

Depends on / 依赖: M.closure_ground, closure_ground, rfl.subset, subset
-/
lemma ground_spanning (M : Matroid α) : M.Spanning M.E :=
  ⟨M.closure_ground, rfl.subset⟩

/--
lemma `IsBase.spanning_of_superset` / 引理 `IsBase.spanning_of_superset`

English:
lemma IsBase.spanning_of_superset
  given: (hB : M.IsBase B) (hBX : B subseteq X) (hX : X subseteq M.E := by aesop_mat)
  proof: hB.spanning.superset hBX

中文:
引理 IsBase.spanning_of_superset
  条件: (hB : M.IsBase B) (hBX : B subseteq X) (hX : X subseteq M.E := by aesop_mat)
  证明: hB.spanning.superset hBX

Depends on / 依赖: M.Spanning, Spanning, aesop_mat, hB.spanning.superset, spanning, superset
-/
lemma IsBase.spanning_of_superset (hB : M.IsBase B) (hBX : B subseteq X) (hX : X subseteq M.E := by aesop_mat) :
    M.Spanning X :=
  hB.spanning.superset hBX

/--
lemma `spanning_iff_exists_isBase_subset'` / 引理 `spanning_iff_exists_isBase_subset'`

English:
lemma spanning_iff_exists_isBase_subset'
  statement: M.Spanning S ↔ (exists B, M.IsBase B ∧ B subseteq S) ∧ S subseteq M.E
  proof: by
  refine ⟨fun h => ⟨?_, h.subset_ground⟩, fun ⟨⟨B, hB, hBS⟩, hSE⟩ => hB.spanning.superset hBS⟩
  obtain ⟨B, hB⟩ := M.exists_isBasis S
  have hB' := hB.isBasis_closure_right
  rw [h.closure_eq]; rw [isBasis_ground_iff] at hB'
  exact ⟨B, hB', hB.subset⟩

中文:
引理 spanning_iff_存在_isBase_subset'
  结论: M.生成 S ↔ (存在 B, M.IsBase B ∧ B subseteq S) ∧ S subseteq M.E
  证明: by
  refine ⟨fun h => ⟨?_, h.subset_ground⟩, fun ⟨⟨B, hB, hBS⟩, hSE⟩ => hB.spanning.superset hBS⟩
  obtain ⟨B, hB⟩ := M.exists_isBasis S
  have hB' := hB.isBasis_closure_right
  rw [h.closure_eq]; rw [isBasis_ground_iff] at hB'
  exact ⟨B, hB', hB.subset⟩

Depends on / 依赖: M.exists_isBasis, closure_eq, exists_isBasis, h.closure_eq, h.subset_ground, hB.isBasis_closure_right, hB.spanning.superset, hB.subset, isBasis_closure_right, isBasis_ground_iff, spanning, subset, subset_ground, superset
-/
lemma spanning_iff_exists_isBase_subset' : M.Spanning S ↔ (exists B, M.IsBase B ∧ B subseteq S) ∧ S subseteq M.E := by
  refine ⟨fun h => ⟨?_, h.subset_ground⟩, fun ⟨⟨B, hB, hBS⟩, hSE⟩ => hB.spanning.superset hBS⟩
  obtain ⟨B, hB⟩ := M.exists_isBasis S
  have hB' := hB.isBasis_closure_right
  rw [h.closure_eq]; rw [isBasis_ground_iff] at hB'
  exact ⟨B, hB', hB.subset⟩

/--
lemma `spanning_iff_exists_isBase_subset` / 引理 `spanning_iff_exists_isBase_subset`

English:
lemma spanning_iff_exists_isBase_subset
  given: (hS : S subseteq M.E := by aesop_mat)
  proof: by
  rw [spanning_iff_exists_isBase_subset']; rw [and_iff_left hS]

中文:
引理 spanning_iff_存在_isBase_subset
  条件: (hS : S subseteq M.E := by aesop_mat)
  证明: by
  rw [spanning_iff_exists_isBase_subset']; rw [and_iff_left hS]

Depends on / 依赖: IsBase, M.IsBase, M.Spanning, Spanning, aesop_mat, and_iff_left, spanning_iff_exists_isBase_subset, subseteq
-/
lemma spanning_iff_exists_isBase_subset (hS : S subseteq M.E := by aesop_mat) :
    M.Spanning S ↔ exists B, M.IsBase B ∧ B subseteq S := by
  rw [spanning_iff_exists_isBase_subset']; rw [and_iff_left hS]

/--
lemma `Spanning.exists_isBase_subset` / 引理 `Spanning.exists_isBase_subset`

English:
lemma Spanning.exists_isBase_subset
  given: (hS : M.Spanning S)
  statement: exists B, M.IsBase B ∧ B subseteq S
  proof: by
  rwa [spanning_iff_exists_isBase_subset] at hS

中文:
引理 生成.存在_isBase_subset
  条件: (hS : M.生成 S)
  结论: 存在 B, M.IsBase B ∧ B subseteq S
  证明: by
  rwa [spanning_iff_exists_isBase_subset] at hS

Depends on / 依赖: spanning_iff_exists_isBase_subset
-/
lemma Spanning.exists_isBase_subset (hS : M.Spanning S) : exists B, M.IsBase B ∧ B subseteq S := by
  rwa [spanning_iff_exists_isBase_subset] at hS

/--
lemma `coindep_iff_compl_spanning` / 引理 `coindep_iff_compl_spanning`

English:
lemma coindep_iff_compl_spanning
  given: (hI : I subseteq M.E := by aesop_mat)
  proof: by
  rw [coindep_iff_exists]; rw [spanning_iff_exists_isBase_subset]

中文:
引理 coindep_iff_compl_spanning
  条件: (hI : I subseteq M.E := by aesop_mat)
  证明: by
  rw [coindep_iff_exists]; rw [spanning_iff_exists_isBase_subset]

Depends on / 依赖: Coindep, M.Coindep, M.Spanning, Spanning, aesop_mat, coindep_iff_exists, spanning_iff_exists_isBase_subset
-/
lemma coindep_iff_compl_spanning (hI : I subseteq M.E := by aesop_mat) :
    M.Coindep I ↔ M.Spanning (M.E \ I) := by
  rw [coindep_iff_exists]; rw [spanning_iff_exists_isBase_subset]

/--
lemma `spanning_iff_compl_coindep` / 引理 `spanning_iff_compl_coindep`

English:
lemma spanning_iff_compl_coindep
  given: (hS : S subseteq M.E := by aesop_mat)
  proof: by
  rw [coindep_iff_compl_spanning]; rw [sdiff_sdiff_cancel_left hS]

中文:
引理 spanning_iff_compl_coindep
  条件: (hS : S subseteq M.E := by aesop_mat)
  证明: by
  rw [coindep_iff_compl_spanning]; rw [sdiff_sdiff_cancel_left hS]

Depends on / 依赖: Coindep, M.Coindep, M.Spanning, Spanning, aesop_mat, coindep_iff_compl_spanning, sdiff_sdiff_cancel_left
-/
lemma spanning_iff_compl_coindep (hS : S subseteq M.E := by aesop_mat) :
    M.Spanning S ↔ M.Coindep (M.E \ S) := by
  rw [coindep_iff_compl_spanning]; rw [sdiff_sdiff_cancel_left hS]

/--
lemma `Coindep.compl_spanning` / 引理 `Coindep.compl_spanning`

English:
lemma Coindep.compl_spanning
  given: (hI : M.Coindep I)
  statement: M.Spanning (M.E \ I)
  proof: (coindep_iff_compl_spanning hI.subset_ground).mp hI

中文:
引理 Coindep.compl_spanning
  条件: (hI : M.Coindep I)
  结论: M.生成 (M.E \ I)
  证明: (coindep_iff_compl_spanning hI.subset_ground).mp hI

Depends on / 依赖: coindep_iff_compl_spanning, hI.subset_ground, subset_ground
-/
lemma Coindep.compl_spanning (hI : M.Coindep I) : M.Spanning (M.E \ I) :=
  (coindep_iff_compl_spanning hI.subset_ground).mp hI

/--
lemma `coindep_iff_closure_compl_eq_ground` / 引理 `coindep_iff_closure_compl_eq_ground`

English:
lemma coindep_iff_closure_compl_eq_ground
  given: (hK : X subseteq M.E := by aesop_mat)
  proof: by
  rw [coindep_iff_compl_spanning]; rw [spanning_iff_closure_eq]

中文:
引理 coindep_iff_closure_compl_eq_ground
  条件: (hK : X subseteq M.E := by aesop_mat)
  证明: by
  rw [coindep_iff_compl_spanning]; rw [spanning_iff_closure_eq]

Depends on / 依赖: Coindep, M.Coindep, M.closure, aesop_mat, closure, coindep_iff_compl_spanning, spanning_iff_closure_eq
-/
lemma coindep_iff_closure_compl_eq_ground (hK : X subseteq M.E := by aesop_mat) :
    M.Coindep X ↔ M.closure (M.E \ X) = M.E := by
  rw [coindep_iff_compl_spanning]; rw [spanning_iff_closure_eq]

/--
lemma `Coindep.closure_compl` / 引理 `Coindep.closure_compl`

English:
lemma Coindep.closure_compl
  given: (hX : M.Coindep X)
  statement: M.closure (M.E \ X) = M.E
  proof: (coindep_iff_closure_compl_eq_ground hX.subset_ground).mp hX

中文:
引理 Coindep.closure_compl
  条件: (hX : M.Coindep X)
  结论: M.closure (M.E \ X) = M.E
  证明: (coindep_iff_closure_compl_eq_ground hX.subset_ground).mp hX

Depends on / 依赖: coindep_iff_closure_compl_eq_ground, hX.subset_ground, subset_ground
-/
lemma Coindep.closure_compl (hX : M.Coindep X) : M.closure (M.E \ X) = M.E :=
  (coindep_iff_closure_compl_eq_ground hX.subset_ground).mp hX

/--
lemma `Indep.isBase_of_spanning` / 引理 `Indep.isBase_of_spanning`

English:
lemma Indep.isBase_of_spanning
  given: (hI : M.Indep I) (hIs : M.Spanning I)
  statement: M.IsBase I
  proof: by
  obtain ⟨B, hB, hBI⟩ := hIs.exists_isBase_subset; rwa [← hB.eq_of_subset_indep hI hBI]

中文:
引理 Indep.isBase_of_spanning
  条件: (hI : M.Indep I) (hIs : M.生成 I)
  结论: M.IsBase I
  证明: by
  obtain ⟨B, hB, hBI⟩ := hIs.exists_isBase_subset; rwa [← hB.eq_of_subset_indep hI hBI]

Depends on / 依赖: eq_of_subset_indep, exists_isBase_subset, hB.eq_of_subset_indep, hIs.exists_isBase_subset
-/
lemma Indep.isBase_of_spanning (hI : M.Indep I) (hIs : M.Spanning I) : M.IsBase I := by
  obtain ⟨B, hB, hBI⟩ := hIs.exists_isBase_subset; rwa [← hB.eq_of_subset_indep hI hBI]

/--
lemma `Spanning.isBase_of_indep` / 引理 `Spanning.isBase_of_indep`

English:
lemma Spanning.isBase_of_indep
  given: (hIs : M.Spanning I) (hI : M.Indep I)
  statement: M.IsBase I
  proof: hI.isBase_of_spanning hIs

中文:
引理 生成.isBase_of_indep
  条件: (hIs : M.生成 I) (hI : M.Indep I)
  结论: M.IsBase I
  证明: hI.isBase_of_spanning hIs

Depends on / 依赖: hI.isBase_of_spanning, isBase_of_spanning
-/
lemma Spanning.isBase_of_indep (hIs : M.Spanning I) (hI : M.Indep I) : M.IsBase I :=
  hI.isBase_of_spanning hIs

/--
lemma `Indep.eq_of_spanning_subset` / 引理 `Indep.eq_of_spanning_subset`

English:
lemma Indep.eq_of_spanning_subset
  given: (hI : M.Indep I) (hS : M.Spanning S) (hSI : S subseteq I)
  statement: S = I
  proof: ((hI.subset hSI).isBase_of_spanning hS).eq_of_subset_indep hI hSI

中文:
引理 Indep.eq_of_spanning_subset
  条件: (hI : M.Indep I) (hS : M.生成 S) (hSI : S subseteq I)
  结论: S = I
  证明: ((hI.subset hSI).isBase_of_spanning hS).eq_of_subset_indep hI hSI

Depends on / 依赖: eq_of_subset_indep, hI.subset, isBase_of_spanning, subset
-/
lemma Indep.eq_of_spanning_subset (hI : M.Indep I) (hS : M.Spanning S) (hSI : S subseteq I) : S = I :=
  ((hI.subset hSI).isBase_of_spanning hS).eq_of_subset_indep hI hSI

/--
lemma `IsBasis.spanning_iff_spanning` / 引理 `IsBasis.spanning_iff_spanning`

English:
lemma IsBasis.spanning_iff_spanning
  given: (hIX : M.IsBasis I X)
  statement: M.Spanning I ↔ M.Spanning X
  proof: by
  rw [spanning_iff_closure_eq]; rw [spanning_iff_closure_eq]; rw [hIX.closure_eq_closure]

中文:
引理 是基.spanning_iff_spanning
  条件: (hIX : M.是基 I X)
  结论: M.生成 I ↔ M.生成 X
  证明: by
  rw [spanning_iff_closure_eq]; rw [spanning_iff_closure_eq]; rw [hIX.closure_eq_closure]

Depends on / 依赖: closure_eq_closure, hIX.closure_eq_closure, spanning_iff_closure_eq
-/
lemma IsBasis.spanning_iff_spanning (hIX : M.IsBasis I X) : M.Spanning I ↔ M.Spanning X := by
  rw [spanning_iff_closure_eq]; rw [spanning_iff_closure_eq]; rw [hIX.closure_eq_closure]

/--
lemma `Spanning.isBase_restrict_iff` / 引理 `Spanning.isBase_restrict_iff`

English:
lemma Spanning.isBase_restrict_iff
  given: (hS : M.Spanning S)
  statement: (M ↾ S).IsBase B ↔ M.IsBase B ∧ B subseteq S
  proof: by
  rw [isBase_restrict_iff']; rw [isBasis'_iff_isBasis]
  refine ⟨fun h => ⟨?_, h.subset⟩, fun h => h.1.indep.isBasis_of_subset_of_subset_closure h.2 ?_⟩
· exact h.indep.isBase_of_spanning by rwa [h.spanning_iff_spanning]
  rw [h.1.closure_eq]
  exact hS.subset_ground

中文:
引理 生成.isBase_restrict_iff
  条件: (hS : M.生成 S)
  结论: (M ↾ S).IsBase B ↔ M.IsBase B ∧ B subseteq S
  证明: by
  rw [isBase_restrict_iff']; rw [isBasis'_iff_isBasis]
  refine ⟨fun h => ⟨?_, h.subset⟩, fun h => h.1.indep.isBasis_of_subset_of_subset_closure h.2 ?_⟩
· exact h.indep.isBase_of_spanning by rwa [h.spanning_iff_spanning]
  rw [h.1.closure_eq]
  exact hS.subset_ground

Depends on / 依赖: _iff_isBasis, closure_eq, h.indep.isBase_of_spanning, h.spanning_iff_spanning, h.subset, hS.subset_ground, indep.isBasis_of_subset_of_subset_closure, isBase_of_spanning, isBase_restrict_iff, isBasis, isBasis_of_subset_of_subset_closure, spanning_iff_spanning, subset, subset_ground
-/
lemma Spanning.isBase_restrict_iff (hS : M.Spanning S) : (M ↾ S).IsBase B ↔ M.IsBase B ∧ B subseteq S := by
  rw [isBase_restrict_iff']; rw [isBasis'_iff_isBasis]
  refine ⟨fun h => ⟨?_, h.subset⟩, fun h => h.1.indep.isBasis_of_subset_of_subset_closure h.2 ?_⟩
· exact h.indep.isBase_of_spanning by rwa [h.spanning_iff_spanning]
  rw [h.1.closure_eq]
  exact hS.subset_ground

/--
lemma `Spanning.compl_coindep` / 引理 `Spanning.compl_coindep`

English:
lemma Spanning.compl_coindep
  given: (hS : M.Spanning S)
  statement: M.Coindep (M.E \ S)
  proof: by
  rwa [← spanning_iff_compl_coindep]

中文:
引理 生成.compl_coindep
  条件: (hS : M.生成 S)
  结论: M.Coindep (M.E \ S)
  证明: by
  rwa [← spanning_iff_compl_coindep]

Depends on / 依赖: spanning_iff_compl_coindep
-/
lemma Spanning.compl_coindep (hS : M.Spanning S) : M.Coindep (M.E \ S) := by
  rwa [← spanning_iff_compl_coindep]

/--
lemma `IsBasis.isBase_of_spanning` / 引理 `IsBasis.isBase_of_spanning`

English:
lemma IsBasis.isBase_of_spanning
  given: (hIX : M.IsBasis I X) (hX : M.Spanning X)
  statement: M.IsBase I
  proof: hIX.indep.isBase_of_spanning by rwa [hIX.spanning_iff_spanning]

中文:
引理 是基.isBase_of_spanning
  条件: (hIX : M.是基 I X) (hX : M.生成 X)
  结论: M.IsBase I
  证明: hIX.indep.isBase_of_spanning by rwa [hIX.spanning_iff_spanning]

Depends on / 依赖: hIX.indep.isBase_of_spanning, hIX.spanning_iff_spanning, isBase_of_spanning, spanning_iff_spanning
-/
lemma IsBasis.isBase_of_spanning (hIX : M.IsBasis I X) (hX : M.Spanning X) : M.IsBase I :=
hIX.indep.isBase_of_spanning by rwa [hIX.spanning_iff_spanning]

/--
lemma `Indep.exists_isBase_subset_spanning` / 引理 `Indep.exists_isBase_subset_spanning`

English:
lemma Indep.exists_isBase_subset_spanning
  given: (hI : M.Indep I) (hS : M.Spanning S) (hIS : I subseteq S)
  proof: by
  obtain ⟨B, hB⟩ := hI.subset_isBasis_of_subset hIS
  exact ⟨B, hB.1.isBase_of_spanning hS, hB.2, hB.1.subset⟩

中文:
引理 Indep.存在_isBase_subset_spanning
  条件: (hI : M.Indep I) (hS : M.生成 S) (hIS : I subseteq S)
  证明: by
  obtain ⟨B, hB⟩ := hI.subset_isBasis_of_subset hIS
  exact ⟨B, hB.1.isBase_of_spanning hS, hB.2, hB.1.subset⟩

Depends on / 依赖: hI.subset_isBasis_of_subset, isBase_of_spanning, subset, subset_isBasis_of_subset
-/
lemma Indep.exists_isBase_subset_spanning (hI : M.Indep I) (hS : M.Spanning S) (hIS : I subseteq S) :
    exists B, M.IsBase B ∧ I subseteq B ∧ B subseteq S := by
  obtain ⟨B, hB⟩ := hI.subset_isBasis_of_subset hIS
  exact ⟨B, hB.1.isBase_of_spanning hS, hB.2, hB.1.subset⟩

/--
lemma `Restriction.isBase_iff_of_spanning` / 引理 `Restriction.isBase_iff_of_spanning`

English:
lemma Restriction.isBase_iff_of_spanning
  given: {N : Matroid α} (hR : N <=r M) (hN : M.Spanning N.E)
  proof: by
  obtain ⟨R, hR : R subseteq M.E, rfl⟩ := hR
  rw [Spanning.isBase_restrict_iff (show M.Spanning R from hN)]; rw [restrict_ground_eq]

中文:
引理 限制.isBase_iff_of_spanning
  条件: {N : 拟阵 α} (hR : N <=r M) (hN : M.生成 N.E)
  证明: by
  obtain ⟨R, hR : R subseteq M.E, rfl⟩ := hR
  rw [Spanning.isBase_restrict_iff (show M.Spanning R from hN)]; rw [restrict_ground_eq]

Depends on / 依赖: M.Spanning, Spanning, Spanning.isBase_restrict_iff, isBase_restrict_iff, restrict_ground_eq, subseteq
-/
lemma Restriction.isBase_iff_of_spanning {N : Matroid α} (hR : N <=r M) (hN : M.Spanning N.E) :
    N.IsBase B ↔ (M.IsBase B ∧ B subseteq N.E) := by
  obtain ⟨R, hR : R subseteq M.E, rfl⟩ := hR
  rw [Spanning.isBase_restrict_iff (show M.Spanning R from hN)]; rw [restrict_ground_eq]

/--
lemma `ext_spanning` / 引理 `ext_spanning`

English:
lemma ext_spanning
  statement: {M M' : Matroid α} (h : M.E = M'.E)
  proof: by
  have hsp' : M.Spanning = M'.Spanning := by
    ext S
    refine (em (S subseteq M.E)).elim (fun hSE => by rw [hsp _ hSE])
      (fun hSE => iff_of_false (fun h => hSE h.subset_ground)
      (fun h' => hSE (h'.subset_ground.trans h.symm.subset)))
  rw [← dual_inj]; rw [ext_iff_indep]; rw [dual_g

中文:
引理 ext_spanning
  结论: {M M' : 拟阵 α} (h : M.E = M'.E)
  证明: by
  have hsp' : M.Spanning = M'.Spanning := by
    ext S
    refine (em (S subseteq M.E)).elim (fun hSE => by rw [hsp _ hSE])
      (fun hSE => iff_of_false (fun h => hSE h.subset_ground)
      (fun h' => hSE (h'.subset_ground.trans h.symm.subset)))
  rw [← dual_inj]; rw [ext_iff_indep]; rw [dual_g

Depends on / 依赖: M.Spanning, Spanning, and_iff_right, coindep_def, coindep_iff_compl_spanning, dual_ground, dual_inj, ext_iff_indep, h.subset_ground, h.symm.subset, iff_of_false, subset, subset_ground, subset_ground.trans, subseteq
-/
lemma ext_spanning {M M' : Matroid α} (h : M.E = M'.E)
    (hsp : forall S, S subseteq M.E -> (M.Spanning S ↔ M'.Spanning S)) : M = M' := by
  have hsp' : M.Spanning = M'.Spanning := by
    ext S
    refine (em (S subseteq M.E)).elim (fun hSE => by rw [hsp _ hSE])
      (fun hSE => iff_of_false (fun h => hSE h.subset_ground)
      (fun h' => hSE (h'.subset_ground.trans h.symm.subset)))
  rw [← dual_inj]; rw [ext_iff_indep]; rw [dual_ground]; rw [dual_ground]; rw [and_iff_right h]
  intro I hIE
  rw [← coindep_def]; rw [← coindep_def]; rw [coindep_iff_compl_spanning]; rw [coindep_iff_compl_spanning]; rw [hsp']; rw [h]

/--
lemma `IsBase.eq_of_superset_spanning` / 引理 `IsBase.eq_of_superset_spanning`

English:
lemma IsBase.eq_of_superset_spanning
  given: (hB : M.IsBase B) (hX : M.Spanning X) (hXB : X subseteq B)
  statement: B = X
  proof: have ⟨B', hB', hB'X⟩ := hX.exists_isBase_subset
  subset_antisymm (by rwa [← hB'.eq_of_subset_isBase hB (hB'X.trans hXB)]) hXB

中文:
引理 IsBase.eq_of_superset_spanning
  条件: (hB : M.IsBase B) (hX : M.生成 X) (hXB : X subseteq B)
  结论: B = X
  证明: have ⟨B', hB', hB'X⟩ := hX.exists_isBase_subset
  subset_antisymm (by rwa [← hB'.eq_of_subset_isBase hB (hB'X.trans hXB)]) hXB

Depends on / 依赖: X.trans, eq_of_subset_isBase, exists_isBase_subset, hX.exists_isBase_subset, subset_antisymm
-/
lemma IsBase.eq_of_superset_spanning (hB : M.IsBase B) (hX : M.Spanning X) (hXB : X subseteq B) : B = X :=
  have ⟨B', hB', hB'X⟩ := hX.exists_isBase_subset
  subset_antisymm (by rwa [← hB'.eq_of_subset_isBase hB (hB'X.trans hXB)]) hXB

/--
theorem `isBase_iff_minimal_spanning` / 定理 `isBase_iff_minimal_spanning`

English:
theorem isBase_iff_minimal_spanning
  statement: M.IsBase B ↔ Minimal M.Spanning B
  proof: by
  rw [minimal_subset_iff]
  refine ⟨fun h => ⟨h.spanning, fun _ => h.eq_of_superset_spanning⟩, fun ⟨h, h'⟩ => ?_⟩
  obtain ⟨B', hB', hBB'⟩ := h.exists_isBase_subset
  rwa [h' hB'.spanning hBB']

中文:
定理 isBase_iff_minimal_spanning
  结论: M.IsBase B ↔ 极小 M.生成 B
  证明: by
  rw [minimal_subset_iff]
  refine ⟨fun h => ⟨h.spanning, fun _ => h.eq_of_superset_spanning⟩, fun ⟨h, h'⟩ => ?_⟩
  obtain ⟨B', hB', hBB'⟩ := h.exists_isBase_subset
  rwa [h' hB'.spanning hBB']

Depends on / 依赖: eq_of_superset_spanning, exists_isBase_subset, h.eq_of_superset_spanning, h.exists_isBase_subset, h.spanning, minimal_subset_iff, spanning
-/
theorem isBase_iff_minimal_spanning : M.IsBase B ↔ Minimal M.Spanning B := by
  rw [minimal_subset_iff]
  refine ⟨fun h => ⟨h.spanning, fun _ => h.eq_of_superset_spanning⟩, fun ⟨h, h'⟩ => ?_⟩
  obtain ⟨B', hB', hBB'⟩ := h.exists_isBase_subset
  rwa [h' hB'.spanning hBB']

/--
theorem `Spanning.isBase_of_minimal` / 定理 `Spanning.isBase_of_minimal`

English:
theorem Spanning.isBase_of_minimal
  given: (hX : M.Spanning X) (h : forall ⦃Y⦄, M.Spanning Y -> Y subseteq X -> X = Y)
  proof: by
  rwa [isBase_iff_minimal_spanning, minimal_subset_iff, and_iff_right hX]

中文:
定理 生成.isBase_of_minimal
  条件: (hX : M.生成 X) (h : 对任意 ⦃Y⦄, M.生成 Y -> Y subseteq X -> X = Y)
  证明: by
  rwa [isBase_iff_minimal_spanning, minimal_subset_iff, and_iff_right hX]

Depends on / 依赖: and_iff_right, isBase_iff_minimal_spanning, minimal_subset_iff
-/
theorem Spanning.isBase_of_minimal (hX : M.Spanning X) (h : forall ⦃Y⦄, M.Spanning Y -> Y subseteq X -> X = Y) :
    M.IsBase X := by
  rwa [isBase_iff_minimal_spanning, minimal_subset_iff, and_iff_right hX]

end Spanning

section Constructions

variable {R S : Set α}

/--
lemma `restrict_closure_eq'` / 引理 `restrict_closure_eq'`

English:
lemma restrict_closure_eq'
  given: (M : Matroid α) (X R : Set α)
  proof: by
  obtain ⟨I, hI⟩ := (M ↾ R).exists_isBasis' X
  obtain ⟨hI', hIR⟩ := isBasis'_restrict_iff.1 hI
  ext e
  rw [← hI.closure_eq_closure]; rw [← hI'.closure_eq_closure]; rw [hI.indep.mem_closure_iff']; rw [mem_union]; rw [mem_inter_iff]; rw [hI'.indep.mem_closure_iff']; rw [restrict_ground_eq]; rw [

中文:
引理 restrict_closure_eq'
  条件: (M : 拟阵 α) (X R : 集合 α)
  证明: by
  obtain ⟨I, hI⟩ := (M ↾ R).exists_isBasis' X
  obtain ⟨hI', hIR⟩ := isBasis'_restrict_iff.1 hI
  ext e
  rw [← hI.closure_eq_closure]; rw [← hI'.closure_eq_closure]; rw [hI.indep.mem_closure_iff']; rw [mem_union]; rw [mem_inter_iff]; rw [hI'.indep.mem_closure_iff']; rw [restrict_ground_eq]; rw [
-/
@[simp] lemma restrict_closure_eq' (M : Matroid α) (X R : Set α) :
    (M ↾ R).closure X = (M.closure (X inter R) inter R) union (R \ M.E) := by
  obtain ⟨I, hI⟩ := (M ↾ R).exists_isBasis' X
  obtain ⟨hI', hIR⟩ := isBasis'_restrict_iff.1 hI
  ext e
  rw [← hI.closure_eq_closure]; rw [← hI'.closure_eq_closure]; rw [hI.indep.mem_closure_iff']; rw [mem_union]; rw [mem_inter_iff]; rw [hI'.indep.mem_closure_iff']; rw [restrict_ground_eq]; rw [restrict_indep_iff]; rw [mem_sdiff]
  by_cases he : M.Indep (insert e I)
  · simp [he, and_comm, insert_subset_iff, hIR, (he.subset_ground (mem_insert ..)),
      imp_or_left_iff_true]
  tauto

/--
lemma `restrict_closure_eq` / 引理 `restrict_closure_eq`

English:
lemma restrict_closure_eq
  given: (M : Matroid α) (hXR : X subseteq R) (hR : R subseteq M.E := by aesop_mat)
  proof: by
  rw [restrict_closure_eq']; rw [sdiff_eq_empty.mpr hR]; rw [union_empty]; rw [inter_eq_self_of_subset_left hXR]

中文:
引理 restrict_closure_eq
  条件: (M : 拟阵 α) (hXR : X subseteq R) (hR : R subseteq M.E := by aesop_mat)
  证明: by
  rw [restrict_closure_eq']; rw [sdiff_eq_empty.mpr hR]; rw [union_empty]; rw [inter_eq_self_of_subset_left hXR]

Depends on / 依赖: M.closure, aesop_mat, closure, inter_eq_self_of_subset_left, restrict_closure_eq, sdiff_eq_empty, sdiff_eq_empty.mpr, union_empty
-/
lemma restrict_closure_eq (M : Matroid α) (hXR : X subseteq R) (hR : R subseteq M.E := by aesop_mat) :
    (M ↾ R).closure X = M.closure X inter R := by
  rw [restrict_closure_eq']; rw [sdiff_eq_empty.mpr hR]; rw [union_empty]; rw [inter_eq_self_of_subset_left hXR]

/--
lemma `emptyOn_closure_eq` / 引理 `emptyOn_closure_eq`

English:
lemma emptyOn_closure_eq
  given: (X : Set α)
  statement: (emptyOn α).closure X = ∅
  proof: (closure_subset_ground ..).antisymm empty_subset _

中文:
引理 emptyOn_closure_eq
  条件: (X : 集合 α)
  结论: (emptyOn α).closure X = ∅
  证明: (closure_subset_ground ..).antisymm empty_subset _
-/
@[simp] lemma emptyOn_closure_eq (X : Set α) : (emptyOn α).closure X = ∅ :=
(closure_subset_ground ..).antisymm empty_subset _

/--
lemma `loopyOn_closure_eq` / 引理 `loopyOn_closure_eq`

English:
lemma loopyOn_closure_eq
  given: (E X : Set α)
  statement: (loopyOn E).closure X = E
  proof: by
  simp [loopyOn, restrict_closure_eq']

中文:
引理 loopyOn_closure_eq
  条件: (E X : 集合 α)
  结论: (loopyOn E).closure X = E
  证明: by
  simp [loopyOn, restrict_closure_eq']
-/
@[simp] lemma loopyOn_closure_eq (E X : Set α) : (loopyOn E).closure X = E := by
  simp [loopyOn, restrict_closure_eq']

/--
lemma `loopyOn_spanning_iff` / 引理 `loopyOn_spanning_iff`

English:
lemma loopyOn_spanning_iff
  given: {E : Set α}
  statement: (loopyOn E).Spanning X ↔ X subseteq E
  proof: by
  rw [spanning_iff]; rw [loopyOn_closure_eq]; rw [loopyOn_ground]; rw [and_iff_right rfl]

中文:
引理 loopyOn_spanning_iff
  条件: {E : 集合 α}
  结论: (loopyOn E).生成 X ↔ X subseteq E
  证明: by
  rw [spanning_iff]; rw [loopyOn_closure_eq]; rw [loopyOn_ground]; rw [and_iff_right rfl]
-/
@[simp] lemma loopyOn_spanning_iff {E : Set α} : (loopyOn E).Spanning X ↔ X subseteq E := by
  rw [spanning_iff]; rw [loopyOn_closure_eq]; rw [loopyOn_ground]; rw [and_iff_right rfl]

/--
lemma `freeOn_closure_eq` / 引理 `freeOn_closure_eq`

English:
lemma freeOn_closure_eq
  given: (E X : Set α)
  statement: (freeOn E).closure X = X inter E
  proof: by
  simp +contextual [← closure_inter_ground _ X, Set.ext_iff, and_comm,
    insert_subset_iff, freeOn_indep_iff, (freeOn_indep inter_subset_right).mem_closure_iff']

中文:
引理 freeOn_closure_eq
  条件: (E X : 集合 α)
  结论: (freeOn E).closure X = X inter E
  证明: by
  simp +contextual [← closure_inter_ground _ X, Set.ext_iff, and_comm,
    insert_subset_iff, freeOn_indep_iff, (freeOn_indep inter_subset_right).mem_closure_iff']
-/
@[simp] lemma freeOn_closure_eq (E X : Set α) : (freeOn E).closure X = X inter E := by
  simp +contextual [← closure_inter_ground _ X, Set.ext_iff, and_comm,
    insert_subset_iff, freeOn_indep_iff, (freeOn_indep inter_subset_right).mem_closure_iff']

/--
lemma `uniqueBaseOn_closure_eq` / 引理 `uniqueBaseOn_closure_eq`

English:
lemma uniqueBaseOn_closure_eq
  given: (I E X : Set α)
  proof: by
  rw [uniqueBaseOn]; rw [restrict_closure_eq']; rw [freeOn_closure_eq]; rw [inter_right_comm]; rw [inter_assoc (c := E)]; rw [inter_self]; rw [inter_right_comm]; rw [freeOn_ground]

中文:
引理 uniqueBaseOn_closure_eq
  条件: (I E X : 集合 α)
  证明: by
  rw [uniqueBaseOn]; rw [restrict_closure_eq']; rw [freeOn_closure_eq]; rw [inter_right_comm]; rw [inter_assoc (c := E)]; rw [inter_self]; rw [inter_right_comm]; rw [freeOn_ground]
-/
@[simp] lemma uniqueBaseOn_closure_eq (I E X : Set α) :
    (uniqueBaseOn I E).closure X = (X inter I inter E) union (E \ I) := by
  rw [uniqueBaseOn]; rw [restrict_closure_eq']; rw [freeOn_closure_eq]; rw [inter_right_comm]; rw [inter_assoc (c := E)]; rw [inter_self]; rw [inter_right_comm]; rw [freeOn_ground]

/--
lemma `closure_empty_eq_ground_iff` / 引理 `closure_empty_eq_ground_iff`

English:
lemma closure_empty_eq_ground_iff
  statement: M.closure ∅ = M.E ↔ M = loopyOn M.E
  proof: by
  refine ⟨fun h => ext_closure ?_, fun h => by rw [h, loopyOn_closure_eq, loopyOn_ground]⟩
  refine fun X => subset_antisymm (by simp [closure_subset_ground]) ?_
  rw [loopyOn_closure_eq]; rw [← h]
  exact M.closure_mono (empty_subset _)

中文:
引理 closure_empty_eq_ground_iff
  结论: M.closure ∅ = M.E ↔ M = loopyOn M.E
  证明: by
  refine ⟨fun h => ext_closure ?_, fun h => by rw [h, loopyOn_closure_eq, loopyOn_ground]⟩
  refine fun X => subset_antisymm (by simp [closure_subset_ground]) ?_
  rw [loopyOn_closure_eq]; rw [← h]
  exact M.closure_mono (empty_subset _)

Depends on / 依赖: M.closure_mono, closure_mono, closure_subset_ground, empty_subset, ext_closure, loopyOn_closure_eq, loopyOn_ground, subset_antisymm
-/
lemma closure_empty_eq_ground_iff : M.closure ∅ = M.E ↔ M = loopyOn M.E := by
  refine ⟨fun h => ext_closure ?_, fun h => by rw [h, loopyOn_closure_eq, loopyOn_ground]⟩
  refine fun X => subset_antisymm (by simp [closure_subset_ground]) ?_
  rw [loopyOn_closure_eq]; rw [← h]
  exact M.closure_mono (empty_subset _)

/--
lemma `comap_closure_eq` / 引理 `comap_closure_eq`

English:
lemma comap_closure_eq
  given: {β : Type*} (M : Matroid β) (f : α -> β) (X : Set α)
  proof: by
  -- Use a choice of basis and extensionality to change the goal to a statement about independence.
  obtain ⟨I, hI⟩ := (M.comap f).exists_isBasis' X
  obtain ⟨hI', hIinj, -⟩ := comap_isBasis'_iff.1 hI
  simp_rw [← hI.closure_eq_closure, ← hI'.closure_eq_closure, Set.ext_iff,
    hI.indep.mem_clo

中文:
引理 comap_closure_eq
  条件: {β : 类型} (M : 拟阵 β) (f : α -> β) (X : 集合 α)
  证明: by
  -- Use a choice of basis and extensionality to change the goal to a statement about independence.
  obtain ⟨I, hI⟩ := (M.comap f).exists_isBasis' X
  obtain ⟨hI', hIinj, -⟩ := comap_isBasis'_iff.1 hI
  simp_rw [← hI.closure_eq_closure, ← hI'.closure_eq_closure, Set.ext_iff,
    hI.indep.mem_clo
-/
@[simp] lemma comap_closure_eq {β : Type*} (M : Matroid β) (f : α -> β) (X : Set α) :
    (M.comap f).closure X = f ⁻¹' M.closure (f '' X) := by
  -- Use a choice of basis and extensionality to change the goal to a statement about independence.
  obtain ⟨I, hI⟩ := (M.comap f).exists_isBasis' X
  obtain ⟨hI', hIinj, -⟩ := comap_isBasis'_iff.1 hI
  simp_rw [← hI.closure_eq_closure, ← hI'.closure_eq_closure, Set.ext_iff,
    hI.indep.mem_closure_iff', comap_ground_eq, mem_preimage, hI'.indep.mem_closure_iff',
    comap_indep_iff, and_imp, mem_image, and_congr_right_iff, ← image_insert_eq]
  -- the lemma now easily follows by considering elements/non-elements of `I` separately.
  intro x hxE
  by_cases hxI : x in I
  · simp [hxI, show exists y in I, f y = f x from ⟨x, hxI, rfl⟩]
  simp [hxI, injOn_insert hxI, hIinj]

/--
lemma `map_closure_eq` / 引理 `map_closure_eq`

English:
lemma map_closure_eq
  given: {β : Type*} (M : Matroid α) (f : α -> β) (hf) (X : Set β)
  proof: by
  -- It is enough to prove that `map` and `closure` commute for `M`-independent sets.
  suffices aux : forall ⦃I⦄, M.Indep I -> (M.map f hf).closure (f '' I) = f '' (M.closure I) by
    obtain ⟨I, hI⟩ := M.exists_isBasis (f ⁻¹' X inter M.E)
    rw [← closure_inter_ground]; rw [map_ground]; rw [← 

中文:
引理 map_closure_eq
  条件: {β : 类型} (M : 拟阵 α) (f : α -> β) (hf) (X : 集合 β)
  证明: by
  -- It is enough to prove that `map` and `closure` commute for `M`-independent sets.
  suffices aux : forall ⦃I⦄, M.Indep I -> (M.map f hf).closure (f '' I) = f '' (M.closure I) by
    obtain ⟨I, hI⟩ := M.exists_isBasis (f ⁻¹' X inter M.E)
    rw [← closure_inter_ground]; rw [map_ground]; rw [← 
-/
@[simp] lemma map_closure_eq {β : Type*} (M : Matroid α) (f : α -> β) (hf) (X : Set β) :
    (M.map f hf).closure X = f '' M.closure (f ⁻¹' X) := by
  -- It is enough to prove that `map` and `closure` commute for `M`-independent sets.
  suffices aux : forall ⦃I⦄, M.Indep I -> (M.map f hf).closure (f '' I) = f '' (M.closure I) by
    obtain ⟨I, hI⟩ := M.exists_isBasis (f ⁻¹' X inter M.E)
    rw [← closure_inter_ground]; rw [map_ground]; rw [← M.closure_inter_ground]; rw [← hI.closure_eq_closure]; rw [← aux hI.indep]; rw [← image_preimage_inter]; rw [← (hI.map hf).closure_eq_closure]
  -- Let `I` be independent, and transform the goal using closure/independence lemmas
  refine fun I hI => Set.ext fun e => ?_
  simp only [(hI.map f hf).mem_closure_iff', map_ground, mem_image, map_indep_iff,
    forall_exists_index, and_imp, hI.mem_closure_iff']
  -- The goal now easily follows from the invariance of independence under maps.
  constructor
  · rintro ⟨⟨x, hxE, rfl⟩, h2⟩
    refine ⟨x, ⟨hxE, fun hI' => ?_⟩, rfl⟩
    obtain ⟨y, hyI, hfy⟩ := h2 _ hI' image_insert_eq.symm
    rw [hf.eq_iff (hI.subset_ground hyI) hxE] at hfy
    rwa [← hfy]
  rintro ⟨x, ⟨hxE, hxi⟩, rfl⟩
  refine ⟨⟨x, hxE, rfl⟩, fun J hJ hJI => ⟨x, hxi ?_, rfl⟩⟩
  replace hJ := hJ.map f hf
  have hrw := image_insert_eq ▸ hJI
  rwa [← hrw, map_image_indep_iff (insert_subset hxE hI.subset_ground)] at hJ

/--
lemma `restrict_spanning_iff` / 引理 `restrict_spanning_iff`

English:
lemma restrict_spanning_iff
  given: (hSR : S subseteq R) (hR : R subseteq M.E := by aesop_mat)
  proof: by
  rw [spanning_iff]; rw [restrict_ground_eq]; rw [and_iff_left hSR]; rw [restrict_closure_eq _ hSR]; rw [inter_eq_right]

中文:
引理 restrict_spanning_iff
  条件: (hSR : S subseteq R) (hR : R subseteq M.E := by aesop_mat)
  证明: by
  rw [spanning_iff]; rw [restrict_ground_eq]; rw [and_iff_left hSR]; rw [restrict_closure_eq _ hSR]; rw [inter_eq_right]

Depends on / 依赖: M.closure, Spanning, aesop_mat, and_iff_left, closure, inter_eq_right, restrict_closure_eq, restrict_ground_eq, spanning_iff, subseteq
-/
lemma restrict_spanning_iff (hSR : S subseteq R) (hR : R subseteq M.E := by aesop_mat) :
    (M ↾ R).Spanning S ↔ R subseteq M.closure S := by
  rw [spanning_iff]; rw [restrict_ground_eq]; rw [and_iff_left hSR]; rw [restrict_closure_eq _ hSR]; rw [inter_eq_right]

/--
lemma `restrict_spanning_iff'` / 引理 `restrict_spanning_iff'`

English:
lemma restrict_spanning_iff'
  statement: (M ↾ R).Spanning S ↔ R inter M.E subseteq M.closure S ∧ S subseteq R
  proof: by
  rw [spanning_iff]; rw [restrict_closure_eq']; rw [restrict_ground_eq]; rw [and_congr_left_iff]; rw [sdiff_eq_compl_inter]; rw [← union_inter_distrib_right]; rw [inter_eq_right]; rw [union_comm]; rw [← sdiff_subset_iff]; rw [sdiff_compl]
  intro hSR
  rw [inter_eq_self_of_subset_left hSR]

中文:
引理 restrict_spanning_iff'
  结论: (M ↾ R).生成 S ↔ R inter M.E subseteq M.closure S ∧ S subseteq R
  证明: by
  rw [spanning_iff]; rw [restrict_closure_eq']; rw [restrict_ground_eq]; rw [and_congr_left_iff]; rw [sdiff_eq_compl_inter]; rw [← union_inter_distrib_right]; rw [inter_eq_right]; rw [union_comm]; rw [← sdiff_subset_iff]; rw [sdiff_compl]
  intro hSR
  rw [inter_eq_self_of_subset_left hSR]

Depends on / 依赖: and_congr_left_iff, inter_eq_right, inter_eq_self_of_subset_left, restrict_closure_eq, restrict_ground_eq, sdiff_compl, sdiff_eq_compl_inter, sdiff_subset_iff, spanning_iff, union_comm, union_inter_distrib_right
-/
lemma restrict_spanning_iff' : (M ↾ R).Spanning S ↔ R inter M.E subseteq M.closure S ∧ S subseteq R := by
  rw [spanning_iff]; rw [restrict_closure_eq']; rw [restrict_ground_eq]; rw [and_congr_left_iff]; rw [sdiff_eq_compl_inter]; rw [← union_inter_distrib_right]; rw [inter_eq_right]; rw [union_comm]; rw [← sdiff_subset_iff]; rw [sdiff_compl]
  intro hSR
  rw [inter_eq_self_of_subset_left hSR]

end Constructions

end Matroid
