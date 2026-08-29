/-
Copyright (c) 2025 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module

public import Mathlib.Order.PFilter
public import Mathlib.RingTheory.Ideal.Colon

/-!
# Ideal Filters

An **ideal filter** is a filter in the lattice of ideals of a ring `A`.

## Main definitions

* `IdealFilter A`: the type of an ideal filter on a ring `A`.
* `IsUniform F` : a filter `F` is uniform if whenever `I` is an ideal in the filter, then for all
  `a : A`, the colon ideal `I.colon {a}` is in `F`.
* `IsTorsionElem` : Given a filter `F`, an element, `m`, of an `A`-module, `M`, is `F`-torsion if
  there exists an ideal `L` in `F` that annihilates `m`.
* `IsTorsion` : Given a filter `F`, an `A`-module, `M`, is `F`-torsion if every element is torsion.
* `gabrielComposition` : Given two filters `F` and `G`, the Gabriel composition of `F` and `G` is
  the set of ideals `L` of `A` such that there exists an ideal `K` in `G` with `K/L` `F`-torsion.
  This is again a filter.
* `IsGabriel F` : a filter `F` is a Gabriel filter if it is uniform and satisfies axiom T4:
  for all `I : Ideal A`, if there exists `J ∈ F` such that for all `a ∈ J` the colon ideal
  `I.colon {a}` is in `F`, then `I ∈ F`.

## Main statements

* `isGabriel_iff`: a filter is Gabriel iff it is uniform and `F • F = F`.

## Notation

* `F • G`: the Gabriel composition of ideal filters `F` and `G`, defined by
  `gabrielComposition F G`.

## Implementation notes

In the classical literature (e.g. Stenström), *right linear topologies* on a ring are often
described via filters of open **right** ideals, and the terminology is frequently abused by
identifying the topology with its filter of ideals.

In this development we work systematically with **left ideals**. Accordingly, Stenström’s
right-ideal construction `(L : a) = {x ∈ A | a * x ∈ L}` is replaced by the left ideal
`L.colon {a} = {a | x * a ∈ L}`.

With this convention, uniform filters correspond to linear (additive) topologies, while the
additional Gabriel condition (axiom T4) imposes an algebraic saturation property that does not
change the induced topology.

## References

* [Bo Stenström, *Rings and Modules of Quotients*][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]
* [nLab: Uniform filter](https://ncatlab.org/nlab/show/uniform+filter)
* [nLab: Gabriel filter](https://ncatlab.org/nlab/show/Gabriel+filter)
* [nLab: Gabriel composition](https://ncatlab.org/nlab/show/Gabriel+composition+of+filters)

## Tags

ring theory, ideal, filter, uniform filter, Gabriel filter, torsion theory
-/

@[expose] public section

open scoped Pointwise

/--
Definition of `IdealFilter` / `IdealFilter` 的定义

English:
abbreviation IdealFilter
  signature: (A : Type*) [Ring A]
  body: Order.PFilter (Ideal A)

中文:
缩写 IdealFilter
  签名: (A : 类型) [Ring A]
  定义体: Order.PFilter (Ideal A)

Depends on / 依赖: Order.PFilter, PFilter
-/
abbrev IdealFilter (A : Type*) [Ring A] := Order.PFilter (Ideal A)

namespace IdealFilter

variable {A : Type*} [Ring A]

/--
Definition of `IsUniform` / `IsUniform` 的定义

English:
class IsUniform
  parameters: (F : IdealFilter A)
  axioms and operations (1):
    - colon_mem({I : Ideal A} (hI : I in F) (a : A)) : I.colon {a} in F

中文:
类 IsUniform
  参数: (F : IdealFilter A)
  公理与运算 (1 个):
    - colon_mem({I : Ideal A} (hI : I in F) (a : A)) : I.colon {a} in F
-/
class IsUniform (F : IdealFilter A) : Prop where
  /-- **Axiom T3.** See [stenstrom1975]. -/
  colon_mem {I : Ideal A} (hI : I in F) (a : A) : I.colon {a} in F

/--
Definition of `IsTorsionElem` / `IsTorsionElem` 的定义

English:
definition IsTorsionElem
  signature: (F : IdealFilter A)
  body: exists L in F, forall a in L, a • m = 0

中文:
定义 IsTorsionElem
  签名: (F : IdealFilter A)
  定义体: exists L in F, forall a in L, a • m = 0
-/
def IsTorsionElem (F : IdealFilter A)
    {M : Type*} [AddCommMonoid M] [Module A M] (m : M) : Prop :=
  exists L in F, forall a in L, a • m = 0

/--
Definition of `IsTorsion` / `IsTorsion` 的定义

English:
definition IsTorsion
  signature: (F : IdealFilter A)
  body: forall m : M, IsTorsionElem F m

中文:
定义 IsTorsion
  签名: (F : IdealFilter A)
  定义体: forall m : M, IsTorsionElem F m

Depends on / 依赖: IsTorsionElem
-/
def IsTorsion (F : IdealFilter A)
    (M : Type*) [AddCommMonoid M] [Module A M] : Prop :=
  forall m : M, IsTorsionElem F m

/--
Definition of `IsTorsionQuot` / `IsTorsionQuot` 的定义

English:
definition IsTorsionQuot
  signature: (F : IdealFilter A) (L K : Ideal A)
  body: forall k in K, exists I in F, I <= L.colon {k}

中文:
定义 IsTorsionQuot
  签名: (F : IdealFilter A) (L K : Ideal A)
  定义体: forall k in K, exists I in F, I <= L.colon {k}

Depends on / 依赖: L.colon
-/
def IsTorsionQuot (F : IdealFilter A) (L K : Ideal A) : Prop :=
  forall k in K, exists I in F, I <= L.colon {k}

/--
lemma `isTorsionQuot_inter_left_iff` / 引理 `isTorsionQuot_inter_left_iff`

English:
lemma isTorsionQuot_inter_left_iff
  given: {F : IdealFilter A} {L K : Ideal A}
  proof: by
  constructor <;>
  · intro h k hk
    rcases h k hk with ⟨I, hI, hI_le⟩
    have hcol : (L ⊓ K).colon {k} = Submodule.colon L {k} :=
      Submodule.colon_inf_eq_left_of_subset (Set.singleton_subset_iff.mpr hk)
    exact ⟨I, hI, (by simpa [hcol] using hI_le)⟩

中文:
引理 isTorsionQuot_inter_left_iff
  条件: {F : IdealFilter A} {L K : Ideal A}
  证明: by
  constructor <;>
  · intro h k hk
    rcases h k hk with ⟨I, hI, hI_le⟩
    have hcol : (L ⊓ K).colon {k} = Submodule.colon L {k} :=
      Submodule.colon_inf_eq_left_of_subset (Set.singleton_subset_iff.mpr hk)
    exact ⟨I, hI, (by simpa [hcol] using hI_le)⟩

Depends on / 依赖: Set.singleton_subset_iff.mpr, Submodule, Submodule.colon, Submodule.colon_inf_eq_left_of_subset, colon_inf_eq_left_of_subset, hI_le, singleton_subset_iff
-/
lemma isTorsionQuot_inter_left_iff {F : IdealFilter A} {L K : Ideal A} :
    IsTorsionQuot F (L ⊓ K) K ↔ IsTorsionQuot F L K := by
  constructor <;>
  · intro h k hk
    rcases h k hk with ⟨I, hI, hI_le⟩
    have hcol : (L ⊓ K).colon {k} = Submodule.colon L {k} :=
      Submodule.colon_inf_eq_left_of_subset (Set.singleton_subset_iff.mpr hk)
    exact ⟨I, hI, (by simpa [hcol] using hI_le)⟩


/--
lemma `isTorsion_def` / 引理 `isTorsion_def`

English:
lemma isTorsion_def
  given: (F : IdealFilter A) (M : Type*) [AddCommMonoid M] [Module A M]
  proof: Iff.rfl

中文:
引理 isTorsion_def
  条件: (F : IdealFilter A) (M : 类型) [AddCommMonoid M] [Module A M]
  证明: Iff.rfl
-/
@[simp] lemma isTorsion_def (F : IdealFilter A) (M : Type*) [AddCommMonoid M] [Module A M] :
    IsTorsion F M ↔ forall m : M, IsTorsionElem F m :=
  Iff.rfl

/--
lemma `isTorsionQuot_def` / 引理 `isTorsionQuot_def`

English:
lemma isTorsionQuot_def
  given: {F : IdealFilter A} {L K : Ideal A}
  proof: Iff.rfl

中文:
引理 isTorsionQuot_def
  条件: {F : IdealFilter A} {L K : Ideal A}
  证明: Iff.rfl
-/
@[simp] lemma isTorsionQuot_def {F : IdealFilter A} {L K : Ideal A} :
    IsTorsionQuot F L K ↔ forall k in (K : Set A), exists I in F, I <= L.colon {k} :=
  Iff.rfl

/--
lemma `isTorsionQuot_self` / 引理 `isTorsionQuot_self`

English:
lemma isTorsionQuot_self
  given: (F : IdealFilter A) (I : Ideal A)
  proof: by
  intro x hx
  obtain ⟨J, hJ⟩ := F.nonempty
  exact ⟨J, hJ, le_of_le_of_eq le_top (by simpa [eq_comm])⟩

中文:
引理 isTorsionQuot_self
  条件: (F : IdealFilter A) (I : Ideal A)
  证明: by
  intro x hx
  obtain ⟨J, hJ⟩ := F.nonempty
  exact ⟨J, hJ, le_of_le_of_eq le_top (by simpa [eq_comm])⟩

Depends on / 依赖: F.nonempty, eq_comm, le_of_le_of_eq, le_top, nonempty
-/
lemma isTorsionQuot_self (F : IdealFilter A) (I : Ideal A) :
    IsTorsionQuot F I I := by
  intro x hx
  obtain ⟨J, hJ⟩ := F.nonempty
  exact ⟨J, hJ, le_of_le_of_eq le_top (by simpa [eq_comm])⟩

/--
lemma `IsTorsionQuot.mono_left` / 引理 `IsTorsionQuot.mono_left`

English:
lemma IsTorsionQuot.mono_left
  statement: {F : IdealFilter A}
  proof: fun _ h => (hIK _ h).imp fun _ => And.imp_right (le_trans · (Submodule.colon_mono hIJ .rfl))

中文:
引理 IsTorsionQuot.mono_left
  结论: {F : IdealFilter A}
  证明: fun _ h => (hIK _ h).imp fun _ => And.imp_right (le_trans · (Submodule.colon_mono hIJ .rfl))

Depends on / 依赖: And.imp_right, Submodule, Submodule.colon_mono, colon_mono, imp_right, le_trans
-/
lemma IsTorsionQuot.mono_left {F : IdealFilter A}
    {I J K : Ideal A} (hIJ : I <= J) (hIK : IsTorsionQuot F I K) : IsTorsionQuot F J K :=
  fun _ h => (hIK _ h).imp fun _ => And.imp_right (le_trans · (Submodule.colon_mono hIJ .rfl))

/--
lemma `IsTorsionQuot.anti_right` / 引理 `IsTorsionQuot.anti_right`

English:
lemma IsTorsionQuot.anti_right
  statement: {F : IdealFilter A}
  proof: fun x hx => hIK x (hJK hx)

中文:
引理 IsTorsionQuot.anti_right
  结论: {F : IdealFilter A}
  证明: fun x hx => hIK x (hJK hx)
-/
lemma IsTorsionQuot.anti_right {F : IdealFilter A}
    {I J K : Ideal A} (hJK : J <= K) (hIK : IsTorsionQuot F I K) : IsTorsionQuot F I J :=
  fun x hx => hIK x (hJK hx)

/--
lemma `IsTorsionQuot.mono` / 引理 `IsTorsionQuot.mono`

English:
lemma IsTorsionQuot.mono
  statement: {F : IdealFilter A} {I J K L : Ideal A} (hIK : IsTorsionQuot F I K)
  proof: (hIK.mono_left hIJ).anti_right hLK

中文:
引理 IsTorsionQuot.mono
  结论: {F : IdealFilter A} {I J K L : Ideal A} (hIK : IsTorsionQuot F I K)
  证明: (hIK.mono_left hIJ).anti_right hLK

Depends on / 依赖: anti_right, hIK.mono_left, mono_left
-/
lemma IsTorsionQuot.mono {F : IdealFilter A} {I J K L : Ideal A} (hIK : IsTorsionQuot F I K)
    (hIJ : I <= J) (hLK : L <= K) : IsTorsionQuot F J L :=
  (hIK.mono_left hIJ).anti_right hLK

/--
lemma `IsTorsionQuot.inf` / 引理 `IsTorsionQuot.inf`

English:
lemma IsTorsionQuot.inf
  statement: {F : IdealFilter A}
  proof: by
  intro x hx
  obtain ⟨I', hI'F, hI'x⟩ := hI x hx
  obtain ⟨J', hJ'F, hJ'x⟩ := hJ x hx
  exact ⟨_, F.inf_mem hI'F hJ'F, (inf_le_inf hI'x hJ'x).trans Submodule.inf_colon.ge⟩

中文:
引理 IsTorsionQuot.inf
  结论: {F : IdealFilter A}
  证明: by
  intro x hx
  obtain ⟨I', hI'F, hI'x⟩ := hI x hx
  obtain ⟨J', hJ'F, hJ'x⟩ := hJ x hx
  exact ⟨_, F.inf_mem hI'F hJ'F, (inf_le_inf hI'x hJ'x).trans Submodule.inf_colon.ge⟩

Depends on / 依赖: F.inf_mem, Submodule, Submodule.inf_colon.ge, inf_colon, inf_le_inf, inf_mem
-/
lemma IsTorsionQuot.inf {F : IdealFilter A}
    {I J K : Ideal A} (hI : IsTorsionQuot F I K) (hJ : IsTorsionQuot F J K) :
    IsTorsionQuot F (I ⊓ J) K := by
  intro x hx
  obtain ⟨I', hI'F, hI'x⟩ := hI x hx
  obtain ⟨J', hJ'F, hJ'x⟩ := hJ x hx
  exact ⟨_, F.inf_mem hI'F hJ'F, (inf_le_inf hI'x hJ'x).trans Submodule.inf_colon.ge⟩

/--
lemma `isPFilter_gabrielComposition` / 引理 `isPFilter_gabrielComposition`

English:
lemma isPFilter_gabrielComposition
  given: (F G : IdealFilter A)
  proof: by
  refine Order.IsPFilter.of_def ?nonempty ?directed ?mem_of_le
  · obtain ⟨J, hJ⟩ := G.nonempty
    exact ⟨J, J, hJ, isTorsionQuot_self F J⟩
  · rintro I ⟨K, hK, hIK⟩ J ⟨L, hL, hJL⟩
    refine ⟨I ⊓ J, ?_, inf_le_left, inf_le_right⟩
    exact ⟨K ⊓ L, G.inf_mem hK hL,
      (hIK.anti_right inf_le_l

中文:
引理 isPFilter_gabrielComposition
  条件: (F G : IdealFilter A)
  证明: by
  refine Order.IsPFilter.of_def ?nonempty ?directed ?mem_of_le
  · obtain ⟨J, hJ⟩ := G.nonempty
    exact ⟨J, J, hJ, isTorsionQuot_self F J⟩
  · rintro I ⟨K, hK, hIK⟩ J ⟨L, hL, hJL⟩
    refine ⟨I ⊓ J, ?_, inf_le_left, inf_le_right⟩
    exact ⟨K ⊓ L, G.inf_mem hK hL,
      (hIK.anti_right inf_le_l

Depends on / 依赖: G.inf_mem, G.nonempty, IsPFilter, Order.IsPFilter.of_def, anti_right, directed, hIK.anti_right, hIK.mono_left, hJL.anti_right, inf_le_left, inf_le_right, inf_mem, isTorsionQuot_self, mem_of_le, mono_left, nonempty, of_def
-/
lemma isPFilter_gabrielComposition (F G : IdealFilter A) :
    Order.IsPFilter {L : Ideal A | exists K in G, F.IsTorsionQuot L K} := by
  refine Order.IsPFilter.of_def ?nonempty ?directed ?mem_of_le
  · obtain ⟨J, hJ⟩ := G.nonempty
    exact ⟨J, J, hJ, isTorsionQuot_self F J⟩
  · rintro I ⟨K, hK, hIK⟩ J ⟨L, hL, hJL⟩
    refine ⟨I ⊓ J, ?_, inf_le_left, inf_le_right⟩
    exact ⟨K ⊓ L, G.inf_mem hK hL,
      (hIK.anti_right inf_le_left).inf (hJL.anti_right inf_le_right)⟩
  · intro I J hIJ ⟨K, hK, hIK⟩
    exact ⟨K, hK, hIK.mono_left hIJ⟩

/--
Definition of `gabrielComposition` / `gabrielComposition` 的定义

English:
definition gabrielComposition
  signature: (F G : IdealFilter A)
  body: (isPFilter_gabrielComposition F G).toPFilter

中文:
定义 gabrielComposition
  签名: (F G : IdealFilter A)
  定义体: (isPFilter_gabrielComposition F G).toPFilter

Depends on / 依赖: isPFilter_gabrielComposition, toPFilter
-/
def gabrielComposition (F G : IdealFilter A) : IdealFilter A :=
  (isPFilter_gabrielComposition F G).toPFilter

/-- `F • G` is the Gabriel composition of ideal filters `F` and `G`. -/
scoped infixl:70 " • " => gabrielComposition

/--
Definition of `IsGabriel` / `IsGabriel` 的定义

English:
class IsGabriel
  parameters: (F : IdealFilter A)
  extends: F.IsUniform
  axioms and operations (1):
    - gabriel_closed((I : Ideal A) (h : exists J in F, forall x in J, I.colon {x} in F)) : I in F

中文:
类 IsGabriel
  参数: (F : IdealFilter A)
  继承: F.IsUniform
  公理与运算 (1 个):
    - gabriel_closed((I : Ideal A) (h : 存在 J in F, 对任意 x in J, I.colon {x} in F)) : I in F
-/
class IsGabriel (F : IdealFilter A) extends F.IsUniform where
  /-- **Axiom T4.** See [stenstrom1975]. -/
  gabriel_closed (I : Ideal A) (h : exists J in F, forall x in J, I.colon {x} in F) : I in F

/--
theorem `isGabriel_iff` / 定理 `isGabriel_iff`

English:
theorem isGabriel_iff
  given: (F : IdealFilter A)
  statement: F.IsGabriel ↔ F.IsUniform ∧ F • F = F
  proof: by
  constructor
  · intro hF
    refine ⟨hF.toIsUniform, ?_⟩
    ext I
    constructor <;> intro hI
    · rcases hI with ⟨J, hJ, htors⟩
      refine hF.gabriel_closed I ⟨J, hJ, fun x hx => ?_⟩
      rcases htors x hx with ⟨K, hK, hincl⟩
      exact Order.PFilter.mem_of_le hincl hK
    · exact ⟨I, h

中文:
定理 isGabriel_iff
  条件: (F : IdealFilter A)
  结论: F.IsGabriel ↔ F.IsUniform ∧ F • F = F
  证明: by
  constructor
  · intro hF
    refine ⟨hF.toIsUniform, ?_⟩
    ext I
    constructor <;> intro hI
    · rcases hI with ⟨J, hJ, htors⟩
      refine hF.gabriel_closed I ⟨J, hJ, fun x hx => ?_⟩
      rcases htors x hx with ⟨K, hK, hincl⟩
      exact Order.PFilter.mem_of_le hincl hK
    · exact ⟨I, h

Depends on / 依赖: I.colon, Order.PFilter.mem_of_le, PFilter, gabriel_closed, hF.gabriel_closed, hF.toIsUniform, hcolon, isTorsionQuot_self, mem_of_le, toIsUniform
-/
theorem isGabriel_iff (F : IdealFilter A) : F.IsGabriel ↔ F.IsUniform ∧ F • F = F := by
  constructor
  · intro hF
    refine ⟨hF.toIsUniform, ?_⟩
    ext I
    constructor <;> intro hI
    · rcases hI with ⟨J, hJ, htors⟩
      refine hF.gabriel_closed I ⟨J, hJ, fun x hx => ?_⟩
      rcases htors x hx with ⟨K, hK, hincl⟩
      exact Order.PFilter.mem_of_le hincl hK
    · exact ⟨I, hI, isTorsionQuot_self F I⟩
  · rintro ⟨h₁, h₂⟩
    refine { toIsUniform := h₁, gabriel_closed := ?_ }
    rintro I ⟨J, hJ, hcolon⟩
    exact h₂.le ⟨J, hJ, fun x hx => ⟨I.colon {x}, hcolon x hx, by simp⟩⟩

end IdealFilter
