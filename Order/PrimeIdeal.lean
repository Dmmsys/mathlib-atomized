/-
Copyright (c) 2021 Noam Atar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noam Atar
-/
module

public import Mathlib.Order.Ideal
public import Mathlib.Order.PFilter

/-!
# Prime ideals

## Main definitions

Throughout this file, `P` is at least a preorder, but some sections require more
structure, such as a bottom element, a top element, or a join-semilattice structure.

- `Order.Ideal.PrimePair`: A pair of an `Order.Ideal` and an `Order.PFilter` which form a partition
  of `P`. This is useful as giving the data of a prime ideal is the same as giving the data of a
  prime filter.
- `Order.Ideal.IsPrime`: a predicate for prime ideals. Dual to the notion of a prime filter.
- `Order.PFilter.IsPrime`: a predicate for prime filters. Dual to the notion of a prime ideal.

## References

- <https://en.wikipedia.org/wiki/Ideal_(order_theory)>

## Tags

ideal, prime

-/

@[expose] public section


open Order.PFilter

namespace Order

variable {P : Type*}

namespace Ideal

/--
Definition of `PrimePair` / `PrimePair` 的定义

English:
structure PrimePair
  parameters: (P : Type*) [Preorder P]
  axioms and operations (3):
    - I : Ideal P
    - F : PFilter P
    - isCompl_I_F : IsCompl (I : Set P) F

中文:
结构 素数对
  参数: (P : 类型) [预序 P]
  公理与运算 (3 个):
    - I : 理想 P
    - F : PFilter P
    - isCompl_I_F : 是补集 (I : 集合 P) F

Depends on / 依赖: _one, toLocalizationMap
-/
structure PrimePair (P : Type*) [Preorder P] where
  I : Ideal P
  F : PFilter P
  isCompl_I_F : IsCompl (I : Set P) F

namespace PrimePair

variable [Preorder P] (IF : PrimePair P)

/--
theorem `compl_I_eq_F` / 定理 `compl_I_eq_F`

English:
theorem compl_I_eq_F
  statement: (IF.I : Set P)ᶜ = IF.F
  proof: IF.isCompl_I_F.compl_eq

中文:
定理 compl_I_eq_F
  结论: (IF.I : 集合 P)ᶜ = IF.F
  证明: IF.isCompl_I_F.compl_eq

Depends on / 依赖: IF.isCompl_I_F.compl_eq, _spec, compl_eq, isCompl_I_F, toLocalizationMap
-/
theorem compl_I_eq_F : (IF.I : Set P)ᶜ = IF.F :=
  IF.isCompl_I_F.compl_eq

/--
theorem `compl_F_eq_I` / 定理 `compl_F_eq_I`

English:
theorem compl_F_eq_I
  statement: (IF.F : Set P)ᶜ = IF.I
  proof: IF.isCompl_I_F.eq_compl.symm

中文:
定理 compl_F_eq_I
  结论: (IF.F : 集合 P)ᶜ = IF.I
  证明: IF.isCompl_I_F.eq_compl.symm

Depends on / 依赖: IF.isCompl_I_F.eq_compl.symm, _spec, eq_compl, isCompl_I_F, toLocalizationMap
-/
theorem compl_F_eq_I : (IF.F : Set P)ᶜ = IF.I :=
  IF.isCompl_I_F.eq_compl.symm

/--
theorem `I_isProper` / 定理 `I_isProper`

English:
theorem I_isProper
  statement: IsProper IF.I
  proof: by
  obtain ⟨w, h⟩ := IF.F.nonempty
  apply isProper_of_notMem (_ : w ∉ IF.I)
  rwa [← IF.compl_I_eq_F] at h

中文:
定理 I_isProper
  结论: 是真 IF.I
  证明: by
  obtain ⟨w, h⟩ := IF.F.nonempty
  apply isProper_of_notMem (_ : w ∉ IF.I)
  rwa [← IF.compl_I_eq_F] at h

Depends on / 依赖: IF.F.nonempty, IF.I, IF.compl_I_eq_F, _spec, compl_I_eq_F, isProper_of_notMem, nonempty
-/
theorem I_isProper : IsProper IF.I := by
  obtain ⟨w, h⟩ := IF.F.nonempty
  apply isProper_of_notMem (_ : w ∉ IF.I)
  rwa [← IF.compl_I_eq_F] at h

/--
theorem `disjoint` / 定理 `disjoint`

English:
theorem disjoint
  statement: Disjoint (IF.I : Set P) IF.F
  proof: IF.isCompl_I_F.disjoint

中文:
定理 disjoint
  结论: Disjoint (IF.I : 集合 P) IF.F
  证明: IF.isCompl_I_F.disjoint

Depends on / 依赖: _spec
-/
protected theorem disjoint : Disjoint (IF.I : Set P) IF.F :=
  IF.isCompl_I_F.disjoint

/--
theorem `I_union_F` / 定理 `I_union_F`

English:
theorem I_union_F
  statement: (IF.I : Set P) union IF.F = Set.univ
  proof: IF.isCompl_I_F.sup_eq_top

中文:
定理 I_union_F
  结论: (IF.I : 集合 P) union IF.F = 集合.univ
  证明: IF.isCompl_I_F.sup_eq_top

Depends on / 依赖: IF.isCompl_I_F.sup_eq_top, isCompl_I_F, sup_eq_top
-/
theorem I_union_F : (IF.I : Set P) union IF.F = Set.univ :=
  IF.isCompl_I_F.sup_eq_top

/--
theorem `F_union_I` / 定理 `F_union_I`

English:
theorem F_union_I
  statement: (IF.F : Set P) union IF.I = Set.univ
  proof: IF.isCompl_I_F.symm.sup_eq_top

中文:
定理 F_union_I
  结论: (IF.F : 集合 P) union IF.I = 集合.univ
  证明: IF.isCompl_I_F.symm.sup_eq_top

Depends on / 依赖: IF.isCompl_I_F.symm.sup_eq_top, _iff_mul_eq, _iff_mul_eq.mpr, eq_mk, isCompl_I_F, map_mul, sup_eq_top
-/
theorem F_union_I : (IF.F : Set P) union IF.I = Set.univ :=
  IF.isCompl_I_F.symm.sup_eq_top

end PrimePair

/-- An ideal `I` is prime if its complement is a filter.
-/
@[mk_iff]
/--
Definition of `IsPrime` / `IsPrime` 的定义

English:
class IsPrime
  parameters: [Preorder P] (I : Ideal P)
  extends: IsProper I
  axioms and operations (1):
    - compl_filter : IsPFilter (I : Set P)ᶜ

中文:
类 是素
  参数: [预序 P] (I : 理想 P)
  继承: 是真 I
  公理与运算 (1 个):
    - compl_filter : IsPFilter (I : 集合 P)ᶜ

Depends on / 依赖: _eq_iff_eq_mul, toLocalizationMap
-/
class IsPrime [Preorder P] (I : Ideal P) : Prop extends IsProper I where
  compl_filter : IsPFilter (I : Set P)ᶜ

section Preorder

variable [Preorder P]

/--
Definition of `IsPrime.toPrimePair` / `IsPrime.toPrimePair` 的定义

English:
definition IsPrime.toPrimePair
  signature: {I : Ideal P} (h : IsPrime I)
  body: { I
    F := h.compl_filter.toPFilter
    isCompl_I_F := isCompl_compl }

中文:
定义 是素.toPrimePair
  签名: {I : 理想 P} (h : 是素 I)
  定义体: { I
    F := h.compl_filter.toPFilter
    isCompl_I_F := isCompl_compl }

Depends on / 依赖: IsLocalization, IsLocalization.map_units, IsUnit, IsUnit.mul_left_inj, _spec, compl_filter, h.compl_filter.toPFilter, isCompl_I_F, isCompl_compl, map_units, mul_left_inj, right_distrib, toPFilter
-/
def IsPrime.toPrimePair {I : Ideal P} (h : IsPrime I) : PrimePair P :=
  { I
    F := h.compl_filter.toPFilter
    isCompl_I_F := isCompl_compl }

/--
theorem `PrimePair.I_isPrime` / 定理 `PrimePair.I_isPrime`

English:
theorem PrimePair.I_isPrime
  given: (IF : PrimePair P)
  statement: IsPrime IF.I
  proof: { IF.I_isProper with
    compl_filter := by
      rw [IF.compl_I_eq_F]
      exact IF.F.isPFilter }

中文:
定理 素数对.I_isPrime
  条件: (IF : 素数对 P)
  结论: 是素 IF.I
  证明: { IF.I_isProper with
    compl_filter := by
      rw [IF.compl_I_eq_F]
      exact IF.F.isPFilter }

Depends on / 依赖: IF.F.isPFilter, IF.I_isProper, IF.compl_I_eq_F, I_isProper, IsLocalization, IsLocalization.mk, SubmonoidClass, SubmonoidClass.coe_pow, _eq_iff_eq_mul, coe_pow, compl_I_eq_F, compl_filter, isPFilter, map_pow, mul_pow, simp_rw
-/
theorem PrimePair.I_isPrime (IF : PrimePair P) : IsPrime IF.I :=
  { IF.I_isProper with
    compl_filter := by
      rw [IF.compl_I_eq_F]
      exact IF.F.isPFilter }

end Preorder

section SemilatticeInf

variable [SemilatticeInf P] {I : Ideal P}

/--
theorem `IsPrime.mem_or_mem` / 定理 `IsPrime.mem_or_mem`

English:
theorem IsPrime.mem_or_mem
  given: (hI : IsPrime I) {x y : P}
  statement: x ⊓ y in I -> x in I ∨ y in I
  proof: by
  contrapose!
  let F := hI.compl_filter.toPFilter
  change x in F ∧ y in F -> x ⊓ y in F
  exact fun h => inf_mem h.1 h.2

中文:
定理 是素.mem_or_mem
  条件: (hI : 是素 I) {x y : P}
  结论: x ⊓ y in I -> x in I ∨ y in I
  证明: by
  contrapose!
  let F := hI.compl_filter.toPFilter
  change x in F ∧ y in F -> x ⊓ y in F
  exact fun h => inf_mem h.1 h.2

Depends on / 依赖: compl_filter, contrapose, hI.compl_filter.toPFilter, inf_mem, toPFilter
-/
theorem IsPrime.mem_or_mem (hI : IsPrime I) {x y : P} : x ⊓ y in I -> x in I ∨ y in I := by
  contrapose!
  let F := hI.compl_filter.toPFilter
  change x in F ∧ y in F -> x ⊓ y in F
  exact fun h => inf_mem h.1 h.2

/--
theorem `IsPrime.of_mem_or_mem` / 定理 `IsPrime.of_mem_or_mem`

English:
theorem IsPrime.of_mem_or_mem
  given: [IsProper I] (hI : forall {x y : P}, x ⊓ y in I -> x in I ∨ y in I)
  proof: by
  rw [isPrime_iff]
  use ‹_›
  refine .of_def ?_ ?_ ?_
  · exact Set.nonempty_compl.2 (I.isProper_iff.1 ‹_›)
  · intro x hx y hy
    exact ⟨x ⊓ y, fun h => (hI h).elim hx hy, inf_le_left, inf_le_right⟩
  · exact @mem_compl_of_ge _ _ _

中文:
定理 是素.of_mem_or_mem
  条件: [是真 I] (hI : 对任意 {x y : P}, x ⊓ y in I -> x in I ∨ y in I)
  证明: by
  rw [isPrime_iff]
  use ‹_›
  refine .of_def ?_ ?_ ?_
  · exact Set.nonempty_compl.2 (I.isProper_iff.1 ‹_›)
  · intro x hx y hy
    exact ⟨x ⊓ y, fun h => (hI h).elim hx hy, inf_le_left, inf_le_right⟩
  · exact @mem_compl_of_ge _ _ _

Depends on / 依赖: I.isProper_iff, Set.nonempty_compl, inf_le_left, inf_le_right, isPrime_iff, isProper_iff, mem_compl_of_ge, nonempty_compl, of_def
-/
theorem IsPrime.of_mem_or_mem [IsProper I] (hI : forall {x y : P}, x ⊓ y in I -> x in I ∨ y in I) :
    IsPrime I := by
  rw [isPrime_iff]
  use ‹_›
  refine .of_def ?_ ?_ ?_
  · exact Set.nonempty_compl.2 (I.isProper_iff.1 ‹_›)
  · intro x hx y hy
    exact ⟨x ⊓ y, fun h => (hI h).elim hx hy, inf_le_left, inf_le_right⟩
  · exact @mem_compl_of_ge _ _ _

/--
theorem `isPrime_iff_mem_or_mem` / 定理 `isPrime_iff_mem_or_mem`

English:
theorem isPrime_iff_mem_or_mem
  given: [IsProper I]
  statement: IsPrime I ↔ forall {x y : P}, x ⊓ y in I -> x in I ∨ y in I
  proof: ⟨IsPrime.mem_or_mem, IsPrime.of_mem_or_mem⟩

中文:
定理 isPrime_iff_mem_or_mem
  条件: [是真 I]
  结论: 是素 I ↔ 对任意 {x y : P}, x ⊓ y in I -> x in I ∨ y in I
  证明: ⟨IsPrime.mem_or_mem, IsPrime.of_mem_or_mem⟩

Depends on / 依赖: IsPrime, IsPrime.mem_or_mem, IsPrime.of_mem_or_mem, mem_or_mem, of_mem_or_mem
-/
theorem isPrime_iff_mem_or_mem [IsProper I] : IsPrime I ↔ forall {x y : P}, x ⊓ y in I -> x in I ∨ y in I :=
  ⟨IsPrime.mem_or_mem, IsPrime.of_mem_or_mem⟩

end SemilatticeInf

section DistribLattice

variable [DistribLattice P] {I : Ideal P}

instance (priority := 100) IsMaximal.isPrime [IsMaximal I] : IsPrime I := by
  rw [isPrime_iff_mem_or_mem]
  intro x y
  contrapose!
  rintro ⟨hx, hynI⟩ hxy
  apply hynI
  let J := I ⊔ principal x
  have hJuniv : (J : Set P) = Set.univ :=
    IsMaximal.maximal_proper (lt_sup_principal_of_notMem ‹_›)
  have hyJ : y in (J : Set P) := Set.eq_univ_iff_forall.mp hJuniv y
  rw [coe_sup_eq] at hyJ
  rcases hyJ with ⟨a, ha, b, hb, hy⟩
  rw [hy]
  refine sup_mem ha (I.lower (le_inf hb ?_) hxy)
  rw [hy]
  exact le_sup_right

end DistribLattice

section BooleanAlgebra

variable [BooleanAlgebra P] {x : P} {I : Ideal P}

/--
theorem `IsPrime.mem_or_compl_mem` / 定理 `IsPrime.mem_or_compl_mem`

English:
theorem IsPrime.mem_or_compl_mem
  given: (hI : IsPrime I)
  statement: x in I ∨ xᶜ in I
  proof: by
  apply hI.mem_or_mem
  rw [inf_compl_eq_bot]
  exact I.bot_mem

中文:
定理 是素.mem_or_compl_mem
  条件: (hI : 是素 I)
  结论: x in I ∨ xᶜ in I
  证明: by
  apply hI.mem_or_mem
  rw [inf_compl_eq_bot]
  exact I.bot_mem

Depends on / 依赖: I.bot_mem, bot_mem, hI.mem_or_mem, inf_compl_eq_bot, mem_or_mem
-/
theorem IsPrime.mem_or_compl_mem (hI : IsPrime I) : x in I ∨ xᶜ in I := by
  apply hI.mem_or_mem
  rw [inf_compl_eq_bot]
  exact I.bot_mem

/--
theorem `IsPrime.compl_mem_of_notMem` / 定理 `IsPrime.compl_mem_of_notMem`

English:
theorem IsPrime.compl_mem_of_notMem
  given: (hI : IsPrime I) (hxnI : x ∉ I)
  statement: xᶜ in I
  proof: hI.mem_or_compl_mem.resolve_left hxnI

中文:
定理 是素.compl_mem_of_notMem
  条件: (hI : 是素 I) (hxnI : x ∉ I)
  结论: xᶜ in I
  证明: hI.mem_or_compl_mem.resolve_left hxnI

Depends on / 依赖: _eq_iff_eq, hI.mem_or_compl_mem.resolve_left, mem_or_compl_mem, resolve_left, toLocalizationMap
-/
theorem IsPrime.compl_mem_of_notMem (hI : IsPrime I) (hxnI : x ∉ I) : xᶜ in I :=
  hI.mem_or_compl_mem.resolve_left hxnI

/--
theorem `isPrime_of_mem_or_compl_mem` / 定理 `isPrime_of_mem_or_compl_mem`

English:
theorem isPrime_of_mem_or_compl_mem
  given: [IsProper I] (h : forall {x : P}, x in I ∨ xᶜ in I)
  statement: IsPrime I
  proof: by
  simp only [isPrime_iff_mem_or_mem, or_iff_not_imp_left]
  intro x y hxy hxI
  have hxcI : xᶜ in I := h.resolve_left hxI
  have ass : x ⊓ y ⊔ y ⊓ xᶜ in I := sup_mem hxy (I.lower inf_le_right hxcI)
  rwa [inf_comm, sup_inf_inf_compl] at ass

中文:
定理 isPrime_of_mem_or_compl_mem
  条件: [是真 I] (h : 对任意 {x : P}, x in I ∨ xᶜ in I)
  结论: 是素 I
  证明: by
  simp only [isPrime_iff_mem_or_mem, or_iff_not_imp_left]
  intro x y hxy hxI
  have hxcI : xᶜ in I := h.resolve_left hxI
  have ass : x ⊓ y ⊔ y ⊓ xᶜ in I := sup_mem hxy (I.lower inf_le_right hxcI)
  rwa [inf_comm, sup_inf_inf_compl] at ass

Depends on / 依赖: I.lower, _eq_iff_eq, h.resolve_left, inf_comm, inf_le_right, isPrime_iff_mem_or_mem, or_iff_not_imp_left, resolve_left, sup_inf_inf_compl, sup_mem, toLocalizationMap
-/
theorem isPrime_of_mem_or_compl_mem [IsProper I] (h : forall {x : P}, x in I ∨ xᶜ in I) : IsPrime I := by
  simp only [isPrime_iff_mem_or_mem, or_iff_not_imp_left]
  intro x y hxy hxI
  have hxcI : xᶜ in I := h.resolve_left hxI
  have ass : x ⊓ y ⊔ y ⊓ xᶜ in I := sup_mem hxy (I.lower inf_le_right hxcI)
  rwa [inf_comm, sup_inf_inf_compl] at ass

/--
theorem `isPrime_iff_mem_or_compl_mem` / 定理 `isPrime_iff_mem_or_compl_mem`

English:
theorem isPrime_iff_mem_or_compl_mem
  given: [IsProper I]
  statement: IsPrime I ↔ forall {x : P}, x in I ∨ xᶜ in I
  proof: ⟨fun h _ => h.mem_or_compl_mem, isPrime_of_mem_or_compl_mem⟩

中文:
定理 isPrime_iff_mem_or_compl_mem
  条件: [是真 I]
  结论: 是素 I ↔ 对任意 {x : P}, x in I ∨ xᶜ in I
  证明: ⟨fun h _ => h.mem_or_compl_mem, isPrime_of_mem_or_compl_mem⟩

Depends on / 依赖: _eq_zero_iff, h.mem_or_compl_mem, isPrime_of_mem_or_compl_mem, mem_or_compl_mem, toLocalizationMap
-/
theorem isPrime_iff_mem_or_compl_mem [IsProper I] : IsPrime I ↔ forall {x : P}, x in I ∨ xᶜ in I :=
  ⟨fun h _ => h.mem_or_compl_mem, isPrime_of_mem_or_compl_mem⟩

instance (priority := 100) IsPrime.isMaximal [IsPrime I] : IsMaximal I := by
  simp only [isMaximal_iff, Set.eq_univ_iff_forall, IsPrime.toIsProper, true_and]
  intro J hIJ x
  rcases Set.exists_of_ssubset hIJ with ⟨y, hyJ, hyI⟩
  suffices ass : x ⊓ y ⊔ x ⊓ yᶜ in J by rwa [sup_inf_inf_compl] at ass
  exact
    sup_mem (J.lower inf_le_right hyJ)
      (hIJ.le <| I.lower inf_le_right <| IsPrime.compl_mem_of_notMem ‹_› hyI)

end BooleanAlgebra

end Ideal

namespace PFilter

variable [Preorder P]

/-- A filter `F` is prime if its complement is an ideal.
-/
@[mk_iff]
/--
Definition of `IsPrime` / `IsPrime` 的定义

English:
class IsPrime
  parameters: (F : PFilter P)
  axioms and operations (1):
    - compl_ideal : IsIdeal (F : Set P)ᶜ

中文:
类 是素
  参数: (F : PFilter P)
  公理与运算 (1 个):
    - compl_ideal : Is理想 (F : 集合 P)ᶜ

Depends on / 依赖: _zero, toLocalizationMap
-/
class IsPrime (F : PFilter P) : Prop where
  compl_ideal : IsIdeal (F : Set P)ᶜ

/--
Definition of `IsPrime.toPrimePair` / `IsPrime.toPrimePair` 的定义

English:
definition IsPrime.toPrimePair
  signature: {F : PFilter P} (h : IsPrime F)
  body: { I := h.compl_ideal.toIdeal
    F
    isCompl_I_F := isCompl_compl.symm }

中文:
定义 是素.toPrimePair
  签名: {F : PFilter P} (h : 是素 F)
  定义体: { I := h.compl_ideal.toIdeal
    F
    isCompl_I_F := isCompl_compl.symm }
-/
def IsPrime.toPrimePair {F : PFilter P} (h : IsPrime F) : Ideal.PrimePair P :=
  { I := h.compl_ideal.toIdeal
    F
    isCompl_I_F := isCompl_compl.symm }

/--
theorem `_root_.Order.Ideal.PrimePair.F_isPrime` / 定理 `_root_.Order.Ideal.PrimePair.F_isPrime`

English:
theorem _root_.Order.Ideal.PrimePair.F_isPrime
  given: (IF : Ideal.PrimePair P)
  statement: IsPrime IF.F
  proof: {
    compl_ideal := by
      rw [IF.compl_F_eq_I]
      exact IF.I.isIdeal }

中文:
定理 _root_.Order.理想.素数对.F_isPrime
  条件: (IF : 理想.素数对 P)
  结论: 是素 IF.F
  证明: {
    compl_ideal := by
      rw [IF.compl_F_eq_I]
      exact IF.I.isIdeal }

Depends on / 依赖: IF.I.isIdeal, IF.compl_F_eq_I, compl_F_eq_I, compl_ideal, isIdeal
-/
theorem _root_.Order.Ideal.PrimePair.F_isPrime (IF : Ideal.PrimePair P) : IsPrime IF.F :=
  {
    compl_ideal := by
      rw [IF.compl_F_eq_I]
      exact IF.I.isIdeal }

end PFilter

end Order
