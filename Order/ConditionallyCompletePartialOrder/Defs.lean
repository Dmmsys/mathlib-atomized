/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Directed
public import Mathlib.Order.SetNotation

/-! # Conditionally complete partial orders

This file defines *conditionally complete partial orders* with suprema, infima or both. These are
partial orders where every nonempty, upwards (downwards) directed set which is
bounded above (below) has a least upper bound (greatest lower bound). This class extends `SupSet`
(`InfSet`) and the requirement is that `sSup` (`sInf`) must be the least upper bound.

The three classes defined herein are:

+ `ConditionallyCompletePartialOrderSup` for partial orders with suprema,
+ `ConditionallyCompletePartialOrderInf` for partial orders with infima, and
+ `ConditionallyCompletePartialOrder` for partial orders with both suprema and infima

One common use case for these classes is the order on a von Neumann algebra, or W⋆-algebra.
This is the strongest order-theoretic structure satisfied by a von Neumann algebra;
in particular it is *not* a conditionally complete *lattice*, and indeed it is a lattice if and only
if the algebra is commutative. In addition, `ℂ` can be made to satisfy this class (one must provide
a suitable `SupSet` instance), with the order `w ≤ z ↔ w.re ≤ z.re ∧ w.im = z.im`, which is
available in the `ComplexOrder` namespace.

These use cases are the motivation for defining three classes, as compared with other parts of the
order theory library, where only the supremum versions are defined (e.g., `CompletePartialOrder` and
`OmegaCompletePartialOrder`). We note that, if these classes are used outside of order theory, then
it is more likely that the infimum versions would be useful. Indeed, whenever the underlying type
has an antitone involution (e.g., if it is an ordered ring, then negation would be such a map),
then any `ConditionallyCompletePartialOrder{Sup,Inf}` is automatically a
`ConditionallyCompletePartialOrder`. Because of the `to_dual` attribute, the additional overhead
required to add and maintain the infimum version is minimal.

-/

public section

variable {ι : Sort*} {α : Type*}

/--
Definition of `ConditionallyCompletePartialOrderInf` / `ConditionallyCompletePartialOrderInf` 的定义

English:
class ConditionallyCompletePartialOrderInf
  parameters: (α : Type*)
  extends: PartialOrder α, InfSet α
  axioms and operations (1):
    - isGLB_csInf_of_directed : forall s, DirectedOn (· >= ·) s -> s.Nonempty -> BddBelow s -> IsGLB s (sInf s)

中文:
类 余nditionallyCompletePartialOrderInf
  参数: (α : 类型)
  继承: 偏序 α, 下确界集 α
  公理与运算 (1 个):
    - isGLB_csInf_of_directed : 对任意 s, DirectedOn (· >= ·) s -> s.非空 -> BddBelow s -> IsGLB s (sInf s)
-/
class ConditionallyCompletePartialOrderInf (α : Type*)
    extends PartialOrder α, InfSet α where
  /-- For each nonempty, directed set `s` which is bounded below, `sInf s` is
  the greatest lower bound of `s`. -/
  isGLB_csInf_of_directed :
    forall s, DirectedOn (· >= ·) s -> s.Nonempty -> BddBelow s -> IsGLB s (sInf s)

/-- Conditionally complete partial orders (with suprema) are partial orders
where every nonempty, directed set which is bounded above has a least upper bound. -/
@[to_dual existing]
/--
Definition of `ConditionallyCompletePartialOrderSup` / `ConditionallyCompletePartialOrderSup` 的定义

English:
class ConditionallyCompletePartialOrderSup
  parameters: (α : Type*)
  extends: PartialOrder α, SupSet α
  axioms and operations (1):
    - isLUB_csSup_of_directed : forall s, DirectedOn (· <= ·) s -> s.Nonempty -> BddAbove s -> IsLUB s (sSup s)

中文:
类 余nditionallyCompletePartialOrderSup
  参数: (α : 类型)
  继承: 偏序 α, 上确界集 α
  公理与运算 (1 个):
    - isLUB_csSup_of_directed : 对任意 s, DirectedOn (· <= ·) s -> s.非空 -> BddAbove s -> IsLUB s (sSup s)
-/
class ConditionallyCompletePartialOrderSup (α : Type*)
    extends PartialOrder α, SupSet α where
  /-- For each nonempty, directed set `s` which is bounded above, `sSup s` is
  the least upper bound of `s`. -/
  isLUB_csSup_of_directed :
    forall s, DirectedOn (· <= ·) s -> s.Nonempty -> BddAbove s -> IsLUB s (sSup s)

/--
Definition of `ConditionallyCompletePartialOrder` / `ConditionallyCompletePartialOrder` 的定义

English:
class ConditionallyCompletePartialOrder
  parameters: (α : Type*)
  extends: ConditionallyCompletePartialOrderSup α, ConditionallyCompletePartialOrderInf α
  (no additional axioms)

中文:
类 余nditionallyCompletePartial序
  参数: (α : 类型)
  继承: 余nditionallyCompletePartialOrderSup α, 余nditionallyCompletePartialOrderInf α
  (无附加公理)
-/
class ConditionallyCompletePartialOrder (α : Type*)
    extends ConditionallyCompletePartialOrderSup α, ConditionallyCompletePartialOrderInf α where

attribute [to_dual existing]
  ConditionallyCompletePartialOrder.toConditionallyCompletePartialOrderSup

variable [ConditionallyCompletePartialOrderSup α]
variable {f : ι -> α} {s : Set α} {a : α}

@[to_dual]
/--
lemma `DirectedOn.isLUB_csSup` / 引理 `DirectedOn.isLUB_csSup`

English:
lemma DirectedOn.isLUB_csSup
  statement: (h_dir : DirectedOn (· <= ·) s)
  proof: ConditionallyCompletePartialOrderSup.isLUB_csSup_of_directed s h_dir h_non h_bdd

@[to_dual csInf_le]

中文:
引理 DirectedOn.isLUB_csSup
  结论: (h_dir : DirectedOn (· <= ·) s)
  证明: ConditionallyCompletePartialOrderSup.isLUB_csSup_of_directed s h_dir h_non h_bdd

@[to_dual csInf_le]
-/
protected lemma DirectedOn.isLUB_csSup (h_dir : DirectedOn (· <= ·) s)
    (h_non : s.Nonempty) (h_bdd : BddAbove s) : IsLUB s (sSup s) :=
  ConditionallyCompletePartialOrderSup.isLUB_csSup_of_directed s h_dir h_non h_bdd

@[to_dual csInf_le]
/--
lemma `DirectedOn.le_csSup` / 引理 `DirectedOn.le_csSup`

English:
lemma DirectedOn.le_csSup
  statement: (hs : DirectedOn (· <= ·) s)
  proof: (hs.isLUB_csSup ⟨a, ha⟩ h_bdd).1 ha

@[to_dual le_csInf]

中文:
引理 DirectedOn.le_csSup
  结论: (hs : DirectedOn (· <= ·) s)
  证明: (hs.isLUB_csSup ⟨a, ha⟩ h_bdd).1 ha

@[to_dual le_csInf]
-/
protected lemma DirectedOn.le_csSup (hs : DirectedOn (· <= ·) s)
    (h_bdd : BddAbove s) (ha : a in s) : a <= sSup s :=
  (hs.isLUB_csSup ⟨a, ha⟩ h_bdd).1 ha

@[to_dual le_csInf]
/--
lemma `DirectedOn.csSup_le` / 引理 `DirectedOn.csSup_le`

English:
lemma DirectedOn.csSup_le
  statement: (hd : DirectedOn (· <= ·) s) (h_non : s.Nonempty)
  proof: (hd.isLUB_csSup h_non ⟨a, ha⟩).2 ha

@[to_dual ciInf_le]

中文:
引理 DirectedOn.csSup_le
  结论: (hd : DirectedOn (· <= ·) s) (h_non : s.非空)
  证明: (hd.isLUB_csSup h_non ⟨a, ha⟩).2 ha

@[to_dual ciInf_le]
-/
protected lemma DirectedOn.csSup_le (hd : DirectedOn (· <= ·) s) (h_non : s.Nonempty)
    (ha : forall b in s, b <= a) : sSup s <= a :=
  (hd.isLUB_csSup h_non ⟨a, ha⟩).2 ha

@[to_dual ciInf_le]
/--
lemma `Directed.le_ciSup` / 引理 `Directed.le_ciSup`

English:
lemma Directed.le_ciSup
  statement: (hf : Directed (· <= ·) f)
  proof: hf.directedOn_range.le_csSup hf_bdd Set.mem_range_self _

@[to_dual le_ciInf]

中文:
引理 Directed.le_ciSup
  结论: (hf : Directed (· <= ·) f)
  证明: hf.directedOn_range.le_csSup hf_bdd Set.mem_range_self _

@[to_dual le_ciInf]
-/
protected lemma Directed.le_ciSup (hf : Directed (· <= ·) f)
    (hf_bdd : BddAbove (Set.range f)) (i : ι) : f i <= ⨆ j, f j :=
hf.directedOn_range.le_csSup hf_bdd Set.mem_range_self _

@[to_dual le_ciInf]
/--
lemma `Directed.ciSup_le` / 引理 `Directed.ciSup_le`

English:
lemma Directed.ciSup_le
  statement: [Nonempty ι] (hf : Directed (· <= ·) f)
  proof: hf.directedOn_range.csSup_le (Set.range_nonempty _) Set.forall_mem_range.2 ha

中文:
引理 Directed.ciSup_le
  结论: [非空 ι] (hf : Directed (· <= ·) f)
  证明: hf.directedOn_range.csSup_le (Set.range_nonempty _) Set.forall_mem_range.2 ha
-/
protected lemma Directed.ciSup_le [Nonempty ι] (hf : Directed (· <= ·) f)
    (ha : forall i, f i <= a) : ⨆ i, f i <= a :=
hf.directedOn_range.csSup_le (Set.range_nonempty _) Set.forall_mem_range.2 ha
