/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Rel

/-!
# Pseudometrics as bundled functions

This file defines a pseudometric as a bundled function.
This allows one to define a semilattice on them, and to construct families of pseudometrics.

## Implementation notes

The `PseudoMetric` definition is made as general as possible without any required axioms
for the codomain. The axioms come into play only in proofs and further constructions
like the `SemilatticeSup` instance. This allows one to talk about functions mapping into
something like `{ fuel: ℕ, time: ℕ }` even though there is no linear order.

In most cases, the codomain will be a linear ordered additive monoid like
`ℝ`, `ℝ≥0`, `ℝ≥0∞`, in which all of the axioms below are satisfied.

-/

public section

variable {X R : Type*}

variable (X R) in
/-- A pseudometric as a bundled function. -/
@[ext]
/--
Definition of `PseudoMetric` / `PseudoMetric` 的定义

English:
structure PseudoMetric
  parameters: [Zero R] [Add R] [LE R]
  axioms and operations (4):
    - toFun : X -> X -> R
    - refl'(x) : toFun x x = 0
    - symm'(x y) : toFun x y = toFun y x
    - triangle'(x y z) : toFun x z <= toFun x y + toFun y z

中文:
结构 PseudoMetric
  参数: [Zero R] [Add R] [LE R]
  公理与运算 (4 个):
    - toFun : X -> X -> R
    - refl'(x) : toFun x x = 0
    - symm'(x y) : toFun x y = toFun y x
    - triangle'(x y z) : toFun x z <= toFun x y + toFun y z
-/
structure PseudoMetric [Zero R] [Add R] [LE R] where
  /-- The underlying binary function mapping into a linearly ordered additive monoid. -/
  toFun : X -> X -> R
  /-- A pseudometric must take identical elements to 0. -/
  refl' x : toFun x x = 0
  /-- A pseudometric must be symmetric. -/
  symm' x y : toFun x y = toFun y x
  /-- A pseudometric must respect the triangle inequality. -/
  triangle' x y z : toFun x z <= toFun x y + toFun y z

namespace PseudoMetric

section Basic

variable [Zero R] [Add R] [LE R] (d : PseudoMetric X R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (PseudoMetric X R) X (X -> R)
  body: PseudoMetric.toFun
  coe_injective _ := by aesop

@[simp, norm_cast]

中文:
实例 :
  签名: FunLike (PseudoMetric X R) X (X -> R)
  定义体: PseudoMetric.toFun
  coe_injective _ := by aesop

@[simp, norm_cast]

Depends on / 依赖: PseudoMetric, PseudoMetric.toFun
-/
instance : FunLike (PseudoMetric X R) X (X -> R) where
  coe := PseudoMetric.toFun
  coe_injective _ := by aesop

@[simp, norm_cast]
/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (d : X -> X -> R) (refl symm triangle)
  statement: mk d refl symm triangle = d
  proof: rfl

中文:
引理 coe_mk
  条件: (d : X -> X -> R) (refl symm triangle)
  结论: mk d refl symm triangle = d
  证明: rfl
-/
lemma coe_mk (d : X -> X -> R) (refl symm triangle) : mk d refl symm triangle = d := rfl

/--
lemma `mk_apply` / 引理 `mk_apply`

English:
lemma mk_apply
  given: (d : X -> X -> R) (refl symm triangle) (x y : X)
  proof: rfl

@[simp]

中文:
引理 mk_apply
  条件: (d : X -> X -> R) (refl symm triangle) (x y : X)
  证明: rfl

@[simp]
-/
lemma mk_apply (d : X -> X -> R) (refl symm triangle) (x y : X) :
    mk d refl symm triangle x y = d x y :=
  rfl

@[simp]
/--
lemma `refl` / 引理 `refl`

English:
lemma refl
  given: (x : X)
  statement: d x x = 0
  proof: d.refl' x

中文:
引理 refl
  条件: (x : X)
  结论: d x x = 0
  证明: d.refl' x
-/
protected lemma refl (x : X) : d x x = 0 := d.refl' x
/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  given: (x y : X)
  statement: d x y = d y x
  proof: d.symm' x y

中文:
引理 symm
  条件: (x y : X)
  结论: d x y = d y x
  证明: d.symm' x y
-/
protected lemma symm (x y : X) : d x y = d y x := d.symm' x y
/--
lemma `triangle` / 引理 `triangle`

English:
lemma triangle
  given: (x y z : X)
  statement: d x z <= d x y + d y z
  proof: d.triangle' x y z

中文:
引理 triangle
  条件: (x y z : X)
  结论: d x z <= d x y + d y z
  证明: d.triangle' x y z
-/
protected lemma triangle (x y z : X) : d x z <= d x y + d y z := d.triangle' x y z

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (PseudoMetric X R)
  body: ⟨fun d d' => ⇑d <= d'⟩

@[simp, norm_cast]

中文:
实例 :
  签名: LE (PseudoMetric X R)
  定义体: ⟨fun d d' => ⇑d <= d'⟩

@[simp, norm_cast]
-/
instance : LE (PseudoMetric X R) := ⟨fun d d' => ⇑d <= d'⟩

@[simp, norm_cast]
/--
lemma `coe_le_coe` / 引理 `coe_le_coe`

English:
lemma coe_le_coe
  given: {d d' : PseudoMetric X R}
  proof: Iff.rfl

中文:
引理 coe_le_coe
  条件: {d d' : PseudoMetric X R}
  证明: Iff.rfl
-/
protected lemma coe_le_coe {d d' : PseudoMetric X R} :
    (d : X -> X -> R) <= d' ↔ d <= d' :=
  Iff.rfl

end Basic

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: R] [Add R] [PartialOrder R] : PartialOrder (PseudoMetric X R)
  body: .lift _ DFunLike.coe_injective

中文:
实例 [Zero
  签名: R] [Add R] [PartialOrder R] : PartialOrder (PseudoMetric X R)
  定义体: .lift _ DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
instance [Zero R] [Add R] [PartialOrder R] : PartialOrder (PseudoMetric X R) :=
  .lift _ DFunLike.coe_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddZeroClass
  signature: R] [Preorder R] : Bot (PseudoMetric X R) where
  body: 0
  bot.refl' _ := rfl
  bot.symm' _ _ := rfl
  bot.triangle' _ _ _ := by simp

@[simp, norm_cast]

中文:
实例 [AddZeroClass
  签名: R] [Preorder R] : Bot (PseudoMetric X R) where
  定义体: 0
  bot.refl' _ := rfl
  bot.symm' _ _ := rfl
  bot.triangle' _ _ _ := by simp

@[simp, norm_cast]
-/
instance [AddZeroClass R] [Preorder R] : Bot (PseudoMetric X R) where
  bot.toFun := 0
  bot.refl' _ := rfl
  bot.symm' _ _ := rfl
  bot.triangle' _ _ _ := by simp

@[simp, norm_cast]
/--
lemma `coe_bot` / 引理 `coe_bot`

English:
lemma coe_bot
  given: [AddZeroClass R] [Preorder R]
  statement: ⇑(⊥ : PseudoMetric X R) = 0
  proof: rfl

@[simp]

中文:
引理 coe_bot
  条件: [AddZeroClass R] [Preorder R]
  结论: ⇑(⊥ : PseudoMetric X R) = 0
  证明: rfl

@[simp]
-/
lemma coe_bot [AddZeroClass R] [Preorder R] : ⇑(⊥ : PseudoMetric X R) = 0 := rfl

@[simp]
/--
lemma `bot_apply` / 引理 `bot_apply`

English:
lemma bot_apply
  given: [AddZeroClass R] [Preorder R] (x y : X)
  proof: rfl

中文:
引理 bot_apply
  条件: [AddZeroClass R] [Preorder R] (x y : X)
  证明: rfl
-/
protected lemma bot_apply [AddZeroClass R] [Preorder R] (x y : X) :
    (⊥ : PseudoMetric X R) x y = 0 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddZeroClass
  signature: R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R] :
  body: {
    toFun := fun x y => (d x y) ⊔ (d' x y)
    refl' _ := by simp
    symm' x y := by simp [d.symm, d'.symm]
    triangle' := by
      intro x y z
      simp only [sup_le_iff]
      refine ⟨(d.triangle x y z).trans ?_, (d'.triangle x y z).trans ?_⟩ <;>
      apply add_le_add <;> simp
  }

@[simp, 

中文:
实例 [AddZeroClass
  签名: R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R] :
  定义体: {
    toFun := fun x y => (d x y) ⊔ (d' x y)
    refl' _ := by simp
    symm' x y := by simp [d.symm, d'.symm]
    triangle' := by
      intro x y z
      simp only [sup_le_iff]
      refine ⟨(d.triangle x y z).trans ?_, (d'.triangle x y z).trans ?_⟩ <;>
      apply add_le_add <;> simp
  }

@[simp, 
-/
instance [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R] :
    Max (PseudoMetric X R) where
  max d d' := {
    toFun := fun x y => (d x y) ⊔ (d' x y)
    refl' _ := by simp
    symm' x y := by simp [d.symm, d'.symm]
    triangle' := by
      intro x y z
      simp only [sup_le_iff]
      refine ⟨(d.triangle x y z).trans ?_, (d'.triangle x y z).trans ?_⟩ <;>
      apply add_le_add <;> simp
  }

@[simp, push_cast]
/--
lemma `coe_sup` / 引理 `coe_sup`

English:
lemma coe_sup
  statement: [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R]
  proof: rfl

@[simp]

中文:
引理 coe_sup
  结论: [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R]
  证明: rfl

@[simp]
-/
lemma coe_sup [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R]
    (d d' : PseudoMetric X R) :
    ((d ⊔ d' : PseudoMetric X R) : X -> X -> R) = (d : X -> X -> R) ⊔ d' := rfl

@[simp]
/--
lemma `sup_apply` / 引理 `sup_apply`

English:
lemma sup_apply
  statement: [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R]
  proof: rfl

中文:
引理 sup_apply
  结论: [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R]
  证明: rfl
-/
protected lemma sup_apply [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R]
    (d d' : PseudoMetric X R) (x y : X) :
    (d ⊔ d') x y = d x y ⊔ d' x y :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddZeroClass
  signature: R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R] :
  body: max
  le_sup_left := by simp [← PseudoMetric.coe_le_coe]
  le_sup_right := by simp [← PseudoMetric.coe_le_coe]
  sup_le _ _ _ := fun h h' _ _ => sup_le (h _ _) (h' _ _)

中文:
实例 [AddZeroClass
  签名: R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R] :
  定义体: max
  le_sup_left := by simp [← PseudoMetric.coe_le_coe]
  le_sup_right := by simp [← PseudoMetric.coe_le_coe]
  sup_le _ _ _ := fun h h' _ _ => sup_le (h _ _) (h' _ _)
-/
instance [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R] :
    SemilatticeSup (PseudoMetric X R) where
  sup := max
  le_sup_left := by simp [← PseudoMetric.coe_le_coe]
  le_sup_right := by simp [← PseudoMetric.coe_le_coe]
  sup_le _ _ _ := fun h h' _ _ => sup_le (h _ _) (h' _ _)

section OrderBot

variable [AddCommMonoid R] [LinearOrder R] [AddLeftStrictMono R]

/--
lemma `nonneg` / 引理 `nonneg`

English:
lemma nonneg
  given: (d : PseudoMetric X R) (x y : X)
  statement: 0 <= d x y
  proof: by
  by_contra! H
  have : d x x < 0 := by
    calc d x x <= d x y + d y x := d.triangle' x y x
      _ < 0 + 0 := by refine add_lt_add H (d.symm x y ▸ H)
      _ = 0 := by simp
  exact this.ne (d.refl x)

中文:
引理 nonneg
  条件: (d : PseudoMetric X R) (x y : X)
  结论: 0 <= d x y
  证明: by
  by_contra! H
  have : d x x < 0 := by
    calc d x x <= d x y + d y x := d.triangle' x y x
      _ < 0 + 0 := by refine add_lt_add H (d.symm x y ▸ H)
      _ = 0 := by simp
  exact this.ne (d.refl x)
-/
protected lemma nonneg (d : PseudoMetric X R) (x y : X) : 0 <= d x y := by
  by_contra! H
  have : d x x < 0 := by
    calc d x x <= d x y + d y x := d.triangle' x y x
      _ < 0 + 0 := by refine add_lt_add H (d.symm x y ▸ H)
      _ = 0 := by simp
  exact this.ne (d.refl x)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot (PseudoMetric X R)
  body: f.nonneg _ _

@[simp, push_cast]

中文:
实例 :
  签名: OrderBot (PseudoMetric X R)
  定义体: f.nonneg _ _

@[simp, push_cast]

Depends on / 依赖: f.nonneg, nonneg
-/
instance : OrderBot (PseudoMetric X R) where
  bot_le f _ _ := f.nonneg _ _

@[simp, push_cast]
/--
lemma `coe_finsetSup` / 引理 `coe_finsetSup`

English:
lemma coe_finsetSup
  statement: [IsOrderedAddMonoid R] {Y : Type*} {f : Y -> PseudoMetric X R} {s : Finset Y}
  proof: by
  simpa using (Finset.sup'_eq_sup hs (f ·)).symm

中文:
引理 coe_finsetSup
  结论: [IsOrderedAddMonoid R] {Y : 类型} {f : Y -> PseudoMetric X R} {s : Finset Y}
  证明: by
  simpa using (Finset.sup'_eq_sup hs (f ·)).symm

Depends on / 依赖: Finset, Finset.sup, _eq_sup
-/
lemma coe_finsetSup [IsOrderedAddMonoid R] {Y : Type*} {f : Y -> PseudoMetric X R} {s : Finset Y}
    (hs : s.Nonempty) :
    ⇑(s.sup f) = s.sup' hs (f ·) := by
  simpa using (Finset.sup'_eq_sup hs (f ·)).symm

/--
lemma `finsetSup_apply` / 引理 `finsetSup_apply`

English:
lemma finsetSup_apply
  statement: [IsOrderedAddMonoid R] {Y : Type*} {f : Y -> PseudoMetric X R}
  proof: by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons a s ha hs ih => simp [hs, ih]

中文:
引理 finsetSup_apply
  结论: [IsOrderedAddMonoid R] {Y : 类型} {f : Y -> PseudoMetric X R}
  证明: by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons a s ha hs ih => simp [hs, ih]

Depends on / 依赖: Finset, Finset.Nonempty.cons_induction, Nonempty, cons_induction, singleton
-/
lemma finsetSup_apply [IsOrderedAddMonoid R] {Y : Type*} {f : Y -> PseudoMetric X R}
    {s : Finset Y} (hs : s.Nonempty) (x y : X) :
    s.sup f x y = s.sup' hs fun i => f i x y := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons a s ha hs ih => simp [hs, ih]

end OrderBot

section IsUltra

/--
Definition of `IsUltra` / `IsUltra` 的定义

English:
class IsUltra
  parameters: [Zero R] [Add R] [LE R] [Max R] (d : PseudoMetric X R)
  axioms and operations (1):
    - le_sup' : forall x y z, d x z <= d x y ⊔ d y z

中文:
类 IsUltra
  参数: [Zero R] [Add R] [LE R] [Max R] (d : PseudoMetric X R)
  公理与运算 (1 个):
    - le_sup' : 对任意 x y z, d x z <= d x y ⊔ d y z
-/
class IsUltra [Zero R] [Add R] [LE R] [Max R] (d : PseudoMetric X R) : Prop where
  /-- Strong triangle inequality of an ultrametric. -/
  le_sup' : forall x y z, d x z <= d x y ⊔ d y z

/--
lemma `IsUltra.le_sup` / 引理 `IsUltra.le_sup`

English:
lemma IsUltra.le_sup
  statement: [Zero R] [Add R] [LE R] [Max R] {d : PseudoMetric X R} [hd : IsUltra d]
  proof: hd.le_sup' x y z

中文:
引理 IsUltra.le_sup
  结论: [Zero R] [Add R] [LE R] [Max R] {d : PseudoMetric X R} [hd : IsUltra d]
  证明: hd.le_sup' x y z

Depends on / 依赖: hd.le_sup, le_sup
-/
lemma IsUltra.le_sup [Zero R] [Add R] [LE R] [Max R] {d : PseudoMetric X R} [hd : IsUltra d]
    {x y z : X} : d x z <= d x y ⊔ d y z :=
  hd.le_sup' x y z

/--
Instance `IsUltra.bot` / 实例 `IsUltra.bot`

English:
instance IsUltra.bot
  signature: [AddZeroClass R] [SemilatticeSup R]
  body: by simp

中文:
实例 IsUltra.bot
  签名: [AddZeroClass R] [SemilatticeSup R]
  定义体: by simp
-/
instance IsUltra.bot [AddZeroClass R] [SemilatticeSup R] :
    IsUltra (⊥ : PseudoMetric X R) where
  le_sup' := by simp

/--
Instance `IsUltra.sup` / 实例 `IsUltra.sup`

English:
instance IsUltra.sup
  signature: [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R]
  body: by
  constructor
  intro x y z
  simp only [PseudoMetric.sup_apply]
  calc d x z ⊔ d' x z <= d x y ⊔ d y z ⊔ (d' x y ⊔ d' y z) := sup_le_sup le_sup le_sup
  _ <= d x y ⊔ d' x y ⊔ (d y z ⊔ d' y z) := by simp [sup_comm, sup_left_comm]

中文:
实例 IsUltra.sup
  签名: [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R]
  定义体: by
  constructor
  intro x y z
  simp only [PseudoMetric.sup_apply]
  calc d x z ⊔ d' x z <= d x y ⊔ d y z ⊔ (d' x y ⊔ d' y z) := sup_le_sup le_sup le_sup
  _ <= d x y ⊔ d' x y ⊔ (d y z ⊔ d' y z) := by simp [sup_comm, sup_left_comm]

Depends on / 依赖: PseudoMetric, PseudoMetric.sup_apply, le_sup, sup_apply, sup_comm, sup_le_sup, sup_left_comm
-/
instance IsUltra.sup [AddZeroClass R] [SemilatticeSup R] [AddLeftMono R] [AddRightMono R]
    {d d' : PseudoMetric X R} [IsUltra d] [IsUltra d'] : IsUltra (d ⊔ d') := by
  constructor
  intro x y z
  simp only [PseudoMetric.sup_apply]
  calc d x z ⊔ d' x z <= d x y ⊔ d y z ⊔ (d' x y ⊔ d' y z) := sup_le_sup le_sup le_sup
  _ <= d x y ⊔ d' x y ⊔ (d y z ⊔ d' y z) := by simp [sup_comm, sup_left_comm]

/--
lemma `IsUltra.finsetSup` / 引理 `IsUltra.finsetSup`

English:
lemma IsUltra.finsetSup
  statement: {Y : Type*} [AddCommMonoid R] [LinearOrder R] [AddLeftStrictMono R]
  proof: by
  constructor
  intro x y z
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  simp_rw [finsetSup_apply hs]
  apply Finset.sup'_le
  simp only [le_sup_iff, Finset.le_sup'_iff]
  intro i hi
  have h := (h i hi).le_sup' x y z
  simp only [le_sup_iff] at h
  refine h.imp ?_ ?_ <;>
  intro H <;

中文:
引理 IsUltra.finsetSup
  结论: {Y : 类型} [AddCommMonoid R] [LinearOrder R] [AddLeftStrictMono R]
  证明: by
  constructor
  intro x y z
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  simp_rw [finsetSup_apply hs]
  apply Finset.sup'_le
  simp only [le_sup_iff, Finset.le_sup'_iff]
  intro i hi
  have h := (h i hi).le_sup' x y z
  simp only [le_sup_iff] at h
  refine h.imp ?_ ?_ <;>
  intro H <;

Depends on / 依赖: Finset, Finset.le_sup, Finset.sup, _iff, eq_empty_or_nonempty, finsetSup_apply, h.imp, le_sup, le_sup_iff, s.eq_empty_or_nonempty, simp_rw
-/
lemma IsUltra.finsetSup {Y : Type*} [AddCommMonoid R] [LinearOrder R] [AddLeftStrictMono R]
    [IsOrderedAddMonoid R] {f : Y -> PseudoMetric X R} {s : Finset Y} (h : forall d in s, IsUltra (f d)) :
    IsUltra (s.sup f) := by
  constructor
  intro x y z
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  simp_rw [finsetSup_apply hs]
  apply Finset.sup'_le
  simp only [le_sup_iff, Finset.le_sup'_iff]
  intro i hi
  have h := (h i hi).le_sup' x y z
  simp only [le_sup_iff] at h
  refine h.imp ?_ ?_ <;>
  intro H <;>
  exact ⟨i, hi, H⟩

end IsUltra

section ball

/--
Instance `isSymm_ball` / 实例 `isSymm_ball`

English:
instance isSymm_ball
  signature: [Add R] [Zero R] [Preorder R] (d : PseudoMetric X R) {ε : R}
  body: by simp [d.symm]

中文:
实例 isSymm_ball
  签名: [Add R] [Zero R] [Preorder R] (d : PseudoMetric X R) {ε : R}
  定义体: by simp [d.symm]

Depends on / 依赖: d.symm
-/
instance isSymm_ball [Add R] [Zero R] [Preorder R] (d : PseudoMetric X R) {ε : R} :
    SetRel.IsSymm {xy | d xy.1 xy.2 < ε} where
  symm := by simp [d.symm]

/--
Instance `isSymm_closedBall` / 实例 `isSymm_closedBall`

English:
instance isSymm_closedBall
  signature: [Add R] [Zero R] [LE R] (d : PseudoMetric X R) {ε : R}
  body: by simp [d.symm]

中文:
实例 isSymm_closedBall
  签名: [Add R] [Zero R] [LE R] (d : PseudoMetric X R) {ε : R}
  定义体: by simp [d.symm]

Depends on / 依赖: d.symm
-/
instance isSymm_closedBall [Add R] [Zero R] [LE R] (d : PseudoMetric X R) {ε : R} :
    SetRel.IsSymm {xy | d xy.1 xy.2 <= ε} where
  symm := by simp [d.symm]

/--
Instance `IsUltra.isTrans_ball` / 实例 `IsUltra.isTrans_ball`

English:
instance IsUltra.isTrans_ball
  signature: [Add R] [Zero R] [LinearOrder R] (d : PseudoMetric X R)
  body: le_sup.trans_lt (max_lt hxy hyz)

中文:
实例 IsUltra.isTrans_ball
  签名: [Add R] [Zero R] [LinearOrder R] (d : PseudoMetric X R)
  定义体: le_sup.trans_lt (max_lt hxy hyz)

Depends on / 依赖: le_sup, le_sup.trans_lt, max_lt, trans_lt
-/
instance IsUltra.isTrans_ball [Add R] [Zero R] [LinearOrder R] (d : PseudoMetric X R)
    [d.IsUltra] {ε : R} :
      SetRel.IsTrans {xy | d xy.1 xy.2 < ε} where
    trans _ _ _ hxy hyz := le_sup.trans_lt (max_lt hxy hyz)

/--
Instance `IsUltra.isTrans_closedBall` / 实例 `IsUltra.isTrans_closedBall`

English:
instance IsUltra.isTrans_closedBall
  signature: [Add R] [Zero R] [SemilatticeSup R] (d : PseudoMetric X R)
  body: le_sup.trans (sup_le hxy hyz)

中文:
实例 IsUltra.isTrans_closedBall
  签名: [Add R] [Zero R] [SemilatticeSup R] (d : PseudoMetric X R)
  定义体: le_sup.trans (sup_le hxy hyz)

Depends on / 依赖: le_sup, le_sup.trans, sup_le
-/
instance IsUltra.isTrans_closedBall [Add R] [Zero R] [SemilatticeSup R] (d : PseudoMetric X R)
    [d.IsUltra] {ε : R} :
    SetRel.IsTrans {xy | d xy.1 xy.2 <= ε} where
  trans _ _ _ hxy hyz := le_sup.trans (sup_le hxy hyz)

end ball

end PseudoMetric
