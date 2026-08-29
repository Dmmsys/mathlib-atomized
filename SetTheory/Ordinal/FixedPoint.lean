/-
Copyright (c) 2018 Violeta Hernández Palacios, Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Mario Carneiro
-/
module

public import Mathlib.Logic.Small.List
public import Mathlib.SetTheory.Ordinal.Enum
public import Mathlib.SetTheory.Ordinal.Exponential

/-!
# Fixed points of normal functions

We prove various statements about the fixed points of normal ordinal functions. We state them in
two forms: as statements about indexed families of normal functions, and as statements about a
single normal function.

Moreover, we prove some lemmas about the fixed points of specific normal functions.

## Main definitions and results

* `nfpFamily`, `nfp`: the next fixed point of a (family of) normal function(s).
* `not_bddAbove_fp_family`, `not_bddAbove_fp`: the (common) fixed points of a (family of) normal
  function(s) are unbounded in the ordinals.
* `deriv_add_eq_mul_omega0_add`: a characterization of the derivative of addition.
* `deriv_mul_eq_opow_omega0_mul`: a characterization of the derivative of multiplication.
-/

@[expose] public section


noncomputable section

universe u v

open Function Order

namespace Ordinal

/-! ### Fixed points of type-indexed families of ordinals -/

section

variable {ι : Type*} {f : ι -> Ordinal.{u} -> Ordinal.{u}}

/--
Definition of `nfpFamily` / `nfpFamily` 的定义

English:
definition nfpFamily
  signature: (f : ι -> Ordinal.{u} -> Ordinal.{u}) (a : Ordinal.{u})
  body: ⨆ i, List.foldr f a i

中文:
定义 nfpFamily
  签名: (f : ι -> Ordinal.{u} -> Ordinal.{u}) (a : Ordinal.{u})
  定义体: ⨆ i, List.foldr f a i

Depends on / 依赖: List.foldr
-/
def nfpFamily (f : ι -> Ordinal.{u} -> Ordinal.{u}) (a : Ordinal.{u}) : Ordinal :=
  ⨆ i, List.foldr f a i

/--
theorem `foldr_le_nfpFamily` / 定理 `foldr_le_nfpFamily`

English:
theorem foldr_le_nfpFamily
  given: [Small.{u} ι] (f : ι -> Ordinal.{u} -> Ordinal.{u}) (a l)
  proof: Ordinal.le_iSup _ _

中文:
定理 foldr_le_nfpFamily
  条件: [Small.{u} ι] (f : ι -> Ordinal.{u} -> Ordinal.{u}) (a l)
  证明: Ordinal.le_iSup _ _

Depends on / 依赖: IsIsometricSMul, IsIsometricSMul.to_continuousConstSMul, Ordinal, Ordinal.le_iSup, PseudoEMetricSpace, le_iSup, to_continuousConstSMul
-/
theorem foldr_le_nfpFamily [Small.{u} ι] (f : ι -> Ordinal.{u} -> Ordinal.{u}) (a l) :
    List.foldr f a l <= nfpFamily f a :=
  Ordinal.le_iSup _ _

/--
theorem `le_nfpFamily` / 定理 `le_nfpFamily`

English:
theorem le_nfpFamily
  given: [Small.{u} ι] (f : ι -> Ordinal.{u} -> Ordinal.{u}) (a)
  statement: a <= nfpFamily f a
  proof: foldr_le_nfpFamily f a []

中文:
定理 le_nfpFamily
  条件: [Small.{u} ι] (f : ι -> Ordinal.{u} -> Ordinal.{u}) (a)
  结论: a <= nfpFamily f a
  证明: foldr_le_nfpFamily f a []

Depends on / 依赖: IsIsometricSMul, IsIsometricSMul.opposite_of_comm, PseudoEMetricSpace, foldr_le_nfpFamily, opposite_of_comm
-/
theorem le_nfpFamily [Small.{u} ι] (f : ι -> Ordinal.{u} -> Ordinal.{u}) (a) : a <= nfpFamily f a :=
  foldr_le_nfpFamily f a []

/--
theorem `lt_nfpFamily_iff` / 定理 `lt_nfpFamily_iff`

English:
theorem lt_nfpFamily_iff
  given: [Small.{u} ι] {a b}
  statement: a < nfpFamily f b ↔ exists l, a < List.foldr f b l
  proof: Ordinal.lt_iSup_iff

中文:
定理 lt_nfpFamily_iff
  条件: [Small.{u} ι] {a b}
  结论: a < nfpFamily f b ↔ 存在 l, a < List.foldr f b l
  证明: Ordinal.lt_iSup_iff

Depends on / 依赖: Ordinal, Ordinal.lt_iSup_iff, lt_iSup_iff
-/
theorem lt_nfpFamily_iff [Small.{u} ι] {a b} : a < nfpFamily f b ↔ exists l, a < List.foldr f b l :=
  Ordinal.lt_iSup_iff

/--
theorem `nfpFamily_le_iff` / 定理 `nfpFamily_le_iff`

English:
theorem nfpFamily_le_iff
  given: [Small.{u} ι] {a b}
  statement: nfpFamily f a <= b ↔ forall l, List.foldr f a l <= b
  proof: Ordinal.iSup_le_iff

中文:
定理 nfpFamily_le_iff
  条件: [Small.{u} ι] {a b}
  结论: nfpFamily f a <= b ↔ 对任意 l, List.foldr f a l <= b
  证明: Ordinal.iSup_le_iff

Depends on / 依赖: Ordinal, Ordinal.iSup_le_iff, iSup_le_iff
-/
theorem nfpFamily_le_iff [Small.{u} ι] {a b} : nfpFamily f a <= b ↔ forall l, List.foldr f a l <= b :=
  Ordinal.iSup_le_iff

/--
theorem `nfpFamily_le` / 定理 `nfpFamily_le`

English:
theorem nfpFamily_le
  given: {a b}
  statement: (forall l, List.foldr f a l <= b) -> nfpFamily f a <= b
  proof: Ordinal.iSup_le

中文:
定理 nfpFamily_le
  条件: {a b}
  结论: (对任意 l, List.foldr f a l <= b) -> nfpFamily f a <= b
  证明: Ordinal.iSup_le

Depends on / 依赖: Ordinal, Ordinal.iSup_le, iSup_le
-/
theorem nfpFamily_le {a b} : (forall l, List.foldr f a l <= b) -> nfpFamily f a <= b :=
  Ordinal.iSup_le

/--
theorem `nfpFamily_monotone` / 定理 `nfpFamily_monotone`

English:
theorem nfpFamily_monotone
  given: [Small.{u} ι] (hf : forall i, Monotone (f i))
  statement: Monotone (nfpFamily f)
  proof: fun _ _ h => nfpFamily_le fun l => (List.foldr_monotone hf l h).trans (foldr_le_nfpFamily _ _ l)

中文:
定理 nfpFamily_monotone
  条件: [Small.{u} ι] (hf : 对任意 i, Monotone (f i))
  结论: Monotone (nfpFamily f)
  证明: fun _ _ h => nfpFamily_le fun l => (List.foldr_monotone hf l h).trans (foldr_le_nfpFamily _ _ l)

Depends on / 依赖: List.foldr_monotone, foldr_le_nfpFamily, foldr_monotone, nfpFamily_le
-/
theorem nfpFamily_monotone [Small.{u} ι] (hf : forall i, Monotone (f i)) : Monotone (nfpFamily f) :=
fun _ _ h => nfpFamily_le fun l => (List.foldr_monotone hf l h).trans (foldr_le_nfpFamily _ _ l)

/--
theorem `apply_lt_nfpFamily` / 定理 `apply_lt_nfpFamily`

English:
theorem apply_lt_nfpFamily
  statement: [Small.{u} ι] (H : forall i, IsNormal (f i)) {a b}
  proof: let ⟨l, hl⟩ := lt_nfpFamily_iff.1 hb
  lt_nfpFamily_iff.2 ⟨i::l, (H i).strictMono hl⟩

中文:
定理 apply_lt_nfpFamily
  结论: [Small.{u} ι] (H : 对任意 i, IsNormal (f i)) {a b}
  证明: let ⟨l, hl⟩ := lt_nfpFamily_iff.1 hb
  lt_nfpFamily_iff.2 ⟨i::l, (H i).strictMono hl⟩

Depends on / 依赖: lt_nfpFamily_iff, strictMono
-/
theorem apply_lt_nfpFamily [Small.{u} ι] (H : forall i, IsNormal (f i)) {a b}
    (hb : b < nfpFamily f a) (i) : f i b < nfpFamily f a :=
  let ⟨l, hl⟩ := lt_nfpFamily_iff.1 hb
  lt_nfpFamily_iff.2 ⟨i::l, (H i).strictMono hl⟩

/--
theorem `apply_lt_nfpFamily_iff` / 定理 `apply_lt_nfpFamily_iff`

English:
theorem apply_lt_nfpFamily_iff
  given: [Nonempty ι] [Small.{u} ι] (H : forall i, IsNormal (f i)) {a b}
  proof: by
  refine ⟨fun h => ?_, apply_lt_nfpFamily H⟩
  let ⟨l, hl⟩ := lt_nfpFamily_iff.1 (h (Classical.arbitrary ι))
exact lt_nfpFamily_iff.2 ⟨l, (H _).strictMono.le_apply.trans_lt hl⟩

中文:
定理 apply_lt_nfpFamily_iff
  条件: [Nonempty ι] [Small.{u} ι] (H : 对任意 i, IsNormal (f i)) {a b}
  证明: by
  refine ⟨fun h => ?_, apply_lt_nfpFamily H⟩
  let ⟨l, hl⟩ := lt_nfpFamily_iff.1 (h (Classical.arbitrary ι))
exact lt_nfpFamily_iff.2 ⟨l, (H _).strictMono.le_apply.trans_lt hl⟩

Depends on / 依赖: Classical, Classical.arbitrary, apply_lt_nfpFamily, arbitrary, le_apply, lt_nfpFamily_iff, strictMono, strictMono.le_apply.trans_lt, trans_lt
-/
theorem apply_lt_nfpFamily_iff [Nonempty ι] [Small.{u} ι] (H : forall i, IsNormal (f i)) {a b} :
    (forall i, f i b < nfpFamily f a) ↔ b < nfpFamily f a := by
  refine ⟨fun h => ?_, apply_lt_nfpFamily H⟩
  let ⟨l, hl⟩ := lt_nfpFamily_iff.1 (h (Classical.arbitrary ι))
exact lt_nfpFamily_iff.2 ⟨l, (H _).strictMono.le_apply.trans_lt hl⟩

/--
theorem `nfpFamily_le_apply` / 定理 `nfpFamily_le_apply`

English:
theorem nfpFamily_le_apply
  given: [Nonempty ι] [Small.{u} ι] (H : forall i, IsNormal (f i)) {a b}
  proof: by
  contrapose!; exact apply_lt_nfpFamily_iff H

中文:
定理 nfpFamily_le_apply
  条件: [Nonempty ι] [Small.{u} ι] (H : 对任意 i, IsNormal (f i)) {a b}
  证明: by
  contrapose!; exact apply_lt_nfpFamily_iff H

Depends on / 依赖: apply_lt_nfpFamily_iff, contrapose
-/
theorem nfpFamily_le_apply [Nonempty ι] [Small.{u} ι] (H : forall i, IsNormal (f i)) {a b} :
    (exists i, nfpFamily f a <= f i b) ↔ nfpFamily f a <= b := by
  contrapose!; exact apply_lt_nfpFamily_iff H

/--
theorem `nfpFamily_le_fp` / 定理 `nfpFamily_le_fp`

English:
theorem nfpFamily_le_fp
  given: (H : forall i, Monotone (f i)) {a b} (ab : a <= b) (h : forall i, f i b <= b)
  proof: by
  apply Ordinal.iSup_le fun l => ?_
  induction l generalizing a with
  | nil => exact ab
  | cons i l IH => exact (H i (IH ab)).trans (h i)

中文:
定理 nfpFamily_le_fp
  条件: (H : 对任意 i, Monotone (f i)) {a b} (ab : a <= b) (h : 对任意 i, f i b <= b)
  证明: by
  apply Ordinal.iSup_le fun l => ?_
  induction l generalizing a with
  | nil => exact ab
  | cons i l IH => exact (H i (IH ab)).trans (h i)

Depends on / 依赖: Ordinal, Ordinal.iSup_le, generalizing, iSup_le
-/
theorem nfpFamily_le_fp (H : forall i, Monotone (f i)) {a b} (ab : a <= b) (h : forall i, f i b <= b) :
    nfpFamily f a <= b := by
  apply Ordinal.iSup_le fun l => ?_
  induction l generalizing a with
  | nil => exact ab
  | cons i l IH => exact (H i (IH ab)).trans (h i)

/--
theorem `nfpFamily_fp` / 定理 `nfpFamily_fp`

English:
theorem nfpFamily_fp
  given: [Small.{u} ι] {i} (H : IsNormal (f i)) (a)
  proof: by
  rw [nfpFamily]; rw [H.map_iSup bddAbove_of_small]
  apply le_antisymm <;> refine Ordinal.iSup_le fun l => ?_
  · exact Ordinal.le_iSup _ (i::l)
  · exact H.strictMono.le_apply.trans (Ordinal.le_iSup _ _)

中文:
定理 nfpFamily_fp
  条件: [Small.{u} ι] {i} (H : IsNormal (f i)) (a)
  证明: by
  rw [nfpFamily]; rw [H.map_iSup bddAbove_of_small]
  apply le_antisymm <;> refine Ordinal.iSup_le fun l => ?_
  · exact Ordinal.le_iSup _ (i::l)
  · exact H.strictMono.le_apply.trans (Ordinal.le_iSup _ _)

Depends on / 依赖: H.map_iSup, H.strictMono.le_apply.trans, Ordinal, Ordinal.iSup_le, Ordinal.le_iSup, bddAbove_of_small, iSup_le, le_antisymm, le_apply, le_iSup, map_iSup, nfpFamily, strictMono
-/
theorem nfpFamily_fp [Small.{u} ι] {i} (H : IsNormal (f i)) (a) :
    f i (nfpFamily f a) = nfpFamily f a := by
  rw [nfpFamily]; rw [H.map_iSup bddAbove_of_small]
  apply le_antisymm <;> refine Ordinal.iSup_le fun l => ?_
  · exact Ordinal.le_iSup _ (i::l)
  · exact H.strictMono.le_apply.trans (Ordinal.le_iSup _ _)

/--
theorem `apply_le_nfpFamily` / 定理 `apply_le_nfpFamily`

English:
theorem apply_le_nfpFamily
  given: [Small.{u} ι] [hι : Nonempty ι] (H : forall i, IsNormal (f i)) {a b}
  proof: by
  refine ⟨fun h => ?_, fun h i => ?_⟩
  · obtain ⟨i⟩ := hι
    exact (H i).strictMono.le_apply.trans (h i)
  · rw [← nfpFamily_fp (H i)]
    exact (H i).monotone h

中文:
定理 apply_le_nfpFamily
  条件: [Small.{u} ι] [hι : Nonempty ι] (H : 对任意 i, IsNormal (f i)) {a b}
  证明: by
  refine ⟨fun h => ?_, fun h i => ?_⟩
  · obtain ⟨i⟩ := hι
    exact (H i).strictMono.le_apply.trans (h i)
  · rw [← nfpFamily_fp (H i)]
    exact (H i).monotone h

Depends on / 依赖: le_apply, monotone, nfpFamily_fp, strictMono, strictMono.le_apply.trans
-/
theorem apply_le_nfpFamily [Small.{u} ι] [hι : Nonempty ι] (H : forall i, IsNormal (f i)) {a b} :
    (forall i, f i b <= nfpFamily f a) ↔ b <= nfpFamily f a := by
  refine ⟨fun h => ?_, fun h i => ?_⟩
  · obtain ⟨i⟩ := hι
    exact (H i).strictMono.le_apply.trans (h i)
  · rw [← nfpFamily_fp (H i)]
    exact (H i).monotone h

/--
theorem `nfpFamily_eq_self` / 定理 `nfpFamily_eq_self`

English:
theorem nfpFamily_eq_self
  given: [Small.{u} ι] {a} (h : forall i, f i a = a)
  statement: nfpFamily f a = a
  proof: by
  apply (Ordinal.iSup_le ?_).antisymm (le_nfpFamily f a)
  intro l
  rw [List.foldr_fixed' h l]

中文:
定理 nfpFamily_eq_self
  条件: [Small.{u} ι] {a} (h : 对任意 i, f i a = a)
  结论: nfpFamily f a = a
  证明: by
  apply (Ordinal.iSup_le ?_).antisymm (le_nfpFamily f a)
  intro l
  rw [List.foldr_fixed' h l]

Depends on / 依赖: List.foldr_fixed, Ordinal, Ordinal.iSup_le, antisymm, foldr_fixed, iSup_le, le_nfpFamily
-/
theorem nfpFamily_eq_self [Small.{u} ι] {a} (h : forall i, f i a = a) : nfpFamily f a = a := by
  apply (Ordinal.iSup_le ?_).antisymm (le_nfpFamily f a)
  intro l
  rw [List.foldr_fixed' h l]

-- Todo: This is actually a special case of the fact the intersection of club sets is a club set.
/--
theorem `not_bddAbove_fp_family` / 定理 `not_bddAbove_fp_family`

English:
theorem not_bddAbove_fp_family
  given: [Small.{u} ι] (H : forall i, IsNormal (f i))
  proof: by
  rw [not_bddAbove_iff]
  refine fun a => ⟨nfpFamily f (succ a), ?_, (lt_succ a).trans_le (le_nfpFamily f _)⟩
  rintro _ ⟨i, rfl⟩
  exact nfpFamily_fp (H i) _

中文:
定理 not_bddAbove_fp_family
  条件: [Small.{u} ι] (H : 对任意 i, IsNormal (f i))
  证明: by
  rw [not_bddAbove_iff]
  refine fun a => ⟨nfpFamily f (succ a), ?_, (lt_succ a).trans_le (le_nfpFamily f _)⟩
  rintro _ ⟨i, rfl⟩
  exact nfpFamily_fp (H i) _

Depends on / 依赖: le_nfpFamily, lt_succ, nfpFamily, nfpFamily_fp, not_bddAbove_iff, trans_le
-/
theorem not_bddAbove_fp_family [Small.{u} ι] (H : forall i, IsNormal (f i)) :
    ¬ BddAbove (⋂ i, Function.fixedPoints (f i)) := by
  rw [not_bddAbove_iff]
  refine fun a => ⟨nfpFamily f (succ a), ?_, (lt_succ a).trans_le (le_nfpFamily f _)⟩
  rintro _ ⟨i, rfl⟩
  exact nfpFamily_fp (H i) _

/--
Definition of `derivFamily` / `derivFamily` 的定义

English:
definition derivFamily
  signature: (f : ι -> Ordinal.{u} -> Ordinal.{u}) (o : Ordinal.{u})
  body: limitRecOn o (nfpFamily f 0) (fun _ IH => nfpFamily f (succ IH))
    fun a _ g => ⨆ b : Set.Iio a, g _ b.2

@[simp]

中文:
定义 derivFamily
  签名: (f : ι -> Ordinal.{u} -> Ordinal.{u}) (o : Ordinal.{u})
  定义体: limitRecOn o (nfpFamily f 0) (fun _ IH => nfpFamily f (succ IH))
    fun a _ g => ⨆ b : Set.Iio a, g _ b.2

@[simp]

Depends on / 依赖: Set.Iio, limitRecOn, nfpFamily
-/
def derivFamily (f : ι -> Ordinal.{u} -> Ordinal.{u}) (o : Ordinal.{u}) : Ordinal.{u} :=
  limitRecOn o (nfpFamily f 0) (fun _ IH => nfpFamily f (succ IH))
    fun a _ g => ⨆ b : Set.Iio a, g _ b.2

@[simp]
/--
theorem `derivFamily_zero` / 定理 `derivFamily_zero`

English:
theorem derivFamily_zero
  given: (f : ι -> Ordinal -> Ordinal)
  proof: limitRecOn_zero ..

@[simp]

中文:
定理 derivFamily_zero
  条件: (f : ι -> Ordinal -> Ordinal)
  证明: limitRecOn_zero ..

@[simp]

Depends on / 依赖: limitRecOn_zero
-/
theorem derivFamily_zero (f : ι -> Ordinal -> Ordinal) :
    derivFamily f 0 = nfpFamily f 0 :=
  limitRecOn_zero ..

@[simp]
/--
theorem `derivFamily_add_one` / 定理 `derivFamily_add_one`

English:
theorem derivFamily_add_one
  given: (f : ι -> Ordinal -> Ordinal) (o)
  proof: limitRecOn_add_one ..

中文:
定理 derivFamily_add_one
  条件: (f : ι -> Ordinal -> Ordinal) (o)
  证明: limitRecOn_add_one ..

Depends on / 依赖: limitRecOn_add_one
-/
theorem derivFamily_add_one (f : ι -> Ordinal -> Ordinal) (o) :
    derivFamily f (o + 1) = nfpFamily f (derivFamily f o + 1) :=
  limitRecOn_add_one ..

-- TODO: deprecate
/--
theorem `derivFamily_succ` / 定理 `derivFamily_succ`

English:
theorem derivFamily_succ
  given: (f : ι -> Ordinal -> Ordinal) (o)
  proof: derivFamily_add_one f o

中文:
定理 derivFamily_succ
  条件: (f : ι -> Ordinal -> Ordinal) (o)
  证明: derivFamily_add_one f o

Depends on / 依赖: derivFamily_add_one
-/
theorem derivFamily_succ (f : ι -> Ordinal -> Ordinal) (o) :
    derivFamily f (succ o) = nfpFamily f (succ (derivFamily f o)) :=
  derivFamily_add_one f o

/--
theorem `derivFamily_limit` / 定理 `derivFamily_limit`

English:
theorem derivFamily_limit
  given: (f : ι -> Ordinal -> Ordinal) {o}
  proof: limitRecOn_limit _ _ _ _

中文:
定理 derivFamily_limit
  条件: (f : ι -> Ordinal -> Ordinal) {o}
  证明: limitRecOn_limit _ _ _ _

Depends on / 依赖: limitRecOn_limit
-/
theorem derivFamily_limit (f : ι -> Ordinal -> Ordinal) {o} :
    IsSuccLimit o -> derivFamily f o = ⨆ b : Set.Iio o, derivFamily f b :=
  limitRecOn_limit _ _ _ _

/--
theorem `isNormal_derivFamily` / 定理 `isNormal_derivFamily`

English:
theorem isNormal_derivFamily
  given: [Small.{u} ι] (f : ι -> Ordinal.{u} -> Ordinal.{u})
  proof: by
  refine IsNormal.of_succ_lt (fun o => ?_) @fun o h => ?_
  · rw [derivFamily_succ, ← succ_le_iff]
    exact le_nfpFamily _ _
  · rw [derivFamily_limit _ h, Set.image_eq_range]
    have := h.nonempty_Iio.to_subtype
    exact isLUB_ciSup bddAbove_of_small

中文:
定理 isNormal_derivFamily
  条件: [Small.{u} ι] (f : ι -> Ordinal.{u} -> Ordinal.{u})
  证明: by
  refine IsNormal.of_succ_lt (fun o => ?_) @fun o h => ?_
  · rw [derivFamily_succ, ← succ_le_iff]
    exact le_nfpFamily _ _
  · rw [derivFamily_limit _ h, Set.image_eq_range]
    have := h.nonempty_Iio.to_subtype
    exact isLUB_ciSup bddAbove_of_small

Depends on / 依赖: IsNormal, IsNormal.of_succ_lt, Set.image_eq_range, bddAbove_of_small, derivFamily_limit, derivFamily_succ, h.nonempty_Iio.to_subtype, image_eq_range, isLUB_ciSup, le_nfpFamily, nonempty_Iio, of_succ_lt, succ_le_iff, to_subtype
-/
theorem isNormal_derivFamily [Small.{u} ι] (f : ι -> Ordinal.{u} -> Ordinal.{u}) :
    IsNormal (derivFamily f) := by
  refine IsNormal.of_succ_lt (fun o => ?_) @fun o h => ?_
  · rw [derivFamily_succ, ← succ_le_iff]
    exact le_nfpFamily _ _
  · rw [derivFamily_limit _ h, Set.image_eq_range]
    have := h.nonempty_Iio.to_subtype
    exact isLUB_ciSup bddAbove_of_small

/--
theorem `derivFamily_strictMono` / 定理 `derivFamily_strictMono`

English:
theorem derivFamily_strictMono
  given: [Small.{u} ι] (f : ι -> Ordinal.{u} -> Ordinal.{u})
  proof: (isNormal_derivFamily f).strictMono

中文:
定理 derivFamily_strictMono
  条件: [Small.{u} ι] (f : ι -> Ordinal.{u} -> Ordinal.{u})
  证明: (isNormal_derivFamily f).strictMono

Depends on / 依赖: isNormal_derivFamily, strictMono
-/
theorem derivFamily_strictMono [Small.{u} ι] (f : ι -> Ordinal.{u} -> Ordinal.{u}) :
    StrictMono (derivFamily f) :=
  (isNormal_derivFamily f).strictMono

/--
theorem `derivFamily_fp` / 定理 `derivFamily_fp`

English:
theorem derivFamily_fp
  given: [Small.{u} ι] {i} (H : IsNormal (f i)) (o : Ordinal)
  proof: by
  induction o using limitRecOn with
  | zero =>
    rw [derivFamily_zero]
    exact nfpFamily_fp H 0
  | add_one =>
    rw [derivFamily_add_one]
    exact nfpFamily_fp H _
  | limit o l IH =>
    have := l.nonempty_Iio.to_subtype
    rw [derivFamily_limit _ l]; rw [H.map_iSup bddAbove_of_small]
 

中文:
定理 derivFamily_fp
  条件: [Small.{u} ι] {i} (H : IsNormal (f i)) (o : Ordinal)
  证明: by
  induction o using limitRecOn with
  | zero =>
    rw [derivFamily_zero]
    exact nfpFamily_fp H 0
  | add_one =>
    rw [derivFamily_add_one]
    exact nfpFamily_fp H _
  | limit o l IH =>
    have := l.nonempty_Iio.to_subtype
    rw [derivFamily_limit _ l]; rw [H.map_iSup bddAbove_of_small]
 

Depends on / 依赖: H.map_iSup, Ordinal, Ordinal.iSup_le_iff, add_one, bddAbove_of_small, derivFamily_add_one, derivFamily_limit, derivFamily_zero, eq_of_forall_ge_iff, forall_congr, iSup_le_iff, l.nonempty_Iio.to_subtype, limitRecOn, map_iSup, nfpFamily_fp, nonempty_Iio, to_subtype
-/
theorem derivFamily_fp [Small.{u} ι] {i} (H : IsNormal (f i)) (o : Ordinal) :
    f i (derivFamily f o) = derivFamily f o := by
  induction o using limitRecOn with
  | zero =>
    rw [derivFamily_zero]
    exact nfpFamily_fp H 0
  | add_one =>
    rw [derivFamily_add_one]
    exact nfpFamily_fp H _
  | limit o l IH =>
    have := l.nonempty_Iio.to_subtype
    rw [derivFamily_limit _ l]; rw [H.map_iSup bddAbove_of_small]
    refine eq_of_forall_ge_iff fun c => ?_
    rw [Ordinal.iSup_le_iff]; rw [Ordinal.iSup_le_iff]
    refine forall_congr' fun a => ?_
    rw [IH _ a.2]

/--
theorem `le_iff_derivFamily` / 定理 `le_iff_derivFamily`

English:
theorem le_iff_derivFamily
  given: [Small.{u} ι] (H : forall i, IsNormal (f i)) {a}
  proof: ⟨fun ha => by
    suffices forall (o), a <= derivFamily f o -> exists o, derivFamily f o = a from
      this a (isNormal_derivFamily _).strictMono.le_apply
    intro o
    induction o using limitRecOn with
    | zero =>
      intro h₁
      refine ⟨0, le_antisymm ?_ h₁⟩
      rw [derivFamily_zero]
 

中文:
定理 le_iff_derivFamily
  条件: [Small.{u} ι] (H : 对任意 i, IsNormal (f i)) {a}
  证明: ⟨fun ha => by
    suffices forall (o), a <= derivFamily f o -> exists o, derivFamily f o = a from
      this a (isNormal_derivFamily _).strictMono.le_apply
    intro o
    induction o using limitRecOn with
    | zero =>
      intro h₁
      refine ⟨0, le_antisymm ?_ h₁⟩
      rw [derivFamily_zero]
 

Depends on / 依赖: add_one, derivFamily, derivFamily_add_one, derivFamily_zero, isNormal_derivFamily, le_antisymm, le_apply, le_or_gt, limitRecOn, monotone, nfpFamily_le_fp, strictMono, strictMono.le_apply, zero_le
-/
theorem le_iff_derivFamily [Small.{u} ι] (H : forall i, IsNormal (f i)) {a} :
    (forall i, f i a <= a) ↔ exists o, derivFamily f o = a :=
  ⟨fun ha => by
    suffices forall (o), a <= derivFamily f o -> exists o, derivFamily f o = a from
      this a (isNormal_derivFamily _).strictMono.le_apply
    intro o
    induction o using limitRecOn with
    | zero =>
      intro h₁
      refine ⟨0, le_antisymm ?_ h₁⟩
      rw [derivFamily_zero]
      exact nfpFamily_le_fp (fun i => (H i).monotone) zero_le ha
    | add_one o IH =>
      intro h₁
      rcases le_or_gt a (derivFamily f o) with h | h
      · exact IH h
      refine ⟨o + 1, le_antisymm ?_ h₁⟩
      rw [derivFamily_add_one]
      exact nfpFamily_le_fp (fun i => (H i).monotone) (succ_le_of_lt h) ha
    | limit o l IH =>
      intro h₁
      rcases eq_or_lt_of_le h₁ with h | h
      · exact ⟨_, h.symm⟩
      rw [derivFamily_limit _ l]; rw [← not_le]; rw [Ordinal.iSup_le_iff]; rw [not_forall] at h
      obtain ⟨o', h⟩ := h
      exact IH o' o'.2 (le_of_not_ge h),
    fun ⟨_, e⟩ i => e ▸ (derivFamily_fp (H i) _).le⟩

/--
theorem `fp_iff_derivFamily` / 定理 `fp_iff_derivFamily`

English:
theorem fp_iff_derivFamily
  given: [Small.{u} ι] (H : forall i, IsNormal (f i)) {a}
  proof: Iff.trans ⟨fun h i => le_of_eq (h i), fun h i => (H i).strictMono.le_apply.ge_iff_eq'.1 (h i)⟩
    (le_iff_derivFamily H)

中文:
定理 fp_iff_derivFamily
  条件: [Small.{u} ι] (H : 对任意 i, IsNormal (f i)) {a}
  证明: Iff.trans ⟨fun h i => le_of_eq (h i), fun h i => (H i).strictMono.le_apply.ge_iff_eq'.1 (h i)⟩
    (le_iff_derivFamily H)

Depends on / 依赖: Iff.trans, ge_iff_eq, le_apply, le_iff_derivFamily, le_of_eq, strictMono, strictMono.le_apply.ge_iff_eq
-/
theorem fp_iff_derivFamily [Small.{u} ι] (H : forall i, IsNormal (f i)) {a} :
    (forall i, f i a = a) ↔ exists o, derivFamily f o = a :=
  Iff.trans ⟨fun h i => le_of_eq (h i), fun h i => (H i).strictMono.le_apply.ge_iff_eq'.1 (h i)⟩
    (le_iff_derivFamily H)

/--
theorem `mem_range_derivFamily` / 定理 `mem_range_derivFamily`

English:
theorem mem_range_derivFamily
  given: [Small.{u} ι] (H : forall i, IsNormal (f i)) {a}
  proof: (fp_iff_derivFamily H).symm

中文:
定理 mem_range_derivFamily
  条件: [Small.{u} ι] (H : 对任意 i, IsNormal (f i)) {a}
  证明: (fp_iff_derivFamily H).symm

Depends on / 依赖: fp_iff_derivFamily
-/
theorem mem_range_derivFamily [Small.{u} ι] (H : forall i, IsNormal (f i)) {a} :
    a in Set.range (derivFamily f) ↔ forall i, f i a = a :=
  (fp_iff_derivFamily H).symm

/--
theorem `derivFamily_eq_enumOrd` / 定理 `derivFamily_eq_enumOrd`

English:
theorem derivFamily_eq_enumOrd
  given: [Small.{u} ι] (H : forall i, IsNormal (f i))
  proof: by
  rw [eq_comm]; rw [eq_enumOrd _ (not_bddAbove_fp_family H)]
  use (isNormal_derivFamily f).strictMono
  rw [Set.range_eq_iff]
  refine ⟨?_, fun a ha => ?_⟩
  · rintro a S ⟨i, hi⟩
    rw [← hi]
    exact derivFamily_fp (H i) a
  rw [Set.mem_iInter] at ha
  rwa [← fp_iff_derivFamily H]

中文:
定理 derivFamily_eq_enumOrd
  条件: [Small.{u} ι] (H : 对任意 i, IsNormal (f i))
  证明: by
  rw [eq_comm]; rw [eq_enumOrd _ (not_bddAbove_fp_family H)]
  use (isNormal_derivFamily f).strictMono
  rw [Set.range_eq_iff]
  refine ⟨?_, fun a ha => ?_⟩
  · rintro a S ⟨i, hi⟩
    rw [← hi]
    exact derivFamily_fp (H i) a
  rw [Set.mem_iInter] at ha
  rwa [← fp_iff_derivFamily H]

Depends on / 依赖: Set.mem_iInter, Set.range_eq_iff, derivFamily_fp, eq_comm, eq_enumOrd, fp_iff_derivFamily, isNormal_derivFamily, mem_iInter, not_bddAbove_fp_family, range_eq_iff, strictMono
-/
theorem derivFamily_eq_enumOrd [Small.{u} ι] (H : forall i, IsNormal (f i)) :
    derivFamily f = enumOrd (⋂ i, Function.fixedPoints (f i)) := by
  rw [eq_comm]; rw [eq_enumOrd _ (not_bddAbove_fp_family H)]
  use (isNormal_derivFamily f).strictMono
  rw [Set.range_eq_iff]
  refine ⟨?_, fun a ha => ?_⟩
  · rintro a S ⟨i, hi⟩
    rw [← hi]
    exact derivFamily_fp (H i) a
  rw [Set.mem_iInter] at ha
  rwa [← fp_iff_derivFamily H]

end

/-! ### Fixed points of a single function -/

section

variable {f : Ordinal.{u} -> Ordinal.{u}}

/--
Definition of `nfp` / `nfp` 的定义

English:
definition nfp
  signature: (f : Ordinal -> Ordinal)
  body: nfpFamily fun _ : Unit => f

中文:
定义 nfp
  签名: (f : Ordinal -> Ordinal)
  定义体: nfpFamily fun _ : Unit => f

Depends on / 依赖: nfpFamily
-/
def nfp (f : Ordinal -> Ordinal) : Ordinal -> Ordinal :=
  nfpFamily fun _ : Unit => f

/--
theorem `nfp_eq_nfpFamily` / 定理 `nfp_eq_nfpFamily`

English:
theorem nfp_eq_nfpFamily
  given: (f : Ordinal -> Ordinal)
  statement: nfp f = nfpFamily fun _ : Unit => f
  proof: rfl

中文:
定理 nfp_eq_nfpFamily
  条件: (f : Ordinal -> Ordinal)
  结论: nfp f = nfpFamily fun _ : Unit => f
  证明: rfl
-/
theorem nfp_eq_nfpFamily (f : Ordinal -> Ordinal) : nfp f = nfpFamily fun _ : Unit => f :=
  rfl

/--
theorem `iSup_iterate_eq_nfp` / 定理 `iSup_iterate_eq_nfp`

English:
theorem iSup_iterate_eq_nfp
  given: (f : Ordinal.{u} -> Ordinal.{u}) (a : Ordinal.{u})
  proof: by
  apply le_antisymm
  · rw [Ordinal.iSup_le_iff]
    intro n
    rw [← List.length_replicate (n := n) (a := Unit.unit)]; rw [← List.foldr_const f a]
    exact Ordinal.le_iSup _ _
  · apply Ordinal.iSup_le
    intro l
    rw [List.foldr_const f a l]
    exact Ordinal.le_iSup _ _

中文:
定理 iSup_iterate_eq_nfp
  条件: (f : Ordinal.{u} -> Ordinal.{u}) (a : Ordinal.{u})
  证明: by
  apply le_antisymm
  · rw [Ordinal.iSup_le_iff]
    intro n
    rw [← List.length_replicate (n := n) (a := Unit.unit)]; rw [← List.foldr_const f a]
    exact Ordinal.le_iSup _ _
  · apply Ordinal.iSup_le
    intro l
    rw [List.foldr_const f a l]
    exact Ordinal.le_iSup _ _

Depends on / 依赖: List.foldr_const, List.length_replicate, Ordinal, Ordinal.iSup_le, Ordinal.iSup_le_iff, Ordinal.le_iSup, Unit.unit, foldr_const, iSup_le, iSup_le_iff, le_antisymm, le_iSup, length_replicate
-/
theorem iSup_iterate_eq_nfp (f : Ordinal.{u} -> Ordinal.{u}) (a : Ordinal.{u}) :
    ⨆ n : Nat, f^[n] a = nfp f a := by
  apply le_antisymm
  · rw [Ordinal.iSup_le_iff]
    intro n
    rw [← List.length_replicate (n := n) (a := Unit.unit)]; rw [← List.foldr_const f a]
    exact Ordinal.le_iSup _ _
  · apply Ordinal.iSup_le
    intro l
    rw [List.foldr_const f a l]
    exact Ordinal.le_iSup _ _

/--
theorem `iterate_le_nfp` / 定理 `iterate_le_nfp`

English:
theorem iterate_le_nfp
  given: (f a n)
  statement: f^[n] a <= nfp f a
  proof: by
  rw [← iSup_iterate_eq_nfp]
  exact Ordinal.le_iSup (fun n => f^[n] a) n

中文:
定理 iterate_le_nfp
  条件: (f a n)
  结论: f^[n] a <= nfp f a
  证明: by
  rw [← iSup_iterate_eq_nfp]
  exact Ordinal.le_iSup (fun n => f^[n] a) n

Depends on / 依赖: Ordinal, Ordinal.le_iSup, iSup_iterate_eq_nfp, le_iSup
-/
theorem iterate_le_nfp (f a n) : f^[n] a <= nfp f a := by
  rw [← iSup_iterate_eq_nfp]
  exact Ordinal.le_iSup (fun n => f^[n] a) n

/--
theorem `le_nfp` / 定理 `le_nfp`

English:
theorem le_nfp
  given: (f a)
  statement: a <= nfp f a
  proof: iterate_le_nfp f a 0

中文:
定理 le_nfp
  条件: (f a)
  结论: a <= nfp f a
  证明: iterate_le_nfp f a 0

Depends on / 依赖: iterate_le_nfp
-/
theorem le_nfp (f a) : a <= nfp f a :=
  iterate_le_nfp f a 0

/--
theorem `lt_nfp_iff` / 定理 `lt_nfp_iff`

English:
theorem lt_nfp_iff
  given: {a b}
  statement: a < nfp f b ↔ exists n, a < f^[n] b
  proof: by
  rw [← iSup_iterate_eq_nfp]
  exact Ordinal.lt_iSup_iff

中文:
定理 lt_nfp_iff
  条件: {a b}
  结论: a < nfp f b ↔ 存在 n, a < f^[n] b
  证明: by
  rw [← iSup_iterate_eq_nfp]
  exact Ordinal.lt_iSup_iff

Depends on / 依赖: Ordinal, Ordinal.lt_iSup_iff, iSup_iterate_eq_nfp, lt_iSup_iff
-/
theorem lt_nfp_iff {a b} : a < nfp f b ↔ exists n, a < f^[n] b := by
  rw [← iSup_iterate_eq_nfp]
  exact Ordinal.lt_iSup_iff

/--
theorem `nfp_le_iff` / 定理 `nfp_le_iff`

English:
theorem nfp_le_iff
  given: {a b}
  statement: nfp f a <= b ↔ forall n, f^[n] a <= b
  proof: by
  rw [← iSup_iterate_eq_nfp]
  exact Ordinal.iSup_le_iff

中文:
定理 nfp_le_iff
  条件: {a b}
  结论: nfp f a <= b ↔ 对任意 n, f^[n] a <= b
  证明: by
  rw [← iSup_iterate_eq_nfp]
  exact Ordinal.iSup_le_iff

Depends on / 依赖: Ordinal, Ordinal.iSup_le_iff, iSup_iterate_eq_nfp, iSup_le_iff
-/
theorem nfp_le_iff {a b} : nfp f a <= b ↔ forall n, f^[n] a <= b := by
  rw [← iSup_iterate_eq_nfp]
  exact Ordinal.iSup_le_iff

/--
theorem `nfp_le` / 定理 `nfp_le`

English:
theorem nfp_le
  given: {a b}
  statement: (forall n, f^[n] a <= b) -> nfp f a <= b
  proof: nfp_le_iff.2

@[simp]

中文:
定理 nfp_le
  条件: {a b}
  结论: (对任意 n, f^[n] a <= b) -> nfp f a <= b
  证明: nfp_le_iff.2

@[simp]

Depends on / 依赖: nfp_le_iff
-/
theorem nfp_le {a b} : (forall n, f^[n] a <= b) -> nfp f a <= b :=
  nfp_le_iff.2

@[simp]
/--
theorem `nfp_id` / 定理 `nfp_id`

English:
theorem nfp_id
  statement: nfp id = id
  proof: by
  ext
  simp_rw [← iSup_iterate_eq_nfp, iterate_id]
  exact ciSup_const

中文:
定理 nfp_id
  结论: nfp id = id
  证明: by
  ext
  simp_rw [← iSup_iterate_eq_nfp, iterate_id]
  exact ciSup_const

Depends on / 依赖: ciSup_const, iSup_iterate_eq_nfp, iterate_id, simp_rw
-/
theorem nfp_id : nfp id = id := by
  ext
  simp_rw [← iSup_iterate_eq_nfp, iterate_id]
  exact ciSup_const

/--
theorem `nfp_monotone` / 定理 `nfp_monotone`

English:
theorem nfp_monotone
  given: (hf : Monotone f)
  statement: Monotone (nfp f)
  proof: nfpFamily_monotone fun _ => hf

中文:
定理 nfp_monotone
  条件: (hf : Monotone f)
  结论: Monotone (nfp f)
  证明: nfpFamily_monotone fun _ => hf

Depends on / 依赖: nfpFamily_monotone
-/
theorem nfp_monotone (hf : Monotone f) : Monotone (nfp f) :=
  nfpFamily_monotone fun _ => hf

/--
theorem `iterate_lt_nfp` / 定理 `iterate_lt_nfp`

English:
theorem iterate_lt_nfp
  given: (hf : StrictMono f) {a} (h : a < f a) (n : Nat)
  statement: f^[n] a < nfp f a
  proof: by
  apply (hf.iterate n h).trans_le
  rw [← iterate_succ_apply]
  exact iterate_le_nfp ..

中文:
定理 iterate_lt_nfp
  条件: (hf : StrictMono f) {a} (h : a < f a) (n : 自然数)
  结论: f^[n] a < nfp f a
  证明: by
  apply (hf.iterate n h).trans_le
  rw [← iterate_succ_apply]
  exact iterate_le_nfp ..

Depends on / 依赖: hf.iterate, iterate, iterate_le_nfp, iterate_succ_apply, trans_le
-/
theorem iterate_lt_nfp (hf : StrictMono f) {a} (h : a < f a) (n : Nat) : f^[n] a < nfp f a := by
  apply (hf.iterate n h).trans_le
  rw [← iterate_succ_apply]
  exact iterate_le_nfp ..

/--
theorem `apply_lt_nfp` / 定理 `apply_lt_nfp`

English:
theorem apply_lt_nfp
  given: (H : IsNormal f) {a b}
  statement: f b < nfp f a ↔ b < nfp f a
  proof: by
  unfold nfp
  rw [← @apply_lt_nfpFamily_iff Unit (fun _ => f) _ _ (fun _ => H) a b]
  exact ⟨fun h _ => h, fun h => h Unit.unit⟩

中文:
定理 apply_lt_nfp
  条件: (H : IsNormal f) {a b}
  结论: f b < nfp f a ↔ b < nfp f a
  证明: by
  unfold nfp
  rw [← @apply_lt_nfpFamily_iff Unit (fun _ => f) _ _ (fun _ => H) a b]
  exact ⟨fun h _ => h, fun h => h Unit.unit⟩

Depends on / 依赖: Unit.unit, apply_lt_nfpFamily_iff
-/
theorem apply_lt_nfp (H : IsNormal f) {a b} : f b < nfp f a ↔ b < nfp f a := by
  unfold nfp
  rw [← @apply_lt_nfpFamily_iff Unit (fun _ => f) _ _ (fun _ => H) a b]
  exact ⟨fun h _ => h, fun h => h Unit.unit⟩

/--
theorem `nfp_le_apply` / 定理 `nfp_le_apply`

English:
theorem nfp_le_apply
  given: (H : IsNormal f) {a b}
  statement: nfp f a <= f b ↔ nfp f a <= b
  proof: le_iff_le_iff_lt_iff_lt.2 (apply_lt_nfp H)

中文:
定理 nfp_le_apply
  条件: (H : IsNormal f) {a b}
  结论: nfp f a <= f b ↔ nfp f a <= b
  证明: le_iff_le_iff_lt_iff_lt.2 (apply_lt_nfp H)

Depends on / 依赖: apply_lt_nfp, le_iff_le_iff_lt_iff_lt
-/
theorem nfp_le_apply (H : IsNormal f) {a b} : nfp f a <= f b ↔ nfp f a <= b :=
  le_iff_le_iff_lt_iff_lt.2 (apply_lt_nfp H)

/--
theorem `nfp_le_fp` / 定理 `nfp_le_fp`

English:
theorem nfp_le_fp
  given: (H : Monotone f) {a b} (ab : a <= b) (h : f b <= b)
  statement: nfp f a <= b
  proof: nfpFamily_le_fp (fun _ => H) ab fun _ => h

中文:
定理 nfp_le_fp
  条件: (H : Monotone f) {a b} (ab : a <= b) (h : f b <= b)
  结论: nfp f a <= b
  证明: nfpFamily_le_fp (fun _ => H) ab fun _ => h

Depends on / 依赖: nfpFamily_le_fp
-/
theorem nfp_le_fp (H : Monotone f) {a b} (ab : a <= b) (h : f b <= b) : nfp f a <= b :=
  nfpFamily_le_fp (fun _ => H) ab fun _ => h

/--
theorem `nfp_fp` / 定理 `nfp_fp`

English:
theorem nfp_fp
  given: (H : IsNormal f)
  statement: forall a, f (nfp f a) = nfp f a
  proof: @nfpFamily_fp Unit (fun _ => f) _ () H

中文:
定理 nfp_fp
  条件: (H : IsNormal f)
  结论: 对任意 a, f (nfp f a) = nfp f a
  证明: @nfpFamily_fp Unit (fun _ => f) _ () H

Depends on / 依赖: nfpFamily_fp
-/
theorem nfp_fp (H : IsNormal f) : forall a, f (nfp f a) = nfp f a :=
  @nfpFamily_fp Unit (fun _ => f) _ () H

/--
theorem `apply_le_nfp` / 定理 `apply_le_nfp`

English:
theorem apply_le_nfp
  given: (H : IsNormal f) {a b}
  statement: f b <= nfp f a ↔ b <= nfp f a
  proof: ⟨H.strictMono.le_apply.trans, fun h => by simpa only [nfp_fp H] using H.monotone h⟩

中文:
定理 apply_le_nfp
  条件: (H : IsNormal f) {a b}
  结论: f b <= nfp f a ↔ b <= nfp f a
  证明: ⟨H.strictMono.le_apply.trans, fun h => by simpa only [nfp_fp H] using H.monotone h⟩

Depends on / 依赖: H.monotone, H.strictMono.le_apply.trans, le_apply, monotone, nfp_fp, strictMono
-/
theorem apply_le_nfp (H : IsNormal f) {a b} : f b <= nfp f a ↔ b <= nfp f a :=
  ⟨H.strictMono.le_apply.trans, fun h => by simpa only [nfp_fp H] using H.monotone h⟩

/--
theorem `nfp_eq_self` / 定理 `nfp_eq_self`

English:
theorem nfp_eq_self
  given: {a} (h : f a = a)
  statement: nfp f a = a
  proof: nfpFamily_eq_self fun _ => h

中文:
定理 nfp_eq_self
  条件: {a} (h : f a = a)
  结论: nfp f a = a
  证明: nfpFamily_eq_self fun _ => h

Depends on / 依赖: nfpFamily_eq_self
-/
theorem nfp_eq_self {a} (h : f a = a) : nfp f a = a :=
  nfpFamily_eq_self fun _ => h

/--
theorem `not_bddAbove_fp` / 定理 `not_bddAbove_fp`

English:
theorem not_bddAbove_fp
  given: (H : IsNormal f)
  statement: ¬ BddAbove (Function.fixedPoints f)
  proof: by
  convert! not_bddAbove_fp_family fun _ : Unit => H
  exact (Set.iInter_const _).symm

中文:
定理 not_bddAbove_fp
  条件: (H : IsNormal f)
  结论: ¬ BddAbove (Function.fixedPoints f)
  证明: by
  convert! not_bddAbove_fp_family fun _ : Unit => H
  exact (Set.iInter_const _).symm

Depends on / 依赖: Set.iInter_const, convert, iInter_const, not_bddAbove_fp_family
-/
theorem not_bddAbove_fp (H : IsNormal f) : ¬ BddAbove (Function.fixedPoints f) := by
  convert! not_bddAbove_fp_family fun _ : Unit => H
  exact (Set.iInter_const _).symm

/--
Definition of `deriv` / `deriv` 的定义

English:
definition deriv
  signature: (f : Ordinal -> Ordinal)
  body: derivFamily fun _ : Unit => f

中文:
定义 deriv
  签名: (f : Ordinal -> Ordinal)
  定义体: derivFamily fun _ : Unit => f

Depends on / 依赖: derivFamily
-/
def deriv (f : Ordinal -> Ordinal) : Ordinal -> Ordinal :=
  derivFamily fun _ : Unit => f

/--
theorem `deriv_eq_derivFamily` / 定理 `deriv_eq_derivFamily`

English:
theorem deriv_eq_derivFamily
  given: (f : Ordinal -> Ordinal)
  statement: deriv f = derivFamily fun _ : Unit => f
  proof: rfl

中文:
定理 deriv_eq_derivFamily
  条件: (f : Ordinal -> Ordinal)
  结论: deriv f = derivFamily fun _ : Unit => f
  证明: rfl
-/
theorem deriv_eq_derivFamily (f : Ordinal -> Ordinal) : deriv f = derivFamily fun _ : Unit => f :=
  rfl

-- TODO: rename to `deriv_zero` once the name is available
@[simp]
/--
theorem `deriv_zero_right` / 定理 `deriv_zero_right`

English:
theorem deriv_zero_right
  given: (f)
  statement: deriv f 0 = nfp f 0
  proof: derivFamily_zero _

@[simp]

中文:
定理 deriv_zero_right
  条件: (f)
  结论: deriv f 0 = nfp f 0
  证明: derivFamily_zero _

@[simp]

Depends on / 依赖: derivFamily_zero
-/
theorem deriv_zero_right (f) : deriv f 0 = nfp f 0 :=
  derivFamily_zero _

@[simp]
/--
theorem `deriv_add_one` / 定理 `deriv_add_one`

English:
theorem deriv_add_one
  given: (f o)
  statement: deriv f (o + 1) = nfp f (deriv f o + 1)
  proof: derivFamily_succ _ _

中文:
定理 deriv_add_one
  条件: (f o)
  结论: deriv f (o + 1) = nfp f (deriv f o + 1)
  证明: derivFamily_succ _ _

Depends on / 依赖: derivFamily_succ
-/
theorem deriv_add_one (f o) : deriv f (o + 1) = nfp f (deriv f o + 1) :=
  derivFamily_succ _ _

-- TODO: deprecate
/--
theorem `deriv_succ` / 定理 `deriv_succ`

English:
theorem deriv_succ
  given: (f o)
  statement: deriv f (succ o) = nfp f (succ (deriv f o))
  proof: deriv_add_one ..

中文:
定理 deriv_succ
  条件: (f o)
  结论: deriv f (succ o) = nfp f (succ (deriv f o))
  证明: deriv_add_one ..

Depends on / 依赖: deriv_add_one
-/
theorem deriv_succ (f o) : deriv f (succ o) = nfp f (succ (deriv f o)) :=
  deriv_add_one ..

/--
theorem `deriv_limit` / 定理 `deriv_limit`

English:
theorem deriv_limit
  given: (f) {o}
  statement: IsSuccLimit o -> deriv f o = ⨆ a : {a // a < o}, deriv f a
  proof: derivFamily_limit _

中文:
定理 deriv_limit
  条件: (f) {o}
  结论: IsSuccLimit o -> deriv f o = ⨆ a : {a // a < o}, deriv f a
  证明: derivFamily_limit _

Depends on / 依赖: derivFamily_limit
-/
theorem deriv_limit (f) {o} : IsSuccLimit o -> deriv f o = ⨆ a : {a // a < o}, deriv f a :=
  derivFamily_limit _

/--
theorem `isNormal_deriv` / 定理 `isNormal_deriv`

English:
theorem isNormal_deriv
  given: (f)
  statement: IsNormal (deriv f)
  proof: isNormal_derivFamily _

中文:
定理 isNormal_deriv
  条件: (f)
  结论: IsNormal (deriv f)
  证明: isNormal_derivFamily _

Depends on / 依赖: isNormal_derivFamily
-/
theorem isNormal_deriv (f) : IsNormal (deriv f) :=
  isNormal_derivFamily _

/--
theorem `deriv_strictMono` / 定理 `deriv_strictMono`

English:
theorem deriv_strictMono
  given: (f)
  statement: StrictMono (deriv f)
  proof: derivFamily_strictMono _

@[deprecated "do not depend on the junk values of `nfp`" (since := "2026-05-13")]

中文:
定理 deriv_strictMono
  条件: (f)
  结论: StrictMono (deriv f)
  证明: derivFamily_strictMono _

@[deprecated "do not depend on the junk values of `nfp`" (since := "2026-05-13")]

Depends on / 依赖: derivFamily_strictMono
-/
theorem deriv_strictMono (f) : StrictMono (deriv f) :=
  derivFamily_strictMono _

@[deprecated "do not depend on the junk values of `nfp`" (since := "2026-05-13")]
/--
theorem `deriv_eq_id_of_nfp_eq_id` / 定理 `deriv_eq_id_of_nfp_eq_id`

English:
theorem deriv_eq_id_of_nfp_eq_id
  given: (h : nfp f = id)
  statement: deriv f = id
  proof: ((isNormal_deriv _).ext_iff .id).2 (by simp [h])

中文:
定理 deriv_eq_id_of_nfp_eq_id
  条件: (h : nfp f = id)
  结论: deriv f = id
  证明: ((isNormal_deriv _).ext_iff .id).2 (by simp [h])

Depends on / 依赖: ext_iff, isNormal_deriv
-/
theorem deriv_eq_id_of_nfp_eq_id (h : nfp f = id) : deriv f = id :=
  ((isNormal_deriv _).ext_iff .id).2 (by simp [h])

/--
theorem `deriv_fp` / 定理 `deriv_fp`

English:
theorem deriv_fp
  given: (H : IsNormal f)
  statement: forall o, f (deriv f o) = deriv f o
  proof: derivFamily_fp (i := ⟨⟩) H

中文:
定理 deriv_fp
  条件: (H : IsNormal f)
  结论: 对任意 o, f (deriv f o) = deriv f o
  证明: derivFamily_fp (i := ⟨⟩) H

Depends on / 依赖: derivFamily_fp
-/
theorem deriv_fp (H : IsNormal f) : forall o, f (deriv f o) = deriv f o :=
  derivFamily_fp (i := ⟨⟩) H

/--
theorem `le_iff_deriv` / 定理 `le_iff_deriv`

English:
theorem le_iff_deriv
  given: (H : IsNormal f) {a}
  statement: f a <= a ↔ exists o, deriv f o = a
  proof: by
  unfold deriv
  rw [← le_iff_derivFamily fun _ : Unit => H]
  exact ⟨fun h _ => h, fun h => h Unit.unit⟩

中文:
定理 le_iff_deriv
  条件: (H : IsNormal f) {a}
  结论: f a <= a ↔ 存在 o, deriv f o = a
  证明: by
  unfold deriv
  rw [← le_iff_derivFamily fun _ : Unit => H]
  exact ⟨fun h _ => h, fun h => h Unit.unit⟩

Depends on / 依赖: Unit.unit, le_iff_derivFamily
-/
theorem le_iff_deriv (H : IsNormal f) {a} : f a <= a ↔ exists o, deriv f o = a := by
  unfold deriv
  rw [← le_iff_derivFamily fun _ : Unit => H]
  exact ⟨fun h _ => h, fun h => h Unit.unit⟩

/--
theorem `mem_range_deriv` / 定理 `mem_range_deriv`

English:
theorem mem_range_deriv
  given: (H : IsNormal f) {a}
  statement: a in Set.range (deriv f) ↔ f a = a
  proof: by
  rw [Set.mem_range]; rw [← H.strictMono.le_apply.ge_iff_eq']; rw [le_iff_deriv H]

中文:
定理 mem_range_deriv
  条件: (H : IsNormal f) {a}
  结论: a in Set.range (deriv f) ↔ f a = a
  证明: by
  rw [Set.mem_range]; rw [← H.strictMono.le_apply.ge_iff_eq']; rw [le_iff_deriv H]

Depends on / 依赖: H.strictMono.le_apply.ge_iff_eq, Set.mem_range, ge_iff_eq, le_apply, le_iff_deriv, mem_range, strictMono
-/
theorem mem_range_deriv (H : IsNormal f) {a} : a in Set.range (deriv f) ↔ f a = a := by
  rw [Set.mem_range]; rw [← H.strictMono.le_apply.ge_iff_eq']; rw [le_iff_deriv H]

/--
theorem `deriv_eq_enumOrd` / 定理 `deriv_eq_enumOrd`

English:
theorem deriv_eq_enumOrd
  given: (H : IsNormal f)
  statement: deriv f = enumOrd (Function.fixedPoints f)
  proof: by
  convert! derivFamily_eq_enumOrd fun _ : Unit => H
  exact (Set.iInter_const _).symm

@[deprecated "do not depend on the junk values of `nfp`" (since := "2026-05-13")]

中文:
定理 deriv_eq_enumOrd
  条件: (H : IsNormal f)
  结论: deriv f = enumOrd (Function.fixedPoints f)
  证明: by
  convert! derivFamily_eq_enumOrd fun _ : Unit => H
  exact (Set.iInter_const _).symm

@[deprecated "do not depend on the junk values of `nfp`" (since := "2026-05-13")]

Depends on / 依赖: Set.iInter_const, convert, derivFamily_eq_enumOrd, iInter_const
-/
theorem deriv_eq_enumOrd (H : IsNormal f) : deriv f = enumOrd (Function.fixedPoints f) := by
  convert! derivFamily_eq_enumOrd fun _ : Unit => H
  exact (Set.iInter_const _).symm

@[deprecated "do not depend on the junk values of `nfp`" (since := "2026-05-13")]
/--
theorem `nfp_zero_left` / 定理 `nfp_zero_left`

English:
theorem nfp_zero_left
  given: (a)
  statement: nfp 0 a = a
  proof: by
  rw [← iSup_iterate_eq_nfp]
  apply (Ordinal.iSup_le ?_).antisymm (Ordinal.le_iSup _ 0)
  intro n
  cases n
  · rfl
  · rw [Function.iterate_succ']
    simp

@[deprecated "do not depend on the junk values of `nfp`" (since := "2026-05-13")]

中文:
定理 nfp_zero_left
  条件: (a)
  结论: nfp 0 a = a
  证明: by
  rw [← iSup_iterate_eq_nfp]
  apply (Ordinal.iSup_le ?_).antisymm (Ordinal.le_iSup _ 0)
  intro n
  cases n
  · rfl
  · rw [Function.iterate_succ']
    simp

@[deprecated "do not depend on the junk values of `nfp`" (since := "2026-05-13")]

Depends on / 依赖: Function, Function.iterate_succ, Ordinal, Ordinal.iSup_le, Ordinal.le_iSup, antisymm, iSup_iterate_eq_nfp, iSup_le, iterate_succ, le_iSup
-/
theorem nfp_zero_left (a) : nfp 0 a = a := by
  rw [← iSup_iterate_eq_nfp]
  apply (Ordinal.iSup_le ?_).antisymm (Ordinal.le_iSup _ 0)
  intro n
  cases n
  · rfl
  · rw [Function.iterate_succ']
    simp

@[deprecated "do not depend on the junk values of `nfp`" (since := "2026-05-13")]
/--
theorem `nfp_zero` / 定理 `nfp_zero`

English:
theorem nfp_zero
  statement: nfp 0 = id
  proof: by
  ext
  exact nfp_zero_left _

@[deprecated "do not depend on the junk values of `deriv`" (since := "2026-05-13")]

中文:
定理 nfp_zero
  结论: nfp 0 = id
  证明: by
  ext
  exact nfp_zero_left _

@[deprecated "do not depend on the junk values of `deriv`" (since := "2026-05-13")]

Depends on / 依赖: nfp_zero_left
-/
theorem nfp_zero : nfp 0 = id := by
  ext
  exact nfp_zero_left _

@[deprecated "do not depend on the junk values of `deriv`" (since := "2026-05-13")]
/--
theorem `deriv_zero` / 定理 `deriv_zero`

English:
theorem deriv_zero
  statement: deriv 0 = id
  proof: deriv_eq_id_of_nfp_eq_id nfp_zero

@[deprecated "do not depend on the junk values of `deriv`" (since := "2026-05-13")]

中文:
定理 deriv_zero
  结论: deriv 0 = id
  证明: deriv_eq_id_of_nfp_eq_id nfp_zero

@[deprecated "do not depend on the junk values of `deriv`" (since := "2026-05-13")]

Depends on / 依赖: deriv_eq_id_of_nfp_eq_id, nfp_zero
-/
theorem deriv_zero : deriv 0 = id :=
  deriv_eq_id_of_nfp_eq_id nfp_zero

@[deprecated "do not depend on the junk values of `deriv`" (since := "2026-05-13")]
/--
theorem `deriv_zero_left` / 定理 `deriv_zero_left`

English:
theorem deriv_zero_left
  given: (a)
  statement: deriv 0 a = a
  proof: by
  rw [deriv_zero]; rw [id_eq]

中文:
定理 deriv_zero_left
  条件: (a)
  结论: deriv 0 a = a
  证明: by
  rw [deriv_zero]; rw [id_eq]

Depends on / 依赖: deriv_zero, id_eq
-/
theorem deriv_zero_left (a) : deriv 0 a = a := by
  rw [deriv_zero]; rw [id_eq]

end

/-! ### Fixed points of addition -/

@[simp]
/--
theorem `nfp_add_zero` / 定理 `nfp_add_zero`

English:
theorem nfp_add_zero
  given: (a)
  statement: nfp (a + ·) 0 = a * ω
  proof: by
  simp [← iSup_iterate_eq_nfp]

中文:
定理 nfp_add_zero
  条件: (a)
  结论: nfp (a + ·) 0 = a * ω
  证明: by
  simp [← iSup_iterate_eq_nfp]

Depends on / 依赖: iSup_iterate_eq_nfp
-/
theorem nfp_add_zero (a) : nfp (a + ·) 0 = a * ω := by
  simp [← iSup_iterate_eq_nfp]

/--
theorem `nfp_add_eq_mul_omega0` / 定理 `nfp_add_eq_mul_omega0`

English:
theorem nfp_add_eq_mul_omega0
  given: {a b} (hba : b <= a * ω)
  statement: nfp (a + ·) b = a * ω
  proof: by
  apply le_antisymm (nfp_le_fp (isNormal_add_right a).monotone hba _)
  · rw [← nfp_add_zero]
    exact nfp_monotone (isNormal_add_right a).monotone zero_le
  · rw [← mul_one_add, one_add_omega0]

中文:
定理 nfp_add_eq_mul_omega0
  条件: {a b} (hba : b <= a * ω)
  结论: nfp (a + ·) b = a * ω
  证明: by
  apply le_antisymm (nfp_le_fp (isNormal_add_right a).monotone hba _)
  · rw [← nfp_add_zero]
    exact nfp_monotone (isNormal_add_right a).monotone zero_le
  · rw [← mul_one_add, one_add_omega0]

Depends on / 依赖: isNormal_add_right, isometry_smul, le_antisymm, monotone, mul_one_add, nfp_add_zero, nfp_le_fp, nfp_monotone, one_add_omega0, zero_le
-/
theorem nfp_add_eq_mul_omega0 {a b} (hba : b <= a * ω) : nfp (a + ·) b = a * ω := by
  apply le_antisymm (nfp_le_fp (isNormal_add_right a).monotone hba _)
  · rw [← nfp_add_zero]
    exact nfp_monotone (isNormal_add_right a).monotone zero_le
  · rw [← mul_one_add, one_add_omega0]

/--
theorem `add_eq_right_iff_mul_omega0_le` / 定理 `add_eq_right_iff_mul_omega0_le`

English:
theorem add_eq_right_iff_mul_omega0_le
  given: {a b : Ordinal}
  statement: a + b = b ↔ a * ω <= b
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← nfp_add_zero a, ← deriv_zero_right]
    obtain ⟨c, hc⟩ := (mem_range_deriv (isNormal_add_right a)).2 h
    rw [← hc]
    exact (isNormal_deriv _).monotone zero_le
  · have := Ordinal.add_sub_cancel_of_le h
    nth_rw 1 [← this]
    rwa [← add_assoc, ←

中文:
定理 add_eq_right_iff_mul_omega0_le
  条件: {a b : Ordinal}
  结论: a + b = b ↔ a * ω <= b
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← nfp_add_zero a, ← deriv_zero_right]
    obtain ⟨c, hc⟩ := (mem_range_deriv (isNormal_add_right a)).2 h
    rw [← hc]
    exact (isNormal_deriv _).monotone zero_le
  · have := Ordinal.add_sub_cancel_of_le h
    nth_rw 1 [← this]
    rwa [← add_assoc, ←

Depends on / 依赖: Ordinal, Ordinal.add_sub_cancel_of_le, add_assoc, add_sub_cancel_of_le, deriv_zero_right, isNormal_add_right, isNormal_deriv, mem_range_deriv, monotone, mul_one_add, nfp_add_zero, nth_rw, one_add_omega0, zero_le
-/
theorem add_eq_right_iff_mul_omega0_le {a b : Ordinal} : a + b = b ↔ a * ω <= b := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← nfp_add_zero a, ← deriv_zero_right]
    obtain ⟨c, hc⟩ := (mem_range_deriv (isNormal_add_right a)).2 h
    rw [← hc]
    exact (isNormal_deriv _).monotone zero_le
  · have := Ordinal.add_sub_cancel_of_le h
    nth_rw 1 [← this]
    rwa [← add_assoc, ← mul_one_add, one_add_omega0]

/--
theorem `add_le_right_iff_mul_omega0_le` / 定理 `add_le_right_iff_mul_omega0_le`

English:
theorem add_le_right_iff_mul_omega0_le
  given: {a b : Ordinal}
  statement: a + b <= b ↔ a * ω <= b
  proof: by
  rw [← add_eq_right_iff_mul_omega0_le]
  exact (isNormal_add_right a).strictMono.le_apply.ge_iff_eq'

中文:
定理 add_le_right_iff_mul_omega0_le
  条件: {a b : Ordinal}
  结论: a + b <= b ↔ a * ω <= b
  证明: by
  rw [← add_eq_right_iff_mul_omega0_le]
  exact (isNormal_add_right a).strictMono.le_apply.ge_iff_eq'

Depends on / 依赖: add_eq_right_iff_mul_omega0_le, ge_iff_eq, isNormal_add_right, le_apply, strictMono, strictMono.le_apply.ge_iff_eq
-/
theorem add_le_right_iff_mul_omega0_le {a b : Ordinal} : a + b <= b ↔ a * ω <= b := by
  rw [← add_eq_right_iff_mul_omega0_le]
  exact (isNormal_add_right a).strictMono.le_apply.ge_iff_eq'

/--
theorem `deriv_add_eq_mul_omega0_add` / 定理 `deriv_add_eq_mul_omega0_add`

English:
theorem deriv_add_eq_mul_omega0_add
  given: (a b : Ordinal.{u})
  statement: deriv (a + ·) b = a * ω + b
  proof: by
  revert b
  rw [← funext_iff]; rw [IsNormal.ext_iff (isNormal_deriv _) (isNormal_add_right _)]
  refine ⟨?_, fun a h => ?_⟩
  · rw [bot_eq_zero, deriv_zero_right, add_zero]
    exact nfp_add_zero a
  · rw [succ_eq_add_one, deriv_add_one, h, ← add_assoc]
    exact nfp_eq_self (add_eq_right_iff_mu

中文:
定理 deriv_add_eq_mul_omega0_add
  条件: (a b : Ordinal.{u})
  结论: deriv (a + ·) b = a * ω + b
  证明: by
  revert b
  rw [← funext_iff]; rw [IsNormal.ext_iff (isNormal_deriv _) (isNormal_add_right _)]
  refine ⟨?_, fun a h => ?_⟩
  · rw [bot_eq_zero, deriv_zero_right, add_zero]
    exact nfp_add_zero a
  · rw [succ_eq_add_one, deriv_add_one, h, ← add_assoc]
    exact nfp_eq_self (add_eq_right_iff_mu

Depends on / 依赖: IsNormal, IsNormal.ext_iff, add_assoc, add_eq_right_iff_mul_omega0_le, add_zero, bot_eq_zero, deriv_add_one, deriv_zero_right, ext_iff, funext_iff, isNormal_add_right, isNormal_deriv, le_self_add, le_self_add.trans, le_succ, nfp_add_zero, nfp_eq_self, revert, succ_eq_add_one
-/
theorem deriv_add_eq_mul_omega0_add (a b : Ordinal.{u}) : deriv (a + ·) b = a * ω + b := by
  revert b
  rw [← funext_iff]; rw [IsNormal.ext_iff (isNormal_deriv _) (isNormal_add_right _)]
  refine ⟨?_, fun a h => ?_⟩
  · rw [bot_eq_zero, deriv_zero_right, add_zero]
    exact nfp_add_zero a
  · rw [succ_eq_add_one, deriv_add_one, h, ← add_assoc]
    exact nfp_eq_self (add_eq_right_iff_mul_omega0_le.2 (le_self_add.trans (le_succ _)))

/-! ### Fixed points of multiplication -/

@[simp]
/--
theorem `nfp_mul_one` / 定理 `nfp_mul_one`

English:
theorem nfp_mul_one
  given: {a : Ordinal} (ha : 0 < a)
  statement: nfp (a * ·) 1 = a ^ ω
  proof: by
  rw [← iSup_iterate_eq_nfp]; rw [← iSup_pow_natCast ha]
  simp

@[simp]

中文:
定理 nfp_mul_one
  条件: {a : Ordinal} (ha : 0 < a)
  结论: nfp (a * ·) 1 = a ^ ω
  证明: by
  rw [← iSup_iterate_eq_nfp]; rw [← iSup_pow_natCast ha]
  simp

@[simp]

Depends on / 依赖: iSup_iterate_eq_nfp, iSup_pow_natCast
-/
theorem nfp_mul_one {a : Ordinal} (ha : 0 < a) : nfp (a * ·) 1 = a ^ ω := by
  rw [← iSup_iterate_eq_nfp]; rw [← iSup_pow_natCast ha]
  simp

@[simp]
/--
theorem `nfp_mul_zero` / 定理 `nfp_mul_zero`

English:
theorem nfp_mul_zero
  given: (a : Ordinal)
  statement: nfp (a * ·) 0 = 0
  proof: by
  rw [← nonpos_iff_eq_zero]; rw [nfp_le_iff]
  simp

中文:
定理 nfp_mul_zero
  条件: (a : Ordinal)
  结论: nfp (a * ·) 0 = 0
  证明: by
  rw [← nonpos_iff_eq_zero]; rw [nfp_le_iff]
  simp

Depends on / 依赖: nfp_le_iff, nonpos_iff_eq_zero
-/
theorem nfp_mul_zero (a : Ordinal) : nfp (a * ·) 0 = 0 := by
  rw [← nonpos_iff_eq_zero]; rw [nfp_le_iff]
  simp

/--
theorem `nfp_mul_eq_opow_omega0` / 定理 `nfp_mul_eq_opow_omega0`

English:
theorem nfp_mul_eq_opow_omega0
  given: {a b : Ordinal} (hb : 0 < b) (hba : b <= a ^ ω)
  proof: by
  rcases eq_zero_or_pos a with rfl | ha
  · rw [zero_opow omega0_ne_zero] at hba
    cases hba.not_gt hb
  apply le_antisymm
  · apply nfp_le_fp (isNormal_mul_right ha).monotone hba
    rw [← opow_one_add]; rw [one_add_omega0]
  rw [← nfp_mul_one ha]
  exact nfp_monotone (isNormal_mul_right ha).m

中文:
定理 nfp_mul_eq_opow_omega0
  条件: {a b : Ordinal} (hb : 0 < b) (hba : b <= a ^ ω)
  证明: by
  rcases eq_zero_or_pos a with rfl | ha
  · rw [zero_opow omega0_ne_zero] at hba
    cases hba.not_gt hb
  apply le_antisymm
  · apply nfp_le_fp (isNormal_mul_right ha).monotone hba
    rw [← opow_one_add]; rw [one_add_omega0]
  rw [← nfp_mul_one ha]
  exact nfp_monotone (isNormal_mul_right ha).m

Depends on / 依赖: eq_zero_or_pos, hba.not_gt, isNormal_mul_right, le_antisymm, monotone, nfp_le_fp, nfp_monotone, nfp_mul_one, not_gt, omega0_ne_zero, one_add_omega0, one_le_iff_pos, opow_one_add, zero_opow
-/
theorem nfp_mul_eq_opow_omega0 {a b : Ordinal} (hb : 0 < b) (hba : b <= a ^ ω) :
    nfp (a * ·) b = a ^ ω := by
  rcases eq_zero_or_pos a with rfl | ha
  · rw [zero_opow omega0_ne_zero] at hba
    cases hba.not_gt hb
  apply le_antisymm
  · apply nfp_le_fp (isNormal_mul_right ha).monotone hba
    rw [← opow_one_add]; rw [one_add_omega0]
  rw [← nfp_mul_one ha]
  exact nfp_monotone (isNormal_mul_right ha).monotone (one_le_iff_pos.2 hb)

/--
theorem `eq_zero_or_opow_omega0_le_of_mul_eq_right` / 定理 `eq_zero_or_opow_omega0_le_of_mul_eq_right`

English:
theorem eq_zero_or_opow_omega0_le_of_mul_eq_right
  given: {a b : Ordinal} (hab : a * b = b)
  proof: by
  rcases eq_zero_or_pos a with ha | ha
  · rw [ha, zero_opow omega0_ne_zero]
    exact .inr zero_le
  rw [or_iff_not_imp_left]
  intro hb
  rw [← nfp_mul_one ha]
  rw [← Ne]; rw [← one_le_iff_ne_zero] at hb
  exact nfp_le_fp (isNormal_mul_right ha).monotone hb (le_of_eq hab)

中文:
定理 eq_zero_or_opow_omega0_le_of_mul_eq_right
  条件: {a b : Ordinal} (hab : a * b = b)
  证明: by
  rcases eq_zero_or_pos a with ha | ha
  · rw [ha, zero_opow omega0_ne_zero]
    exact .inr zero_le
  rw [or_iff_not_imp_left]
  intro hb
  rw [← nfp_mul_one ha]
  rw [← Ne]; rw [← one_le_iff_ne_zero] at hb
  exact nfp_le_fp (isNormal_mul_right ha).monotone hb (le_of_eq hab)

Depends on / 依赖: eq_zero_or_pos, isNormal_mul_right, le_of_eq, monotone, nfp_le_fp, nfp_mul_one, omega0_ne_zero, one_le_iff_ne_zero, or_iff_not_imp_left, zero_le, zero_opow
-/
theorem eq_zero_or_opow_omega0_le_of_mul_eq_right {a b : Ordinal} (hab : a * b = b) :
    b = 0 ∨ a ^ ω <= b := by
  rcases eq_zero_or_pos a with ha | ha
  · rw [ha, zero_opow omega0_ne_zero]
    exact .inr zero_le
  rw [or_iff_not_imp_left]
  intro hb
  rw [← nfp_mul_one ha]
  rw [← Ne]; rw [← one_le_iff_ne_zero] at hb
  exact nfp_le_fp (isNormal_mul_right ha).monotone hb (le_of_eq hab)

/--
theorem `mul_eq_right_iff_opow_omega0_dvd` / 定理 `mul_eq_right_iff_opow_omega0_dvd`

English:
theorem mul_eq_right_iff_opow_omega0_dvd
  given: {a b : Ordinal}
  statement: a * b = b ↔ a ^ ω ∣ b
  proof: by
  rcases eq_zero_or_pos a with ha | ha
  · rw [ha, zero_mul, zero_opow omega0_ne_zero, zero_dvd_iff]
    exact eq_comm
  refine ⟨fun hab => ?_, fun h => ?_⟩
  · rw [dvd_iff_mod_eq_zero]
    rw [← div_add_mod b (a ^ ω)]; rw [mul_add]; rw [← mul_assoc]; rw [← opow_one_add]; rw [one_add_omega0]; rw 

中文:
定理 mul_eq_right_iff_opow_omega0_dvd
  条件: {a b : Ordinal}
  结论: a * b = b ↔ a ^ ω ∣ b
  证明: by
  rcases eq_zero_or_pos a with ha | ha
  · rw [ha, zero_mul, zero_opow omega0_ne_zero, zero_dvd_iff]
    exact eq_comm
  refine ⟨fun hab => ?_, fun h => ?_⟩
  · rw [dvd_iff_mod_eq_zero]
    rw [← div_add_mod b (a ^ ω)]; rw [mul_add]; rw [← mul_assoc]; rw [← opow_one_add]; rw [one_add_omega0]; rw 

Depends on / 依赖: add_left_cancel_iff, div_add_mod, dvd_iff_mod_eq_zero, eq_comm, eq_zero_or_opow_omega0_le_of_mul_eq_right, eq_zero_or_pos, mod_lt, mul_add, mul_assoc, not_lt_of_ge, omega0_ne_zero, one_add_omega0, opow_ne_zero, opow_one_add, pos_iff_ne_zero, zero_dvd_iff, zero_mul, zero_opow
-/
theorem mul_eq_right_iff_opow_omega0_dvd {a b : Ordinal} : a * b = b ↔ a ^ ω ∣ b := by
  rcases eq_zero_or_pos a with ha | ha
  · rw [ha, zero_mul, zero_opow omega0_ne_zero, zero_dvd_iff]
    exact eq_comm
  refine ⟨fun hab => ?_, fun h => ?_⟩
  · rw [dvd_iff_mod_eq_zero]
    rw [← div_add_mod b (a ^ ω)]; rw [mul_add]; rw [← mul_assoc]; rw [← opow_one_add]; rw [one_add_omega0]; rw [add_left_cancel_iff] at hab
    rcases eq_zero_or_opow_omega0_le_of_mul_eq_right hab with hab | hab
    · exact hab
    refine (not_lt_of_ge hab (mod_lt b (opow_ne_zero ω ?_))).elim
    rwa [← pos_iff_ne_zero]
  obtain ⟨c, hc⟩ := h
  rw [hc]; rw [← mul_assoc]; rw [← opow_one_add]; rw [one_add_omega0]

/--
theorem `mul_le_right_iff_opow_omega0_dvd` / 定理 `mul_le_right_iff_opow_omega0_dvd`

English:
theorem mul_le_right_iff_opow_omega0_dvd
  given: {a b : Ordinal} (ha : 0 < a)
  proof: by
  rw [← mul_eq_right_iff_opow_omega0_dvd]
  exact (isNormal_mul_right ha).strictMono.le_apply.ge_iff_eq'

中文:
定理 mul_le_right_iff_opow_omega0_dvd
  条件: {a b : Ordinal} (ha : 0 < a)
  证明: by
  rw [← mul_eq_right_iff_opow_omega0_dvd]
  exact (isNormal_mul_right ha).strictMono.le_apply.ge_iff_eq'

Depends on / 依赖: ge_iff_eq, isNormal_mul_right, le_apply, mul_eq_right_iff_opow_omega0_dvd, strictMono, strictMono.le_apply.ge_iff_eq
-/
theorem mul_le_right_iff_opow_omega0_dvd {a b : Ordinal} (ha : 0 < a) :
    a * b <= b ↔ (a ^ ω) ∣ b := by
  rw [← mul_eq_right_iff_opow_omega0_dvd]
  exact (isNormal_mul_right ha).strictMono.le_apply.ge_iff_eq'

/--
theorem `nfp_mul_opow_omega0_add` / 定理 `nfp_mul_opow_omega0_add`

English:
theorem nfp_mul_opow_omega0_add
  statement: {a c : Ordinal} (b) (ha : 0 < a) (hc : 0 < c)
  proof: by
  apply le_antisymm
  · apply nfp_le_fp (isNormal_mul_right ha).monotone
    · rw [mul_succ]
      gcongr
    · rw [← mul_assoc, ← opow_one_add, one_add_omega0]
  · obtain ⟨d, hd⟩ :=
      mul_eq_right_iff_opow_omega0_dvd.1 (nfp_fp (isNormal_mul_right ha) (a ^ ω * b + c))
    rw [hd]
    apply mu

中文:
定理 nfp_mul_opow_omega0_add
  结论: {a c : Ordinal} (b) (ha : 0 < a) (hc : 0 < c)
  证明: by
  apply le_antisymm
  · apply nfp_le_fp (isNormal_mul_right ha).monotone
    · rw [mul_succ]
      gcongr
    · rw [← mul_assoc, ← opow_one_add, one_add_omega0]
  · obtain ⟨d, hd⟩ :=
      mul_eq_right_iff_opow_omega0_dvd.1 (nfp_fp (isNormal_mul_right ha) (a ^ ω * b + c))
    rw [hd]
    apply mu

Depends on / 依赖: add_lt_add_right, add_zero, isNormal_mul_right, le_antisymm, le_nfp, monotone, mul_assoc, mul_eq_right_iff_opow_omega0_dvd, mul_le_mul_right, mul_succ, nfp_fp, nfp_le_fp, one_add_omega0, opow_one_add, opow_pos, succ_le_iff, trans_le
-/
theorem nfp_mul_opow_omega0_add {a c : Ordinal} (b) (ha : 0 < a) (hc : 0 < c)
    (hca : c <= a ^ ω) : nfp (a * ·) (a ^ ω * b + c) = a ^ ω * succ b := by
  apply le_antisymm
  · apply nfp_le_fp (isNormal_mul_right ha).monotone
    · rw [mul_succ]
      gcongr
    · rw [← mul_assoc, ← opow_one_add, one_add_omega0]
  · obtain ⟨d, hd⟩ :=
      mul_eq_right_iff_opow_omega0_dvd.1 (nfp_fp (isNormal_mul_right ha) (a ^ ω * b + c))
    rw [hd]
    apply mul_le_mul_right
    have := le_nfp (a * ·) (a ^ ω * b + c)
    rw [hd] at this
    have := (add_lt_add_right hc (a ^ ω * b)).trans_le this
    rw [add_zero]; rw [mul_lt_mul_iff_right₀ (opow_pos ω ha)] at this
    rwa [succ_le_iff]

/--
theorem `deriv_mul_eq_opow_omega0_mul` / 定理 `deriv_mul_eq_opow_omega0_mul`

English:
theorem deriv_mul_eq_opow_omega0_mul
  given: {a : Ordinal.{u}} (ha : 0 < a) (b)
  proof: by
  revert b
  rw [← funext_iff]; rw [IsNormal.ext_iff (isNormal_deriv _) (isNormal_mul_right (opow_pos ω ha))]
  refine ⟨?_, fun c h => ?_⟩
  · rw [bot_eq_zero, deriv_zero_right, nfp_mul_zero, mul_zero]
  · rw [deriv_succ, h]
    exact nfp_mul_opow_omega0_add c ha zero_lt_one (one_le_iff_pos.2 (op

中文:
定理 deriv_mul_eq_opow_omega0_mul
  条件: {a : Ordinal.{u}} (ha : 0 < a) (b)
  证明: by
  revert b
  rw [← funext_iff]; rw [IsNormal.ext_iff (isNormal_deriv _) (isNormal_mul_right (opow_pos ω ha))]
  refine ⟨?_, fun c h => ?_⟩
  · rw [bot_eq_zero, deriv_zero_right, nfp_mul_zero, mul_zero]
  · rw [deriv_succ, h]
    exact nfp_mul_opow_omega0_add c ha zero_lt_one (one_le_iff_pos.2 (op

Depends on / 依赖: IsNormal, IsNormal.ext_iff, bot_eq_zero, deriv_succ, deriv_zero_right, ext_iff, funext_iff, isNormal_deriv, isNormal_mul_right, mul_zero, nfp_mul_opow_omega0_add, nfp_mul_zero, one_le_iff_pos, opow_pos, revert, zero_lt_one
-/
theorem deriv_mul_eq_opow_omega0_mul {a : Ordinal.{u}} (ha : 0 < a) (b) :
    deriv (a * ·) b = a ^ ω * b := by
  revert b
  rw [← funext_iff]; rw [IsNormal.ext_iff (isNormal_deriv _) (isNormal_mul_right (opow_pos ω ha))]
  refine ⟨?_, fun c h => ?_⟩
  · rw [bot_eq_zero, deriv_zero_right, nfp_mul_zero, mul_zero]
  · rw [deriv_succ, h]
    exact nfp_mul_opow_omega0_add c ha zero_lt_one (one_le_iff_pos.2 (opow_pos _ ha))

end Ordinal
