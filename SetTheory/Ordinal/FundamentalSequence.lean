/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Mario Carneiro
-/
module

public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

/-!
# Fundamental sequences

A fundamental sequence for a countable limit ordinal `o` is a strictly monotone function `ℕ → Iio o`
with cofinal range. We can generalize this notion to arbitrary ordinals by setting the domain as
`Iio o.cof.card`. Note that for a countable limit ordinal, one has `o.cof.card = ω`.

## Main results

- `Ordinal.exists_isFundamentalSeq`: every ordinal has a fundamental sequence.
-/

@[expose] public section

universe u

open Cardinal Order Set

namespace Ordinal

variable {a b o : Ordinal}

/--
Definition of `IsFundamentalSeq` / `IsFundamentalSeq` 的定义

English:
structure IsFundamentalSeq
  parameters: (f : Iio a -> Iio o)
  axioms and operations (3):
    - le_ord_cof : a <= o.cof.ord
    - strictMono : StrictMono f
    - isCofinal_range : IsCofinal (range f)

中文:
结构 是FundamentalSeq
  参数: (f : 左无界右开区间 a -> 左无界右开区间 o)
  公理与运算 (3 个):
    - le_ord_cof : a <= o.cof.ord
    - strictMono : 严格递增 f
    - isCofinal_range : IsCofinal (range f)
-/
structure IsFundamentalSeq (f : Iio a -> Iio o) : Prop where
  /-- This condition alongside the others is enough to conclude `o.cof.ord = a`, see
  `IsFundamentalSeq.ord_cof`. -/
  le_ord_cof : a <= o.cof.ord
  /-- A fundamental sequence is strictly monotonic. -/
  strictMono : StrictMono f
  /-- A fundamental sequence for `o` has cofinal range, i.e. its least strict upper bound equals the
  ordinal `o`. See `IsFundamentalSeq.iSup_add_one_eq` and `IsFundamentalSeq.iSup_eq`. -/
  isCofinal_range : IsCofinal (range f)

namespace IsFundamentalSeq
variable {f : Iio a -> Iio o} {g : Iio b -> Iio a}

/--
theorem `iSup_add_one_eq` / 定理 `iSup_add_one_eq`

English:
theorem iSup_add_one_eq
  given: (hf : IsFundamentalSeq f)
  statement: ⨆ i, (f i).1 + 1 = o
  proof: by
  apply le_antisymm
  · simp_rw [Ordinal.iSup_le_iff, add_one_le_iff]
    exact fun i => (f i).2
  · refine le_of_forall_lt fun b hb => ?_
    obtain ⟨_, ⟨c, rfl⟩, hc : b <= _⟩ := hf.isCofinal_range ⟨b, hb⟩
    apply hc.trans_lt
    rw [← add_one_le_iff]
    apply Ordinal.le_iSup

中文:
定理 iSup_add_one_eq
  条件: (hf : 是FundamentalSeq f)
  结论: ⨆ i, (f i).1 + 1 = o
  证明: by
  apply le_antisymm
  · simp_rw [Ordinal.iSup_le_iff, add_one_le_iff]
    exact fun i => (f i).2
  · refine le_of_forall_lt fun b hb => ?_
    obtain ⟨_, ⟨c, rfl⟩, hc : b <= _⟩ := hf.isCofinal_range ⟨b, hb⟩
    apply hc.trans_lt
    rw [← add_one_le_iff]
    apply Ordinal.le_iSup

Depends on / 依赖: Ordinal, Ordinal.iSup_le_iff, Ordinal.le_iSup, add_one_le_iff, hc.trans_lt, hf.isCofinal_range, iSup_le_iff, isCofinal_range, le_antisymm, le_iSup, le_of_forall_lt, simp_rw, trans_lt
-/
theorem iSup_add_one_eq (hf : IsFundamentalSeq f) : ⨆ i, (f i).1 + 1 = o := by
  apply le_antisymm
  · simp_rw [Ordinal.iSup_le_iff, add_one_le_iff]
    exact fun i => (f i).2
  · refine le_of_forall_lt fun b hb => ?_
    obtain ⟨_, ⟨c, rfl⟩, hc : b <= _⟩ := hf.isCofinal_range ⟨b, hb⟩
    apply hc.trans_lt
    rw [← add_one_le_iff]
    apply Ordinal.le_iSup

/--
theorem `ord_cof` / 定理 `ord_cof`

English:
theorem ord_cof
  given: (hf : IsFundamentalSeq f)
  statement: o.cof.ord = a
  proof: by
  apply hf.le_ord_cof.antisymm'
  rw [← hf.iSup_add_one_eq]; rw [cof_iSup_Iio_add_one hf.strictMono]
  exact ord_cof_le a

中文:
定理 ord_cof
  条件: (hf : 是FundamentalSeq f)
  结论: o.cof.ord = a
  证明: by
  apply hf.le_ord_cof.antisymm'
  rw [← hf.iSup_add_one_eq]; rw [cof_iSup_Iio_add_one hf.strictMono]
  exact ord_cof_le a

Depends on / 依赖: antisymm, cof_iSup_Iio_add_one, hf.iSup_add_one_eq, hf.le_ord_cof.antisymm, hf.strictMono, iSup_add_one_eq, le_ord_cof, ord_cof_le, strictMono
-/
theorem ord_cof (hf : IsFundamentalSeq f) : o.cof.ord = a := by
  apply hf.le_ord_cof.antisymm'
  rw [← hf.iSup_add_one_eq]; rw [cof_iSup_Iio_add_one hf.strictMono]
  exact ord_cof_le a

/--
theorem `iSup_eq` / 定理 `iSup_eq`

English:
theorem iSup_eq
  given: (hf : IsFundamentalSeq f) (ha : 1 < a)
  statement: ⨆ i, (f i).1 = o
  proof: by
  rw [← iSup_Iio_add_one hf.strictMono]; rw [hf.iSup_add_one_eq]
  rw [← hf.ord_cof]
  apply (isSuccLimit_ord _).isSuccPrelimit
  rwa [aleph0_le_cof_iff, ← ord_lt_ord, hf.ord_cof, ord_one]

中文:
定理 iSup_eq
  条件: (hf : 是FundamentalSeq f) (ha : 1 < a)
  结论: ⨆ i, (f i).1 = o
  证明: by
  rw [← iSup_Iio_add_one hf.strictMono]; rw [hf.iSup_add_one_eq]
  rw [← hf.ord_cof]
  apply (isSuccLimit_ord _).isSuccPrelimit
  rwa [aleph0_le_cof_iff, ← ord_lt_ord, hf.ord_cof, ord_one]

Depends on / 依赖: aleph0_le_cof_iff, hf.iSup_add_one_eq, hf.ord_cof, hf.strictMono, iSup_Iio_add_one, iSup_add_one_eq, isSuccLimit_ord, isSuccPrelimit, ord_cof, ord_lt_ord, ord_one, strictMono
-/
theorem iSup_eq (hf : IsFundamentalSeq f) (ha : 1 < a) : ⨆ i, (f i).1 = o := by
  rw [← iSup_Iio_add_one hf.strictMono]; rw [hf.iSup_add_one_eq]
  rw [← hf.ord_cof]
  apply (isSuccLimit_ord _).isSuccPrelimit
  rwa [aleph0_le_cof_iff, ← ord_lt_ord, hf.ord_cof, ord_one]

/--
theorem `id` / 定理 `id`

English:
theorem id
  given: (ho : o <= o.cof.ord)
  statement: IsFundamentalSeq (o := o) id where
  proof: strictMono_id
  isCofinal_range := by simp
  le_ord_cof := ho

中文:
定理 id
  条件: (ho : o <= o.cof.ord)
  结论: 是FundamentalSeq (o := o) id where
  证明: strictMono_id
  isCofinal_range := by simp
  le_ord_cof := ho
-/
protected theorem id (ho : o <= o.cof.ord) : IsFundamentalSeq (o := o) id where
  strictMono := strictMono_id
  isCofinal_range := by simp
  le_ord_cof := ho

/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  given: (f : Iio 0 -> Iio 0)
  statement: IsFundamentalSeq f where
  proof: by simp
  le_ord_cof := by simp
  isCofinal_range := .of_isEmpty

中文:
定理 zero
  条件: (f : 左无界右开区间 0 -> 左无界右开区间 0)
  结论: 是FundamentalSeq f where
  证明: by simp
  le_ord_cof := by simp
  isCofinal_range := .of_isEmpty
-/
protected theorem zero (f : Iio 0 -> Iio 0) : IsFundamentalSeq f where
  strictMono _ := by simp
  le_ord_cof := by simp
  isCofinal_range := .of_isEmpty

set_option backward.isDefEq.respectTransparency false in
/--
theorem `add_one` / 定理 `add_one`

English:
theorem add_one
  given: (o : Ordinal)
  proof: by simp
  le_ord_cof := by simp
  isCofinal_range := by simp [IsTop]

中文:
定理 add_one
  条件: (o : 序数)
  证明: by simp
  le_ord_cof := by simp
  isCofinal_range := by simp [IsTop]
-/
protected theorem add_one (o : Ordinal) :
    @IsFundamentalSeq 1 (o + 1) fun _ => ⟨o, lt_add_one o⟩ where
  strictMono _ := by simp
  le_ord_cof := by simp
  isCofinal_range := by simp [IsTop]

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: (hf : IsFundamentalSeq f) (hg : IsFundamentalSeq g)
  proof: hf.strictMono.comp hg.strictMono
  le_ord_cof := by rw [hf.ord_cof, ← hg.ord_cof]; exact a.ord_cof_le
  isCofinal_range := by
    rw [range_comp]
    exact hg.isCofinal_range.image hf.strictMono.monotone hf.isCofinal_range

中文:
定理 comp
  条件: (hf : 是FundamentalSeq f) (hg : 是FundamentalSeq g)
  证明: hf.strictMono.comp hg.strictMono
  le_ord_cof := by rw [hf.ord_cof, ← hg.ord_cof]; exact a.ord_cof_le
  isCofinal_range := by
    rw [range_comp]
    exact hg.isCofinal_range.image hf.strictMono.monotone hf.isCofinal_range
-/
protected theorem comp (hf : IsFundamentalSeq f) (hg : IsFundamentalSeq g) :
    IsFundamentalSeq (f ∘ g) where
  strictMono := hf.strictMono.comp hg.strictMono
  le_ord_cof := by rw [hf.ord_cof, ← hg.ord_cof]; exact a.ord_cof_le
  isCofinal_range := by
    rw [range_comp]
    exact hg.isCofinal_range.image hf.strictMono.monotone hf.isCofinal_range

/--
theorem `comp_isNormal` / 定理 `comp_isNormal`

English:
theorem comp_isNormal
  statement: {g : Ordinal -> Ordinal} (hg : IsNormal g) (hf : IsFundamentalSeq f)
  proof: hg.strictMono.comp hf.strictMono
  le_ord_cof := by rw [cof_map_of_isNormal hg ho, hf.ord_cof]
  isCofinal_range := by
    rintro ⟨b, hb⟩
    rw [mem_Iio]; rw [hg.lt_iff_exists_lt ho] at hb
    obtain ⟨c, hc, hc'⟩ := hb
    obtain ⟨_, ⟨d, rfl⟩, hd⟩ := hf.isCofinal_range ⟨c, hc⟩
    refine ⟨⟨_, hg.st

中文:
定理 comp_isNormal
  结论: {g : 序数 -> 序数} (hg : 是正规 g) (hf : 是FundamentalSeq f)
  证明: hg.strictMono.comp hf.strictMono
  le_ord_cof := by rw [cof_map_of_isNormal hg ho, hf.ord_cof]
  isCofinal_range := by
    rintro ⟨b, hb⟩
    rw [mem_Iio]; rw [hg.lt_iff_exists_lt ho] at hb
    obtain ⟨c, hc, hc'⟩ := hb
    obtain ⟨_, ⟨d, rfl⟩, hd⟩ := hf.isCofinal_range ⟨c, hc⟩
    refine ⟨⟨_, hg.st

Depends on / 依赖: hf.strictMono, hg.strictMono.comp, strictMono
-/
theorem comp_isNormal {g : Ordinal -> Ordinal} (hg : IsNormal g) (hf : IsFundamentalSeq f)
    (ho : IsSuccLimit o) : IsFundamentalSeq fun i => ⟨g (f i), hg.strictMono (f i).2⟩ where
  strictMono := hg.strictMono.comp hf.strictMono
  le_ord_cof := by rw [cof_map_of_isNormal hg ho, hf.ord_cof]
  isCofinal_range := by
    rintro ⟨b, hb⟩
    rw [mem_Iio]; rw [hg.lt_iff_exists_lt ho] at hb
    obtain ⟨c, hc, hc'⟩ := hb
    obtain ⟨_, ⟨d, rfl⟩, hd⟩ := hf.isCofinal_range ⟨c, hc⟩
    refine ⟨⟨_, hg.strictMono (f d).2⟩, ?_, hc'.le.trans (hg.monotone hd)⟩
    simp

end IsFundamentalSeq

/--
theorem `exists_isFundamentalSeq` / 定理 `exists_isFundamentalSeq`

English:
theorem exists_isFundamentalSeq
  given: (ha : o.cof.ord = a)
  statement: exists f : Iio a -> Iio o, IsFundamentalSeq f
  proof: by
  subst ha
  obtain ⟨s, hs, hs'⟩ := exists_ord_cof_eq o.ToType
  rw [cof_toType] at hs'
let g := (OrderIso.setCongr _ _ (congrArg _ hs'.symm)).trans
    .ofRelIsoLT (enum (α := s) (· < ·))
  refine ⟨fun i => g i, le_rfl, fun _ => by simp, ?_⟩
  rw [range_comp']; rw [OrderIso.map_isCofinal_iff]; r

中文:
定理 存在_isFundamentalSeq
  条件: (ha : o.cof.ord = a)
  结论: 存在 f : 左无界右开区间 a -> 左无界右开区间 o, 是FundamentalSeq f
  证明: by
  subst ha
  obtain ⟨s, hs, hs'⟩ := exists_ord_cof_eq o.ToType
  rw [cof_toType] at hs'
let g := (OrderIso.setCongr _ _ (congrArg _ hs'.symm)).trans
    .ofRelIsoLT (enum (α := s) (· < ·))
  refine ⟨fun i => g i, le_rfl, fun _ => by simp, ?_⟩
  rw [range_comp']; rw [OrderIso.map_isCofinal_iff]; r

Depends on / 依赖: OrderIso, OrderIso.map_isCofinal_iff, OrderIso.setCongr, ToType, cof_toType, exists_ord_cof_eq, g.range_eq, le_rfl, map_isCofinal_iff, o.ToType, ofRelIsoLT, range_comp, range_eq, setCongr
-/
theorem exists_isFundamentalSeq (ha : o.cof.ord = a) : exists f : Iio a -> Iio o, IsFundamentalSeq f := by
  subst ha
  obtain ⟨s, hs, hs'⟩ := exists_ord_cof_eq o.ToType
  rw [cof_toType] at hs'
let g := (OrderIso.setCongr _ _ (congrArg _ hs'.symm)).trans
    .ofRelIsoLT (enum (α := s) (· < ·))
  refine ⟨fun i => g i, le_rfl, fun _ => by simp, ?_⟩
  rw [range_comp']; rw [OrderIso.map_isCofinal_iff]; rw [range_comp']; rw [g.range_eq]
  simpa

/-! ### Deprecated material -/

/-- A fundamental sequence for `a` is an increasing sequence of length `o = cof a` that converges at
    `a`. We provide `o` explicitly in order to avoid type rewrites. -/
@[deprecated IsFundamentalSeq (since := "2026-03-23")]
/--
Definition of `IsFundamentalSequence` / `IsFundamentalSequence` 的定义

English:
definition IsFundamentalSequence
  signature: (a o : Ordinal.{u}) (f : forall b < o, Ordinal.{u})
  body: o <= a.cof.ord ∧ (forall {i j} (hi hj), i < j -> f i hi < f j hj) ∧ blsub.{u, u} o f = a

中文:
定义 IsFundamentalSequence
  签名: (a o : 序数.{u}) (f : 对任意 b < o, 序数.{u})
  定义体: o <= a.cof.ord ∧ (forall {i j} (hi hj), i < j -> f i hi < f j hj) ∧ blsub.{u, u} o f = a

Depends on / 依赖: a.cof.ord
-/
def IsFundamentalSequence (a o : Ordinal.{u}) (f : forall b < o, Ordinal.{u}) : Prop :=
  o <= a.cof.ord ∧ (forall {i j} (hi hj), i < j -> f i hi < f j hj) ∧ blsub.{u, u} o f = a

namespace IsFundamentalSequence

variable {a o : Ordinal.{u}} {f : forall b < o, Ordinal.{u}}

@[deprecated IsFundamentalSeq.ord_cof (since := "2026-03-23")]
/--
theorem `cof_eq` / 定理 `cof_eq`

English:
theorem cof_eq
  given: (hf : IsFundamentalSequence a o f)
  statement: a.cof.ord = o
  proof: hf.1.antisymm' by
    rw [← hf.2.2]
    exact (ord_le_ord.2 (cof_blsub_le f)).trans (ord_card_le o)

@[deprecated IsFundamentalSeq.strictMono (since := "2026-03-23")]

中文:
定理 cof_eq
  条件: (hf : IsFundamentalSequence a o f)
  结论: a.cof.ord = o
  证明: hf.1.antisymm' by
    rw [← hf.2.2]
    exact (ord_le_ord.2 (cof_blsub_le f)).trans (ord_card_le o)

@[deprecated IsFundamentalSeq.strictMono (since := "2026-03-23")]
-/
protected theorem cof_eq (hf : IsFundamentalSequence a o f) : a.cof.ord = o :=
hf.1.antisymm' by
    rw [← hf.2.2]
    exact (ord_le_ord.2 (cof_blsub_le f)).trans (ord_card_le o)

@[deprecated IsFundamentalSeq.strictMono (since := "2026-03-23")]
/--
theorem `strict_mono` / 定理 `strict_mono`

English:
theorem strict_mono
  given: (hf : IsFundamentalSequence a o f) {i j}
  proof: hf.2.1

@[deprecated IsFundamentalSeq.iSup_add_one_eq (since := "2026-03-23")]

中文:
定理 strict_mono
  条件: (hf : IsFundamentalSequence a o f) {i j}
  证明: hf.2.1

@[deprecated IsFundamentalSeq.iSup_add_one_eq (since := "2026-03-23")]

Depends on / 依赖: h.symm
-/
protected theorem strict_mono (hf : IsFundamentalSequence a o f) {i j} :
    forall hi hj, i < j -> f i hi < f j hj :=
  hf.2.1

@[deprecated IsFundamentalSeq.iSup_add_one_eq (since := "2026-03-23")]
/--
theorem `blsub_eq` / 定理 `blsub_eq`

English:
theorem blsub_eq
  given: (hf : IsFundamentalSequence a o f)
  statement: blsub.{u, u} o f = a
  proof: hf.2.2

@[deprecated IsFundamentalSeq (since := "2026-03-23")]

中文:
定理 blsub_eq
  条件: (hf : IsFundamentalSequence a o f)
  结论: blsub.{u, u} o f = a
  证明: hf.2.2

@[deprecated IsFundamentalSeq (since := "2026-03-23")]
-/
theorem blsub_eq (hf : IsFundamentalSequence a o f) : blsub.{u, u} o f = a :=
  hf.2.2

@[deprecated IsFundamentalSeq (since := "2026-03-23")]
/--
theorem `ord_cof` / 定理 `ord_cof`

English:
theorem ord_cof
  given: (hf : IsFundamentalSequence a o f)
  proof: by
  have H := hf.cof_eq
  subst H
  exact hf

@[deprecated IsFundamentalSeq.id (since := "2026-03-23")]

中文:
定理 ord_cof
  条件: (hf : IsFundamentalSequence a o f)
  证明: by
  have H := hf.cof_eq
  subst H
  exact hf

@[deprecated IsFundamentalSeq.id (since := "2026-03-23")]

Depends on / 依赖: cof_eq, hf.cof_eq
-/
theorem ord_cof (hf : IsFundamentalSequence a o f) :
    IsFundamentalSequence a a.cof.ord fun i hi => f i (hi.trans_le (by rw [hf.cof_eq])) := by
  have H := hf.cof_eq
  subst H
  exact hf

@[deprecated IsFundamentalSeq.id (since := "2026-03-23")]
/--
theorem `id_of_le_cof` / 定理 `id_of_le_cof`

English:
theorem id_of_le_cof
  given: (h : o <= o.cof.ord)
  statement: IsFundamentalSequence o o fun a _ => a
  proof: ⟨h, @fun _ _ _ _ => id, blsub_id o⟩

@[deprecated IsFundamentalSeq.zero (since := "2026-03-23")]

中文:
定理 id_of_le_cof
  条件: (h : o <= o.cof.ord)
  结论: IsFundamentalSequence o o fun a _ => a
  证明: ⟨h, @fun _ _ _ _ => id, blsub_id o⟩

@[deprecated IsFundamentalSeq.zero (since := "2026-03-23")]

Depends on / 依赖: blsub_id
-/
theorem id_of_le_cof (h : o <= o.cof.ord) : IsFundamentalSequence o o fun a _ => a :=
  ⟨h, @fun _ _ _ _ => id, blsub_id o⟩

@[deprecated IsFundamentalSeq.zero (since := "2026-03-23")]
/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  given: {f : forall b < (0 : Ordinal), Ordinal}
  statement: IsFundamentalSequence 0 0 f
  proof: ⟨by rw [cof_zero, ord_zero], @fun i _ hi => (not_lt_zero hi).elim, blsub_zero f⟩

@[deprecated IsFundamentalSeq.add_one (since := "2026-03-23")]

中文:
定理 zero
  条件: {f : 对任意 b < (0 : 序数), 序数}
  结论: IsFundamentalSequence 0 0 f
  证明: ⟨by rw [cof_zero, ord_zero], @fun i _ hi => (not_lt_zero hi).elim, blsub_zero f⟩

@[deprecated IsFundamentalSeq.add_one (since := "2026-03-23")]
-/
protected theorem zero {f : forall b < (0 : Ordinal), Ordinal} : IsFundamentalSequence 0 0 f :=
  ⟨by rw [cof_zero, ord_zero], @fun i _ hi => (not_lt_zero hi).elim, blsub_zero f⟩

@[deprecated IsFundamentalSeq.add_one (since := "2026-03-23")]
/--
theorem `succ` / 定理 `succ`

English:
theorem succ
  statement: IsFundamentalSequence (succ o) 1 fun _ _ => o
  proof: by
  refine ⟨?_, @fun i j hi hj h => ?_, blsub_const Ordinal.one_ne_zero o⟩
  · rw [cof_succ, ord_one]
  · rw [lt_one_iff_zero] at hi hj
    rw [hi]; rw [hj] at h
    exact h.false.elim

@[deprecated IsFundamentalSeq.strictMono (since := "2026-03-23")]

中文:
定理 succ
  结论: IsFundamentalSequence (succ o) 1 fun _ _ => o
  证明: by
  refine ⟨?_, @fun i j hi hj h => ?_, blsub_const Ordinal.one_ne_zero o⟩
  · rw [cof_succ, ord_one]
  · rw [lt_one_iff_zero] at hi hj
    rw [hi]; rw [hj] at h
    exact h.false.elim

@[deprecated IsFundamentalSeq.strictMono (since := "2026-03-23")]
-/
protected theorem succ : IsFundamentalSequence (succ o) 1 fun _ _ => o := by
  refine ⟨?_, @fun i j hi hj h => ?_, blsub_const Ordinal.one_ne_zero o⟩
  · rw [cof_succ, ord_one]
  · rw [lt_one_iff_zero] at hi hj
    rw [hi]; rw [hj] at h
    exact h.false.elim

@[deprecated IsFundamentalSeq.strictMono (since := "2026-03-23")]
/--
theorem `monotone` / 定理 `monotone`

English:
theorem monotone
  statement: (hf : IsFundamentalSequence a o f) {i j : Ordinal} (hi : i < o)
  proof: by
  rcases lt_or_eq_of_le hij with (hij | rfl)
  · exact (hf.2.1 hi hj hij).le
  · rfl

@[deprecated IsFundamentalSeq.comp (since := "2026-03-23")]

中文:
定理 monotone
  结论: (hf : IsFundamentalSequence a o f) {i j : 序数} (hi : i < o)
  证明: by
  rcases lt_or_eq_of_le hij with (hij | rfl)
  · exact (hf.2.1 hi hj hij).le
  · rfl

@[deprecated IsFundamentalSeq.comp (since := "2026-03-23")]
-/
protected theorem monotone (hf : IsFundamentalSequence a o f) {i j : Ordinal} (hi : i < o)
    (hj : j < o) (hij : i <= j) : f i hi <= f j hj := by
  rcases lt_or_eq_of_le hij with (hij | rfl)
  · exact (hf.2.1 hi hj hij).le
  · rfl

@[deprecated IsFundamentalSeq.comp (since := "2026-03-23")]
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  statement: {a o o' : Ordinal.{u}} {f : forall b < o, Ordinal.{u}} (hf : IsFundamentalSequence a o f)
  proof: by
  refine ⟨?_, @fun i j _ _ h => hf.2.1 _ _ (hg.2.1 _ _ h), ?_⟩
  · rw [hf.cof_eq]
    exact hg.1.trans (ord_cof_le o)
  · rw [@blsub_comp.{u, u, u} o _ f (@IsFundamentalSequence.monotone _ _ f hf)]
    · exact hf.2.2
    · exact hg.2.2

@[deprecated IsFundamentalSeq (since := "2026-03-23")]

中文:
定理 trans
  结论: {a o o' : 序数.{u}} {f : 对任意 b < o, 序数.{u}} (hf : IsFundamentalSequence a o f)
  证明: by
  refine ⟨?_, @fun i j _ _ h => hf.2.1 _ _ (hg.2.1 _ _ h), ?_⟩
  · rw [hf.cof_eq]
    exact hg.1.trans (ord_cof_le o)
  · rw [@blsub_comp.{u, u, u} o _ f (@IsFundamentalSequence.monotone _ _ f hf)]
    · exact hf.2.2
    · exact hg.2.2

@[deprecated IsFundamentalSeq (since := "2026-03-23")]

Depends on / 依赖: IsFundamentalSequence, IsFundamentalSequence.monotone, blsub_comp, cof_eq, hf.cof_eq, monotone, ord_cof_le
-/
theorem trans {a o o' : Ordinal.{u}} {f : forall b < o, Ordinal.{u}} (hf : IsFundamentalSequence a o f)
    {g : forall b < o', Ordinal.{u}} (hg : IsFundamentalSequence o o' g) :
    IsFundamentalSequence a o' fun i hi =>
      f (g i hi) (by rw [← hg.2.2]; apply lt_blsub) := by
  refine ⟨?_, @fun i j _ _ h => hf.2.1 _ _ (hg.2.1 _ _ h), ?_⟩
  · rw [hf.cof_eq]
    exact hg.1.trans (ord_cof_le o)
  · rw [@blsub_comp.{u, u, u} o _ f (@IsFundamentalSequence.monotone _ _ f hf)]
    · exact hf.2.2
    · exact hg.2.2

@[deprecated IsFundamentalSeq (since := "2026-03-23")]
/--
theorem `lt` / 定理 `lt`

English:
theorem lt
  statement: {a o : Ordinal} {s : Π p < o, Ordinal}
  proof: h.blsub_eq ▸ lt_blsub s p hp

中文:
定理 lt
  结论: {a o : 序数} {s : Π p < o, 序数}
  证明: h.blsub_eq ▸ lt_blsub s p hp
-/
protected theorem lt {a o : Ordinal} {s : Π p < o, Ordinal}
    (h : IsFundamentalSequence a o s) {p : Ordinal} (hp : p < o) : s p hp < a :=
  h.blsub_eq ▸ lt_blsub s p hp

end IsFundamentalSequence

/-- Every ordinal has a fundamental sequence. -/
@[deprecated exists_isFundamentalSeq (since := "2026-03-23")]
/--
theorem `exists_fundamental_sequence` / 定理 `exists_fundamental_sequence`

English:
theorem exists_fundamental_sequence
  given: (a : Ordinal.{u})
  proof: by
  suffices h : exists o f, IsFundamentalSequence a o f by
    rcases h with ⟨o, f, hf⟩
    exact ⟨_, hf.ord_cof⟩
  rcases exists_lsub_cof a with ⟨ι, f, hf, hι⟩
  rcases ord_eq ι with ⟨r, wo, hr⟩
  let r' := Subrel r fun i => forall j, r j i -> f j < f i
  let hrr' : r' ↪r r := Subrel.relEmbedding

中文:
定理 存在_fundamental_sequence
  条件: (a : 序数.{u})
  证明: by
  suffices h : exists o f, IsFundamentalSequence a o f by
    rcases h with ⟨o, f, hf⟩
    exact ⟨_, hf.ord_cof⟩
  rcases exists_lsub_cof a with ⟨ι, f, hf, hι⟩
  rcases ord_eq ι with ⟨r, wo, hr⟩
  let r' := Subrel r fun i => forall j, r j i -> f j < f i
  let hrr' : r' ↪r r := Subrel.relEmbedding

Depends on / 依赖: IsFundamentalSequence, Subrel, Subrel.relEmbedding, blsub_le, exists_lsub_cof, hf.le, hf.ord_cof, isWellOrder, le_antisymm, lsub_le_iff, ord_cof, ord_eq, ordinal_type_le, ordinal_type_le.trans, relEmbedding
-/
theorem exists_fundamental_sequence (a : Ordinal.{u}) :
    exists f, IsFundamentalSequence a a.cof.ord f := by
  suffices h : exists o f, IsFundamentalSequence a o f by
    rcases h with ⟨o, f, hf⟩
    exact ⟨_, hf.ord_cof⟩
  rcases exists_lsub_cof a with ⟨ι, f, hf, hι⟩
  rcases ord_eq ι with ⟨r, wo, hr⟩
  let r' := Subrel r fun i => forall j, r j i -> f j < f i
  let hrr' : r' ↪r r := Subrel.relEmbedding _ _
  have := hrr'.isWellOrder
  refine
    ⟨_, _, hrr'.ordinal_type_le.trans ?_, @fun i j _ h _ => (enum r' ⟨j, h⟩).prop _ ?_,
      le_antisymm (blsub_le fun i hi => lsub_le_iff.1 hf.le _) ?_⟩
  · rw [← hι, hr]
  · change r (hrr'.1 _) (hrr'.1 _)
    rwa [hrr'.2, @enum_lt_enum _ r']
  · rw [← hf, lsub_le_iff]
    intro i
    suffices h : exists i' hi', f i <= bfamilyOfFamily' r' (fun i => f i) i' hi' by
      rcases h with ⟨i', hi', hfg⟩
      exact hfg.trans_lt (lt_blsub _ _ _)
    by_cases! h : forall j, r j i -> f j < f i
    · refine ⟨typein r' ⟨i, h⟩, typein_lt_type _ _, ?_⟩
      rw [bfamilyOfFamily'_typein]
    · obtain ⟨hji, hij⟩ := wo.wf.min_mem _ h
      refine ⟨typein r' ⟨_, fun k hkj => lt_of_lt_of_le ?_ hij⟩, typein_lt_type _ _, ?_⟩
      · by_contra! H
        exact (wo.wf.not_lt_min {j | r j i ∧ f i <= f j} ⟨IsTrans.trans _ _ _ hkj hji, H⟩) hkj
      · rwa [bfamilyOfFamily'_typein]

@[deprecated IsFundamentalSeq.comp_isNormal (since := "2026-03-23")]
/--
theorem `IsFundamentalSequence.of_isNormal` / 定理 `IsFundamentalSequence.of_isNormal`

English:
theorem IsFundamentalSequence.of_isNormal
  statement: {f : Ordinal.{u} -> Ordinal.{u}} (hf : IsNormal f)
  proof: by
  refine ⟨?_, @fun i j _ _ h => hf.strictMono (hg.2.1 _ _ h), ?_⟩
  · grind [Ordinal.IsFundamentalSequence, cof_map_of_isNormal]
  · rw [@blsub_comp.{u, u, u} a _ (fun b _ => f b) (@fun i j _ _ h => hf.strictMono.monotone h) g
        hg.2.2]
    exact IsNormal.blsub_eq.{u, u} hf ha

中文:
定理 IsFundamentalSequence.of_isNormal
  结论: {f : 序数.{u} -> 序数.{u}} (hf : 是正规 f)
  证明: by
  refine ⟨?_, @fun i j _ _ h => hf.strictMono (hg.2.1 _ _ h), ?_⟩
  · grind [Ordinal.IsFundamentalSequence, cof_map_of_isNormal]
  · rw [@blsub_comp.{u, u, u} a _ (fun b _ => f b) (@fun i j _ _ h => hf.strictMono.monotone h) g
        hg.2.2]
    exact IsNormal.blsub_eq.{u, u} hf ha

Depends on / 依赖: IsFundamentalSequence, IsNormal, IsNormal.blsub_eq, Ordinal, Ordinal.IsFundamentalSequence, blsub_comp, blsub_eq, cof_map_of_isNormal, hf.strictMono, hf.strictMono.monotone, monotone, strictMono
-/
theorem IsFundamentalSequence.of_isNormal {f : Ordinal.{u} -> Ordinal.{u}} (hf : IsNormal f)
    {a o} (ha : IsSuccLimit a) {g} (hg : IsFundamentalSequence a o g) :
    IsFundamentalSequence (f a) o fun b hb => f (g b hb) := by
  refine ⟨?_, @fun i j _ _ h => hf.strictMono (hg.2.1 _ _ h), ?_⟩
  · grind [Ordinal.IsFundamentalSequence, cof_map_of_isNormal]
  · rw [@blsub_comp.{u, u, u} a _ (fun b _ => f b) (@fun i j _ _ h => hf.strictMono.monotone h) g
        hg.2.2]
    exact IsNormal.blsub_eq.{u, u} hf ha

end Ordinal
