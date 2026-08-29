/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Yaël Dillies
-/
module

public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Data.Set.Function
public import Mathlib.Order.Directed

/-!
# Monotone functions on intervals

This file shows many variants of the fact that a monotone function `f` sends an interval with
endpoints `a` and `b` to the interval with endpoints `f a` and `f b`.
-/

public section

variable {α β : Type*} {f : α -> β}

open Set

section Preorder
variable [Preorder α] [Preorder β] {a b : α}

/--
lemma `MonotoneOn.mapsTo_Ici` / 引理 `MonotoneOn.mapsTo_Ici`

English:
lemma MonotoneOn.mapsTo_Ici
  given: (h : MonotoneOn f (Ici a))
  statement: MapsTo f (Ici a) (Ici (f a))
  proof: fun _ _ => by aesop

中文:
引理 MonotoneOn.mapsTo_Ici
  条件: (h : MonotoneOn f (左闭右无界区间 a))
  结论: 映射到 f (左闭右无界区间 a) (左闭右无界区间 (f a))
  证明: fun _ _ => by aesop
-/
lemma MonotoneOn.mapsTo_Ici (h : MonotoneOn f (Ici a)) : MapsTo f (Ici a) (Ici (f a)) :=
  fun _ _ => by aesop

/--
lemma `MonotoneOn.mapsTo_Iic` / 引理 `MonotoneOn.mapsTo_Iic`

English:
lemma MonotoneOn.mapsTo_Iic
  given: (h : MonotoneOn f (Iic b))
  statement: MapsTo f (Iic b) (Iic (f b))
  proof: fun _ _ => by aesop

中文:
引理 MonotoneOn.mapsTo_Iic
  条件: (h : MonotoneOn f (左无界右闭区间 b))
  结论: 映射到 f (左无界右闭区间 b) (左无界右闭区间 (f b))
  证明: fun _ _ => by aesop
-/
lemma MonotoneOn.mapsTo_Iic (h : MonotoneOn f (Iic b)) : MapsTo f (Iic b) (Iic (f b)) :=
  fun _ _ => by aesop

/--
lemma `MonotoneOn.mapsTo_Icc` / 引理 `MonotoneOn.mapsTo_Icc`

English:
lemma MonotoneOn.mapsTo_Icc
  given: (h : MonotoneOn f (Icc a b))
  statement: MapsTo f (Icc a b) (Icc (f a) (f b))
  proof: fun _c hc =>
    ⟨h (left_mem_Icc.2 <| hc.1.trans hc.2) hc hc.1, h hc (right_mem_Icc.2 <| hc.1.trans hc.2) hc.2⟩

中文:
引理 MonotoneOn.mapsTo_Icc
  条件: (h : MonotoneOn f (闭区间 a b))
  结论: 映射到 f (闭区间 a b) (闭区间 (f a) (f b))
  证明: fun _c hc =>
    ⟨h (left_mem_Icc.2 <| hc.1.trans hc.2) hc hc.1, h hc (right_mem_Icc.2 <| hc.1.trans hc.2) hc.2⟩

Depends on / 依赖: left_mem_Icc, right_mem_Icc
-/
lemma MonotoneOn.mapsTo_Icc (h : MonotoneOn f (Icc a b)) : MapsTo f (Icc a b) (Icc (f a) (f b)) :=
  fun _c hc =>
    ⟨h (left_mem_Icc.2 <| hc.1.trans hc.2) hc hc.1, h hc (right_mem_Icc.2 <| hc.1.trans hc.2) hc.2⟩

/--
lemma `AntitoneOn.mapsTo_Ici` / 引理 `AntitoneOn.mapsTo_Ici`

English:
lemma AntitoneOn.mapsTo_Ici
  given: (h : AntitoneOn f (Ici a))
  statement: MapsTo f (Ici a) (Iic (f a))
  proof: fun _ _ => by aesop

中文:
引理 AntitoneOn.mapsTo_Ici
  条件: (h : AntitoneOn f (左闭右无界区间 a))
  结论: 映射到 f (左闭右无界区间 a) (左无界右闭区间 (f a))
  证明: fun _ _ => by aesop
-/
lemma AntitoneOn.mapsTo_Ici (h : AntitoneOn f (Ici a)) : MapsTo f (Ici a) (Iic (f a)) :=
  fun _ _ => by aesop

/--
lemma `AntitoneOn.mapsTo_Iic` / 引理 `AntitoneOn.mapsTo_Iic`

English:
lemma AntitoneOn.mapsTo_Iic
  given: (h : AntitoneOn f (Iic b))
  statement: MapsTo f (Iic b) (Ici (f b))
  proof: fun _ _ => by aesop

中文:
引理 AntitoneOn.mapsTo_Iic
  条件: (h : AntitoneOn f (左无界右闭区间 b))
  结论: 映射到 f (左无界右闭区间 b) (左闭右无界区间 (f b))
  证明: fun _ _ => by aesop
-/
lemma AntitoneOn.mapsTo_Iic (h : AntitoneOn f (Iic b)) : MapsTo f (Iic b) (Ici (f b)) :=
  fun _ _ => by aesop

/--
lemma `AntitoneOn.mapsTo_Icc` / 引理 `AntitoneOn.mapsTo_Icc`

English:
lemma AntitoneOn.mapsTo_Icc
  given: (h : AntitoneOn f (Icc a b))
  statement: MapsTo f (Icc a b) (Icc (f b) (f a))
  proof: fun _c hc =>
    ⟨h hc (right_mem_Icc.2 <| hc.1.trans hc.2) hc.2, h (left_mem_Icc.2 <| hc.1.trans hc.2) hc hc.1⟩

中文:
引理 AntitoneOn.mapsTo_Icc
  条件: (h : AntitoneOn f (闭区间 a b))
  结论: 映射到 f (闭区间 a b) (闭区间 (f b) (f a))
  证明: fun _c hc =>
    ⟨h hc (right_mem_Icc.2 <| hc.1.trans hc.2) hc.2, h (left_mem_Icc.2 <| hc.1.trans hc.2) hc hc.1⟩

Depends on / 依赖: left_mem_Icc, right_mem_Icc
-/
lemma AntitoneOn.mapsTo_Icc (h : AntitoneOn f (Icc a b)) : MapsTo f (Icc a b) (Icc (f b) (f a)) :=
  fun _c hc =>
    ⟨h hc (right_mem_Icc.2 <| hc.1.trans hc.2) hc.2, h (left_mem_Icc.2 <| hc.1.trans hc.2) hc hc.1⟩

/--
lemma `StrictMonoOn.mapsTo_Ioi` / 引理 `StrictMonoOn.mapsTo_Ioi`

English:
lemma StrictMonoOn.mapsTo_Ioi
  given: (h : StrictMonoOn f (Ici a))
  statement: MapsTo f (Ioi a) (Ioi (f a))
  proof: fun _c hc => h le_rfl hc.le hc

中文:
引理 StrictMonoOn.mapsTo_Ioi
  条件: (h : StrictMonoOn f (左闭右无界区间 a))
  结论: 映射到 f (左开右无界区间 a) (左开右无界区间 (f a))
  证明: fun _c hc => h le_rfl hc.le hc

Depends on / 依赖: hc.le, le_rfl
-/
lemma StrictMonoOn.mapsTo_Ioi (h : StrictMonoOn f (Ici a)) : MapsTo f (Ioi a) (Ioi (f a)) :=
  fun _c hc => h le_rfl hc.le hc

/--
lemma `StrictMonoOn.mapsTo_Iio` / 引理 `StrictMonoOn.mapsTo_Iio`

English:
lemma StrictMonoOn.mapsTo_Iio
  given: (h : StrictMonoOn f (Iic b))
  statement: MapsTo f (Iio b) (Iio (f b))
  proof: fun _c hc => h hc.le le_rfl hc

中文:
引理 StrictMonoOn.mapsTo_Iio
  条件: (h : StrictMonoOn f (左无界右闭区间 b))
  结论: 映射到 f (左无界右开区间 b) (左无界右开区间 (f b))
  证明: fun _c hc => h hc.le le_rfl hc

Depends on / 依赖: hc.le, le_rfl
-/
lemma StrictMonoOn.mapsTo_Iio (h : StrictMonoOn f (Iic b)) : MapsTo f (Iio b) (Iio (f b)) :=
  fun _c hc => h hc.le le_rfl hc

/--
lemma `StrictMonoOn.mapsTo_Ioo` / 引理 `StrictMonoOn.mapsTo_Ioo`

English:
lemma StrictMonoOn.mapsTo_Ioo
  given: (h : StrictMonoOn f (Icc a b))
  proof: fun _c hc =>
    ⟨h (left_mem_Icc.2 (hc.1.trans hc.2).le) (Ioo_subset_Icc_self hc) hc.1,
     h (Ioo_subset_Icc_self hc) (right_mem_Icc.2 (hc.1.trans hc.2).le) hc.2⟩

中文:
引理 StrictMonoOn.mapsTo_Ioo
  条件: (h : StrictMonoOn f (闭区间 a b))
  证明: fun _c hc =>
    ⟨h (left_mem_Icc.2 (hc.1.trans hc.2).le) (Ioo_subset_Icc_self hc) hc.1,
     h (Ioo_subset_Icc_self hc) (right_mem_Icc.2 (hc.1.trans hc.2).le) hc.2⟩

Depends on / 依赖: Ioo_subset_Icc_self, left_mem_Icc, right_mem_Icc
-/
lemma StrictMonoOn.mapsTo_Ioo (h : StrictMonoOn f (Icc a b)) :
    MapsTo f (Ioo a b) (Ioo (f a) (f b)) :=
  fun _c hc =>
    ⟨h (left_mem_Icc.2 (hc.1.trans hc.2).le) (Ioo_subset_Icc_self hc) hc.1,
     h (Ioo_subset_Icc_self hc) (right_mem_Icc.2 (hc.1.trans hc.2).le) hc.2⟩

/--
lemma `StrictAntiOn.mapsTo_Ioi` / 引理 `StrictAntiOn.mapsTo_Ioi`

English:
lemma StrictAntiOn.mapsTo_Ioi
  given: (h : StrictAntiOn f (Ici a))
  statement: MapsTo f (Ioi a) (Iio (f a))
  proof: fun _c hc => h le_rfl hc.le hc

中文:
引理 StrictAntiOn.mapsTo_Ioi
  条件: (h : StrictAntiOn f (左闭右无界区间 a))
  结论: 映射到 f (左开右无界区间 a) (左无界右开区间 (f a))
  证明: fun _c hc => h le_rfl hc.le hc

Depends on / 依赖: hc.le, le_rfl
-/
lemma StrictAntiOn.mapsTo_Ioi (h : StrictAntiOn f (Ici a)) : MapsTo f (Ioi a) (Iio (f a)) :=
  fun _c hc => h le_rfl hc.le hc

/--
lemma `StrictAntiOn.mapsTo_Iio` / 引理 `StrictAntiOn.mapsTo_Iio`

English:
lemma StrictAntiOn.mapsTo_Iio
  given: (h : StrictAntiOn f (Iic b))
  statement: MapsTo f (Iio b) (Ioi (f b))
  proof: fun _c hc => h hc.le le_rfl hc

中文:
引理 StrictAntiOn.mapsTo_Iio
  条件: (h : StrictAntiOn f (左无界右闭区间 b))
  结论: 映射到 f (左无界右开区间 b) (左开右无界区间 (f b))
  证明: fun _c hc => h hc.le le_rfl hc

Depends on / 依赖: hc.le, le_rfl
-/
lemma StrictAntiOn.mapsTo_Iio (h : StrictAntiOn f (Iic b)) : MapsTo f (Iio b) (Ioi (f b)) :=
  fun _c hc => h hc.le le_rfl hc

/--
lemma `StrictAntiOn.mapsTo_Ioo` / 引理 `StrictAntiOn.mapsTo_Ioo`

English:
lemma StrictAntiOn.mapsTo_Ioo
  given: (h : StrictAntiOn f (Icc a b))
  proof: fun _c hc =>
    ⟨h (Ioo_subset_Icc_self hc) (right_mem_Icc.2 (hc.1.trans hc.2).le) hc.2,
     h (left_mem_Icc.2 (hc.1.trans hc.2).le) (Ioo_subset_Icc_self hc) hc.1⟩

中文:
引理 StrictAntiOn.mapsTo_Ioo
  条件: (h : StrictAntiOn f (闭区间 a b))
  证明: fun _c hc =>
    ⟨h (Ioo_subset_Icc_self hc) (right_mem_Icc.2 (hc.1.trans hc.2).le) hc.2,
     h (left_mem_Icc.2 (hc.1.trans hc.2).le) (Ioo_subset_Icc_self hc) hc.1⟩

Depends on / 依赖: Ioo_subset_Icc_self, left_mem_Icc, right_mem_Icc
-/
lemma StrictAntiOn.mapsTo_Ioo (h : StrictAntiOn f (Icc a b)) :
    MapsTo f (Ioo a b) (Ioo (f b) (f a)) :=
  fun _c hc =>
    ⟨h (Ioo_subset_Icc_self hc) (right_mem_Icc.2 (hc.1.trans hc.2).le) hc.2,
     h (left_mem_Icc.2 (hc.1.trans hc.2).le) (Ioo_subset_Icc_self hc) hc.1⟩

/--
lemma `Monotone.mapsTo_Ici` / 引理 `Monotone.mapsTo_Ici`

English:
lemma Monotone.mapsTo_Ici
  given: (h : Monotone f)
  statement: MapsTo f (Ici a) (Ici (f a))
  proof: (h.monotoneOn _).mapsTo_Ici

中文:
引理 递增.mapsTo_Ici
  条件: (h : 递增 f)
  结论: 映射到 f (左闭右无界区间 a) (左闭右无界区间 (f a))
  证明: (h.monotoneOn _).mapsTo_Ici

Depends on / 依赖: h.monotoneOn, mapsTo_Ici, monotoneOn
-/
lemma Monotone.mapsTo_Ici (h : Monotone f) : MapsTo f (Ici a) (Ici (f a)) :=
  (h.monotoneOn _).mapsTo_Ici

/--
lemma `Monotone.mapsTo_Iic` / 引理 `Monotone.mapsTo_Iic`

English:
lemma Monotone.mapsTo_Iic
  given: (h : Monotone f)
  statement: MapsTo f (Iic b) (Iic (f b))
  proof: (h.monotoneOn _).mapsTo_Iic

中文:
引理 递增.mapsTo_Iic
  条件: (h : 递增 f)
  结论: 映射到 f (左无界右闭区间 b) (左无界右闭区间 (f b))
  证明: (h.monotoneOn _).mapsTo_Iic

Depends on / 依赖: h.monotoneOn, mapsTo_Iic, monotoneOn
-/
lemma Monotone.mapsTo_Iic (h : Monotone f) : MapsTo f (Iic b) (Iic (f b)) :=
  (h.monotoneOn _).mapsTo_Iic

/--
lemma `Monotone.mapsTo_Icc` / 引理 `Monotone.mapsTo_Icc`

English:
lemma Monotone.mapsTo_Icc
  given: (h : Monotone f)
  statement: MapsTo f (Icc a b) (Icc (f a) (f b))
  proof: (h.monotoneOn _).mapsTo_Icc

中文:
引理 递增.mapsTo_Icc
  条件: (h : 递增 f)
  结论: 映射到 f (闭区间 a b) (闭区间 (f a) (f b))
  证明: (h.monotoneOn _).mapsTo_Icc

Depends on / 依赖: h.monotoneOn, mapsTo_Icc, monotoneOn
-/
lemma Monotone.mapsTo_Icc (h : Monotone f) : MapsTo f (Icc a b) (Icc (f a) (f b)) :=
  (h.monotoneOn _).mapsTo_Icc

/--
lemma `Antitone.mapsTo_Ici` / 引理 `Antitone.mapsTo_Ici`

English:
lemma Antitone.mapsTo_Ici
  given: (h : Antitone f)
  statement: MapsTo f (Ici a) (Iic (f a))
  proof: (h.antitoneOn _).mapsTo_Ici

中文:
引理 递减.mapsTo_Ici
  条件: (h : 递减 f)
  结论: 映射到 f (左闭右无界区间 a) (左无界右闭区间 (f a))
  证明: (h.antitoneOn _).mapsTo_Ici

Depends on / 依赖: antitoneOn, h.antitoneOn, mapsTo_Ici
-/
lemma Antitone.mapsTo_Ici (h : Antitone f) : MapsTo f (Ici a) (Iic (f a)) :=
  (h.antitoneOn _).mapsTo_Ici

/--
lemma `Antitone.mapsTo_Iic` / 引理 `Antitone.mapsTo_Iic`

English:
lemma Antitone.mapsTo_Iic
  given: (h : Antitone f)
  statement: MapsTo f (Iic b) (Ici (f b))
  proof: (h.antitoneOn _).mapsTo_Iic

中文:
引理 递减.mapsTo_Iic
  条件: (h : 递减 f)
  结论: 映射到 f (左无界右闭区间 b) (左闭右无界区间 (f b))
  证明: (h.antitoneOn _).mapsTo_Iic

Depends on / 依赖: antitoneOn, h.antitoneOn, mapsTo_Iic
-/
lemma Antitone.mapsTo_Iic (h : Antitone f) : MapsTo f (Iic b) (Ici (f b)) :=
  (h.antitoneOn _).mapsTo_Iic

/--
lemma `Antitone.mapsTo_Icc` / 引理 `Antitone.mapsTo_Icc`

English:
lemma Antitone.mapsTo_Icc
  given: (h : Antitone f)
  statement: MapsTo f (Icc a b) (Icc (f b) (f a))
  proof: (h.antitoneOn _).mapsTo_Icc

中文:
引理 递减.mapsTo_Icc
  条件: (h : 递减 f)
  结论: 映射到 f (闭区间 a b) (闭区间 (f b) (f a))
  证明: (h.antitoneOn _).mapsTo_Icc

Depends on / 依赖: antitoneOn, h.antitoneOn, mapsTo_Icc
-/
lemma Antitone.mapsTo_Icc (h : Antitone f) : MapsTo f (Icc a b) (Icc (f b) (f a)) :=
  (h.antitoneOn _).mapsTo_Icc

/--
lemma `StrictMono.mapsTo_Ioi` / 引理 `StrictMono.mapsTo_Ioi`

English:
lemma StrictMono.mapsTo_Ioi
  given: (h : StrictMono f)
  statement: MapsTo f (Ioi a) (Ioi (f a))
  proof: (h.strictMonoOn _).mapsTo_Ioi

中文:
引理 严格递增.mapsTo_Ioi
  条件: (h : 严格递增 f)
  结论: 映射到 f (左开右无界区间 a) (左开右无界区间 (f a))
  证明: (h.strictMonoOn _).mapsTo_Ioi

Depends on / 依赖: h.strictMonoOn, mapsTo_Ioi, strictMonoOn
-/
lemma StrictMono.mapsTo_Ioi (h : StrictMono f) : MapsTo f (Ioi a) (Ioi (f a)) :=
  (h.strictMonoOn _).mapsTo_Ioi

/--
lemma `StrictMono.mapsTo_Iio` / 引理 `StrictMono.mapsTo_Iio`

English:
lemma StrictMono.mapsTo_Iio
  given: (h : StrictMono f)
  statement: MapsTo f (Iio b) (Iio (f b))
  proof: (h.strictMonoOn _).mapsTo_Iio

中文:
引理 严格递增.mapsTo_Iio
  条件: (h : 严格递增 f)
  结论: 映射到 f (左无界右开区间 b) (左无界右开区间 (f b))
  证明: (h.strictMonoOn _).mapsTo_Iio

Depends on / 依赖: h.strictMonoOn, mapsTo_Iio, strictMonoOn
-/
lemma StrictMono.mapsTo_Iio (h : StrictMono f) : MapsTo f (Iio b) (Iio (f b)) :=
  (h.strictMonoOn _).mapsTo_Iio

/--
lemma `StrictMono.mapsTo_Ioo` / 引理 `StrictMono.mapsTo_Ioo`

English:
lemma StrictMono.mapsTo_Ioo
  given: (h : StrictMono f)
  statement: MapsTo f (Ioo a b) (Ioo (f a) (f b))
  proof: (h.strictMonoOn _).mapsTo_Ioo

中文:
引理 严格递增.mapsTo_Ioo
  条件: (h : 严格递增 f)
  结论: 映射到 f (开区间 a b) (开区间 (f a) (f b))
  证明: (h.strictMonoOn _).mapsTo_Ioo

Depends on / 依赖: h.strictMonoOn, mapsTo_Ioo, strictMonoOn
-/
lemma StrictMono.mapsTo_Ioo (h : StrictMono f) : MapsTo f (Ioo a b) (Ioo (f a) (f b)) :=
  (h.strictMonoOn _).mapsTo_Ioo

/--
lemma `StrictAnti.mapsTo_Ioi` / 引理 `StrictAnti.mapsTo_Ioi`

English:
lemma StrictAnti.mapsTo_Ioi
  given: (h : StrictAnti f)
  statement: MapsTo f (Ioi a) (Iio (f a))
  proof: (h.strictAntiOn _).mapsTo_Ioi

中文:
引理 严格递减.mapsTo_Ioi
  条件: (h : 严格递减 f)
  结论: 映射到 f (左开右无界区间 a) (左无界右开区间 (f a))
  证明: (h.strictAntiOn _).mapsTo_Ioi

Depends on / 依赖: h.strictAntiOn, mapsTo_Ioi, strictAntiOn
-/
lemma StrictAnti.mapsTo_Ioi (h : StrictAnti f) : MapsTo f (Ioi a) (Iio (f a)) :=
  (h.strictAntiOn _).mapsTo_Ioi

/--
lemma `StrictAnti.mapsTo_Iio` / 引理 `StrictAnti.mapsTo_Iio`

English:
lemma StrictAnti.mapsTo_Iio
  given: (h : StrictAnti f)
  statement: MapsTo f (Iio b) (Ioi (f b))
  proof: (h.strictAntiOn _).mapsTo_Iio

中文:
引理 严格递减.mapsTo_Iio
  条件: (h : 严格递减 f)
  结论: 映射到 f (左无界右开区间 b) (左开右无界区间 (f b))
  证明: (h.strictAntiOn _).mapsTo_Iio

Depends on / 依赖: h.strictAntiOn, mapsTo_Iio, strictAntiOn
-/
lemma StrictAnti.mapsTo_Iio (h : StrictAnti f) : MapsTo f (Iio b) (Ioi (f b)) :=
  (h.strictAntiOn _).mapsTo_Iio

/--
lemma `StrictAnti.mapsTo_Ioo` / 引理 `StrictAnti.mapsTo_Ioo`

English:
lemma StrictAnti.mapsTo_Ioo
  given: (h : StrictAnti f)
  statement: MapsTo f (Ioo a b) (Ioo (f b) (f a))
  proof: (h.strictAntiOn _).mapsTo_Ioo

中文:
引理 严格递减.mapsTo_Ioo
  条件: (h : 严格递减 f)
  结论: 映射到 f (开区间 a b) (开区间 (f b) (f a))
  证明: (h.strictAntiOn _).mapsTo_Ioo

Depends on / 依赖: h.strictAntiOn, mapsTo_Ioo, strictAntiOn
-/
lemma StrictAnti.mapsTo_Ioo (h : StrictAnti f) : MapsTo f (Ioo a b) (Ioo (f b) (f a)) :=
  (h.strictAntiOn _).mapsTo_Ioo

/--
lemma `MonotoneOn.image_Ici_subset` / 引理 `MonotoneOn.image_Ici_subset`

English:
lemma MonotoneOn.image_Ici_subset
  given: (h : MonotoneOn f (Ici a))
  statement: f '' Ici a subseteq Ici (f a)
  proof: h.mapsTo_Ici.image_subset

中文:
引理 MonotoneOn.image_Ici_subset
  条件: (h : MonotoneOn f (左闭右无界区间 a))
  结论: f '' 左闭右无界区间 a subseteq 左闭右无界区间 (f a)
  证明: h.mapsTo_Ici.image_subset

Depends on / 依赖: h.mapsTo_Ici.image_subset, image_subset, mapsTo_Ici
-/
lemma MonotoneOn.image_Ici_subset (h : MonotoneOn f (Ici a)) : f '' Ici a subseteq Ici (f a) :=
  h.mapsTo_Ici.image_subset

/--
lemma `MonotoneOn.image_Iic_subset` / 引理 `MonotoneOn.image_Iic_subset`

English:
lemma MonotoneOn.image_Iic_subset
  given: (h : MonotoneOn f (Iic b))
  statement: f '' Iic b subseteq Iic (f b)
  proof: h.mapsTo_Iic.image_subset

中文:
引理 MonotoneOn.image_Iic_subset
  条件: (h : MonotoneOn f (左无界右闭区间 b))
  结论: f '' 左无界右闭区间 b subseteq 左无界右闭区间 (f b)
  证明: h.mapsTo_Iic.image_subset

Depends on / 依赖: h.mapsTo_Iic.image_subset, image_subset, mapsTo_Iic
-/
lemma MonotoneOn.image_Iic_subset (h : MonotoneOn f (Iic b)) : f '' Iic b subseteq Iic (f b) :=
  h.mapsTo_Iic.image_subset

/--
lemma `MonotoneOn.image_Icc_subset` / 引理 `MonotoneOn.image_Icc_subset`

English:
lemma MonotoneOn.image_Icc_subset
  given: (h : MonotoneOn f (Icc a b))
  statement: f '' Icc a b subseteq Icc (f a) (f b)
  proof: h.mapsTo_Icc.image_subset

中文:
引理 MonotoneOn.image_Icc_subset
  条件: (h : MonotoneOn f (闭区间 a b))
  结论: f '' 闭区间 a b subseteq 闭区间 (f a) (f b)
  证明: h.mapsTo_Icc.image_subset

Depends on / 依赖: h.mapsTo_Icc.image_subset, image_subset, mapsTo_Icc
-/
lemma MonotoneOn.image_Icc_subset (h : MonotoneOn f (Icc a b)) : f '' Icc a b subseteq Icc (f a) (f b) :=
  h.mapsTo_Icc.image_subset

/--
lemma `AntitoneOn.image_Ici_subset` / 引理 `AntitoneOn.image_Ici_subset`

English:
lemma AntitoneOn.image_Ici_subset
  given: (h : AntitoneOn f (Ici a))
  statement: f '' Ici a subseteq Iic (f a)
  proof: h.mapsTo_Ici.image_subset

中文:
引理 AntitoneOn.image_Ici_subset
  条件: (h : AntitoneOn f (左闭右无界区间 a))
  结论: f '' 左闭右无界区间 a subseteq 左无界右闭区间 (f a)
  证明: h.mapsTo_Ici.image_subset

Depends on / 依赖: h.mapsTo_Ici.image_subset, image_subset, mapsTo_Ici
-/
lemma AntitoneOn.image_Ici_subset (h : AntitoneOn f (Ici a)) : f '' Ici a subseteq Iic (f a) :=
  h.mapsTo_Ici.image_subset

/--
lemma `AntitoneOn.image_Iic_subset` / 引理 `AntitoneOn.image_Iic_subset`

English:
lemma AntitoneOn.image_Iic_subset
  given: (h : AntitoneOn f (Iic b))
  statement: f '' Iic b subseteq Ici (f b)
  proof: h.mapsTo_Iic.image_subset

中文:
引理 AntitoneOn.image_Iic_subset
  条件: (h : AntitoneOn f (左无界右闭区间 b))
  结论: f '' 左无界右闭区间 b subseteq 左闭右无界区间 (f b)
  证明: h.mapsTo_Iic.image_subset

Depends on / 依赖: h.mapsTo_Iic.image_subset, image_subset, mapsTo_Iic
-/
lemma AntitoneOn.image_Iic_subset (h : AntitoneOn f (Iic b)) : f '' Iic b subseteq Ici (f b) :=
  h.mapsTo_Iic.image_subset

/--
lemma `AntitoneOn.image_Icc_subset` / 引理 `AntitoneOn.image_Icc_subset`

English:
lemma AntitoneOn.image_Icc_subset
  given: (h : AntitoneOn f (Icc a b))
  statement: f '' Icc a b subseteq Icc (f b) (f a)
  proof: h.mapsTo_Icc.image_subset

中文:
引理 AntitoneOn.image_Icc_subset
  条件: (h : AntitoneOn f (闭区间 a b))
  结论: f '' 闭区间 a b subseteq 闭区间 (f b) (f a)
  证明: h.mapsTo_Icc.image_subset

Depends on / 依赖: h.mapsTo_Icc.image_subset, image_subset, mapsTo_Icc
-/
lemma AntitoneOn.image_Icc_subset (h : AntitoneOn f (Icc a b)) : f '' Icc a b subseteq Icc (f b) (f a) :=
  h.mapsTo_Icc.image_subset

/--
lemma `StrictMonoOn.image_Ioi_subset` / 引理 `StrictMonoOn.image_Ioi_subset`

English:
lemma StrictMonoOn.image_Ioi_subset
  given: (h : StrictMonoOn f (Ici a))
  statement: f '' Ioi a subseteq Ioi (f a)
  proof: h.mapsTo_Ioi.image_subset

中文:
引理 StrictMonoOn.image_Ioi_subset
  条件: (h : StrictMonoOn f (左闭右无界区间 a))
  结论: f '' 左开右无界区间 a subseteq 左开右无界区间 (f a)
  证明: h.mapsTo_Ioi.image_subset

Depends on / 依赖: h.mapsTo_Ioi.image_subset, image_subset, mapsTo_Ioi
-/
lemma StrictMonoOn.image_Ioi_subset (h : StrictMonoOn f (Ici a)) : f '' Ioi a subseteq Ioi (f a) :=
  h.mapsTo_Ioi.image_subset

/--
lemma `StrictMonoOn.image_Iio_subset` / 引理 `StrictMonoOn.image_Iio_subset`

English:
lemma StrictMonoOn.image_Iio_subset
  given: (h : StrictMonoOn f (Iic b))
  statement: f '' Iio b subseteq Iio (f b)
  proof: h.mapsTo_Iio.image_subset

中文:
引理 StrictMonoOn.image_Iio_subset
  条件: (h : StrictMonoOn f (左无界右闭区间 b))
  结论: f '' 左无界右开区间 b subseteq 左无界右开区间 (f b)
  证明: h.mapsTo_Iio.image_subset

Depends on / 依赖: h.mapsTo_Iio.image_subset, image_subset, mapsTo_Iio
-/
lemma StrictMonoOn.image_Iio_subset (h : StrictMonoOn f (Iic b)) : f '' Iio b subseteq Iio (f b) :=
  h.mapsTo_Iio.image_subset

/--
lemma `StrictMonoOn.image_Ioo_subset` / 引理 `StrictMonoOn.image_Ioo_subset`

English:
lemma StrictMonoOn.image_Ioo_subset
  given: (h : StrictMonoOn f (Icc a b))
  proof: h.mapsTo_Ioo.image_subset

中文:
引理 StrictMonoOn.image_Ioo_subset
  条件: (h : StrictMonoOn f (闭区间 a b))
  证明: h.mapsTo_Ioo.image_subset

Depends on / 依赖: h.mapsTo_Ioo.image_subset, image_subset, mapsTo_Ioo
-/
lemma StrictMonoOn.image_Ioo_subset (h : StrictMonoOn f (Icc a b)) :
    f '' Ioo a b subseteq Ioo (f a) (f b) := h.mapsTo_Ioo.image_subset

/--
lemma `StrictAntiOn.image_Ioi_subset` / 引理 `StrictAntiOn.image_Ioi_subset`

English:
lemma StrictAntiOn.image_Ioi_subset
  given: (h : StrictAntiOn f (Ici a))
  statement: f '' Ioi a subseteq Iio (f a)
  proof: h.mapsTo_Ioi.image_subset

中文:
引理 StrictAntiOn.image_Ioi_subset
  条件: (h : StrictAntiOn f (左闭右无界区间 a))
  结论: f '' 左开右无界区间 a subseteq 左无界右开区间 (f a)
  证明: h.mapsTo_Ioi.image_subset

Depends on / 依赖: h.mapsTo_Ioi.image_subset, image_subset, mapsTo_Ioi
-/
lemma StrictAntiOn.image_Ioi_subset (h : StrictAntiOn f (Ici a)) : f '' Ioi a subseteq Iio (f a) :=
  h.mapsTo_Ioi.image_subset

/--
lemma `StrictAntiOn.image_Iio_subset` / 引理 `StrictAntiOn.image_Iio_subset`

English:
lemma StrictAntiOn.image_Iio_subset
  given: (h : StrictAntiOn f (Iic b))
  statement: f '' Iio b subseteq Ioi (f b)
  proof: h.mapsTo_Iio.image_subset

中文:
引理 StrictAntiOn.image_Iio_subset
  条件: (h : StrictAntiOn f (左无界右闭区间 b))
  结论: f '' 左无界右开区间 b subseteq 左开右无界区间 (f b)
  证明: h.mapsTo_Iio.image_subset

Depends on / 依赖: h.mapsTo_Iio.image_subset, image_subset, mapsTo_Iio
-/
lemma StrictAntiOn.image_Iio_subset (h : StrictAntiOn f (Iic b)) : f '' Iio b subseteq Ioi (f b) :=
  h.mapsTo_Iio.image_subset

/--
lemma `StrictAntiOn.image_Ioo_subset` / 引理 `StrictAntiOn.image_Ioo_subset`

English:
lemma StrictAntiOn.image_Ioo_subset
  given: (h : StrictAntiOn f (Icc a b))
  proof: h.mapsTo_Ioo.image_subset

中文:
引理 StrictAntiOn.image_Ioo_subset
  条件: (h : StrictAntiOn f (闭区间 a b))
  证明: h.mapsTo_Ioo.image_subset

Depends on / 依赖: h.mapsTo_Ioo.image_subset, image_subset, mapsTo_Ioo
-/
lemma StrictAntiOn.image_Ioo_subset (h : StrictAntiOn f (Icc a b)) :
    f '' Ioo a b subseteq Ioo (f b) (f a) := h.mapsTo_Ioo.image_subset

/--
lemma `Monotone.image_Ici_subset` / 引理 `Monotone.image_Ici_subset`

English:
lemma Monotone.image_Ici_subset
  given: (h : Monotone f)
  statement: f '' Ici a subseteq Ici (f a)
  proof: (h.monotoneOn _).image_Ici_subset

中文:
引理 递增.image_Ici_subset
  条件: (h : 递增 f)
  结论: f '' 左闭右无界区间 a subseteq 左闭右无界区间 (f a)
  证明: (h.monotoneOn _).image_Ici_subset

Depends on / 依赖: h.monotoneOn, image_Ici_subset, monotoneOn
-/
lemma Monotone.image_Ici_subset (h : Monotone f) : f '' Ici a subseteq Ici (f a) :=
  (h.monotoneOn _).image_Ici_subset

/--
lemma `Monotone.image_Iic_subset` / 引理 `Monotone.image_Iic_subset`

English:
lemma Monotone.image_Iic_subset
  given: (h : Monotone f)
  statement: f '' Iic b subseteq Iic (f b)
  proof: (h.monotoneOn _).image_Iic_subset

中文:
引理 递增.image_Iic_subset
  条件: (h : 递增 f)
  结论: f '' 左无界右闭区间 b subseteq 左无界右闭区间 (f b)
  证明: (h.monotoneOn _).image_Iic_subset

Depends on / 依赖: h.monotoneOn, image_Iic_subset, monotoneOn
-/
lemma Monotone.image_Iic_subset (h : Monotone f) : f '' Iic b subseteq Iic (f b) :=
  (h.monotoneOn _).image_Iic_subset

/--
lemma `Monotone.image_Icc_subset` / 引理 `Monotone.image_Icc_subset`

English:
lemma Monotone.image_Icc_subset
  given: (h : Monotone f)
  statement: f '' Icc a b subseteq Icc (f a) (f b)
  proof: (h.monotoneOn _).image_Icc_subset

中文:
引理 递增.image_Icc_subset
  条件: (h : 递增 f)
  结论: f '' 闭区间 a b subseteq 闭区间 (f a) (f b)
  证明: (h.monotoneOn _).image_Icc_subset

Depends on / 依赖: h.monotoneOn, image_Icc_subset, monotoneOn
-/
lemma Monotone.image_Icc_subset (h : Monotone f) : f '' Icc a b subseteq Icc (f a) (f b) :=
  (h.monotoneOn _).image_Icc_subset

/--
lemma `Antitone.image_Ici_subset` / 引理 `Antitone.image_Ici_subset`

English:
lemma Antitone.image_Ici_subset
  given: (h : Antitone f)
  statement: f '' Ici a subseteq Iic (f a)
  proof: (h.antitoneOn _).image_Ici_subset

中文:
引理 递减.image_Ici_subset
  条件: (h : 递减 f)
  结论: f '' 左闭右无界区间 a subseteq 左无界右闭区间 (f a)
  证明: (h.antitoneOn _).image_Ici_subset

Depends on / 依赖: antitoneOn, h.antitoneOn, image_Ici_subset
-/
lemma Antitone.image_Ici_subset (h : Antitone f) : f '' Ici a subseteq Iic (f a) :=
  (h.antitoneOn _).image_Ici_subset

/--
lemma `Antitone.image_Iic_subset` / 引理 `Antitone.image_Iic_subset`

English:
lemma Antitone.image_Iic_subset
  given: (h : Antitone f)
  statement: f '' Iic b subseteq Ici (f b)
  proof: (h.antitoneOn _).image_Iic_subset

中文:
引理 递减.image_Iic_subset
  条件: (h : 递减 f)
  结论: f '' 左无界右闭区间 b subseteq 左闭右无界区间 (f b)
  证明: (h.antitoneOn _).image_Iic_subset

Depends on / 依赖: antitoneOn, h.antitoneOn, image_Iic_subset
-/
lemma Antitone.image_Iic_subset (h : Antitone f) : f '' Iic b subseteq Ici (f b) :=
  (h.antitoneOn _).image_Iic_subset

/--
lemma `Antitone.image_Icc_subset` / 引理 `Antitone.image_Icc_subset`

English:
lemma Antitone.image_Icc_subset
  given: (h : Antitone f)
  statement: f '' Icc a b subseteq Icc (f b) (f a)
  proof: (h.antitoneOn _).image_Icc_subset

中文:
引理 递减.image_Icc_subset
  条件: (h : 递减 f)
  结论: f '' 闭区间 a b subseteq 闭区间 (f b) (f a)
  证明: (h.antitoneOn _).image_Icc_subset

Depends on / 依赖: antitoneOn, h.antitoneOn, image_Icc_subset
-/
lemma Antitone.image_Icc_subset (h : Antitone f) : f '' Icc a b subseteq Icc (f b) (f a) :=
  (h.antitoneOn _).image_Icc_subset

/--
lemma `StrictMono.image_Ioi_subset` / 引理 `StrictMono.image_Ioi_subset`

English:
lemma StrictMono.image_Ioi_subset
  given: (h : StrictMono f)
  statement: f '' Ioi a subseteq Ioi (f a)
  proof: (h.strictMonoOn _).image_Ioi_subset

中文:
引理 严格递增.image_Ioi_subset
  条件: (h : 严格递增 f)
  结论: f '' 左开右无界区间 a subseteq 左开右无界区间 (f a)
  证明: (h.strictMonoOn _).image_Ioi_subset

Depends on / 依赖: h.strictMonoOn, image_Ioi_subset, strictMonoOn
-/
lemma StrictMono.image_Ioi_subset (h : StrictMono f) : f '' Ioi a subseteq Ioi (f a) :=
  (h.strictMonoOn _).image_Ioi_subset

/--
lemma `StrictMono.image_Iio_subset` / 引理 `StrictMono.image_Iio_subset`

English:
lemma StrictMono.image_Iio_subset
  given: (h : StrictMono f)
  statement: f '' Iio b subseteq Iio (f b)
  proof: (h.strictMonoOn _).image_Iio_subset

中文:
引理 严格递增.image_Iio_subset
  条件: (h : 严格递增 f)
  结论: f '' 左无界右开区间 b subseteq 左无界右开区间 (f b)
  证明: (h.strictMonoOn _).image_Iio_subset

Depends on / 依赖: h.strictMonoOn, image_Iio_subset, strictMonoOn
-/
lemma StrictMono.image_Iio_subset (h : StrictMono f) : f '' Iio b subseteq Iio (f b) :=
  (h.strictMonoOn _).image_Iio_subset

/--
lemma `StrictMono.image_Ioo_subset` / 引理 `StrictMono.image_Ioo_subset`

English:
lemma StrictMono.image_Ioo_subset
  given: (h : StrictMono f)
  statement: f '' Ioo a b subseteq Ioo (f a) (f b)
  proof: (h.strictMonoOn _).image_Ioo_subset

中文:
引理 严格递增.image_Ioo_subset
  条件: (h : 严格递增 f)
  结论: f '' 开区间 a b subseteq 开区间 (f a) (f b)
  证明: (h.strictMonoOn _).image_Ioo_subset

Depends on / 依赖: h.strictMonoOn, image_Ioo_subset, strictMonoOn
-/
lemma StrictMono.image_Ioo_subset (h : StrictMono f) : f '' Ioo a b subseteq Ioo (f a) (f b) :=
  (h.strictMonoOn _).image_Ioo_subset

/--
lemma `StrictAnti.image_Ioi_subset` / 引理 `StrictAnti.image_Ioi_subset`

English:
lemma StrictAnti.image_Ioi_subset
  given: (h : StrictAnti f)
  statement: f '' Ioi a subseteq Iio (f a)
  proof: (h.strictAntiOn _).image_Ioi_subset

中文:
引理 严格递减.image_Ioi_subset
  条件: (h : 严格递减 f)
  结论: f '' 左开右无界区间 a subseteq 左无界右开区间 (f a)
  证明: (h.strictAntiOn _).image_Ioi_subset

Depends on / 依赖: h.strictAntiOn, image_Ioi_subset, strictAntiOn
-/
lemma StrictAnti.image_Ioi_subset (h : StrictAnti f) : f '' Ioi a subseteq Iio (f a) :=
  (h.strictAntiOn _).image_Ioi_subset

/--
lemma `StrictAnti.image_Iio_subset` / 引理 `StrictAnti.image_Iio_subset`

English:
lemma StrictAnti.image_Iio_subset
  given: (h : StrictAnti f)
  statement: f '' Iio b subseteq Ioi (f b)
  proof: (h.strictAntiOn _).image_Iio_subset

中文:
引理 严格递减.image_Iio_subset
  条件: (h : 严格递减 f)
  结论: f '' 左无界右开区间 b subseteq 左开右无界区间 (f b)
  证明: (h.strictAntiOn _).image_Iio_subset

Depends on / 依赖: h.strictAntiOn, image_Iio_subset, strictAntiOn
-/
lemma StrictAnti.image_Iio_subset (h : StrictAnti f) : f '' Iio b subseteq Ioi (f b) :=
  (h.strictAntiOn _).image_Iio_subset

/--
lemma `StrictAnti.image_Ioo_subset` / 引理 `StrictAnti.image_Ioo_subset`

English:
lemma StrictAnti.image_Ioo_subset
  given: (h : StrictAnti f)
  statement: f '' Ioo a b subseteq Ioo (f b) (f a)
  proof: (h.strictAntiOn _).image_Ioo_subset

中文:
引理 严格递减.image_Ioo_subset
  条件: (h : 严格递减 f)
  结论: f '' 开区间 a b subseteq 开区间 (f b) (f a)
  证明: (h.strictAntiOn _).image_Ioo_subset

Depends on / 依赖: h.strictAntiOn, image_Ioo_subset, strictAntiOn
-/
lemma StrictAnti.image_Ioo_subset (h : StrictAnti f) : f '' Ioo a b subseteq Ioo (f b) (f a) :=
  (h.strictAntiOn _).image_Ioo_subset

end Preorder

section PartialOrder
variable [PartialOrder α] [Preorder β] {a b : α}

/--
lemma `StrictMonoOn.mapsTo_Ico` / 引理 `StrictMonoOn.mapsTo_Ico`

English:
lemma StrictMonoOn.mapsTo_Ico
  given: (h : StrictMonoOn f (Icc a b))
  proof: fun _c hc => ⟨h.monotoneOn (left_mem_Icc.2 <| hc.1.trans hc.2.le) (Ico_subset_Icc_self hc) hc.1,
    h (Ico_subset_Icc_self hc) (right_mem_Icc.2 <| hc.1.trans hc.2.le) hc.2⟩

中文:
引理 StrictMonoOn.mapsTo_Ico
  条件: (h : StrictMonoOn f (闭区间 a b))
  证明: fun _c hc => ⟨h.monotoneOn (left_mem_Icc.2 <| hc.1.trans hc.2.le) (Ico_subset_Icc_self hc) hc.1,
    h (Ico_subset_Icc_self hc) (right_mem_Icc.2 <| hc.1.trans hc.2.le) hc.2⟩

Depends on / 依赖: Ico_subset_Icc_self, h.monotoneOn, left_mem_Icc, monotoneOn, right_mem_Icc
-/
lemma StrictMonoOn.mapsTo_Ico (h : StrictMonoOn f (Icc a b)) :
    MapsTo f (Ico a b) (Ico (f a) (f b)) :=
  fun _c hc => ⟨h.monotoneOn (left_mem_Icc.2 <| hc.1.trans hc.2.le) (Ico_subset_Icc_self hc) hc.1,
    h (Ico_subset_Icc_self hc) (right_mem_Icc.2 <| hc.1.trans hc.2.le) hc.2⟩

/--
lemma `StrictMonoOn.mapsTo_Ioc` / 引理 `StrictMonoOn.mapsTo_Ioc`

English:
lemma StrictMonoOn.mapsTo_Ioc
  given: (h : StrictMonoOn f (Icc a b))
  proof: fun _c hc => ⟨h (left_mem_Icc.2 <| hc.1.le.trans hc.2) (Ioc_subset_Icc_self hc) hc.1,
    h.monotoneOn (Ioc_subset_Icc_self hc) (right_mem_Icc.2 <| hc.1.le.trans hc.2) hc.2⟩

中文:
引理 StrictMonoOn.mapsTo_Ioc
  条件: (h : StrictMonoOn f (闭区间 a b))
  证明: fun _c hc => ⟨h (left_mem_Icc.2 <| hc.1.le.trans hc.2) (Ioc_subset_Icc_self hc) hc.1,
    h.monotoneOn (Ioc_subset_Icc_self hc) (right_mem_Icc.2 <| hc.1.le.trans hc.2) hc.2⟩

Depends on / 依赖: Ioc_subset_Icc_self, h.monotoneOn, le.trans, left_mem_Icc, monotoneOn, right_mem_Icc
-/
lemma StrictMonoOn.mapsTo_Ioc (h : StrictMonoOn f (Icc a b)) :
    MapsTo f (Ioc a b) (Ioc (f a) (f b)) :=
  fun _c hc => ⟨h (left_mem_Icc.2 <| hc.1.le.trans hc.2) (Ioc_subset_Icc_self hc) hc.1,
    h.monotoneOn (Ioc_subset_Icc_self hc) (right_mem_Icc.2 <| hc.1.le.trans hc.2) hc.2⟩

/--
lemma `StrictAntiOn.mapsTo_Ico` / 引理 `StrictAntiOn.mapsTo_Ico`

English:
lemma StrictAntiOn.mapsTo_Ico
  given: (h : StrictAntiOn f (Icc a b))
  proof: fun _c hc => ⟨h (Ico_subset_Icc_self hc) (right_mem_Icc.2 <| hc.1.trans hc.2.le) hc.2,
    h.antitoneOn (left_mem_Icc.2 <| hc.1.trans hc.2.le) (Ico_subset_Icc_self hc) hc.1⟩

中文:
引理 StrictAntiOn.mapsTo_Ico
  条件: (h : StrictAntiOn f (闭区间 a b))
  证明: fun _c hc => ⟨h (Ico_subset_Icc_self hc) (right_mem_Icc.2 <| hc.1.trans hc.2.le) hc.2,
    h.antitoneOn (left_mem_Icc.2 <| hc.1.trans hc.2.le) (Ico_subset_Icc_self hc) hc.1⟩

Depends on / 依赖: Ico_subset_Icc_self, antitoneOn, h.antitoneOn, left_mem_Icc, right_mem_Icc
-/
lemma StrictAntiOn.mapsTo_Ico (h : StrictAntiOn f (Icc a b)) :
    MapsTo f (Ico a b) (Ioc (f b) (f a)) :=
  fun _c hc => ⟨h (Ico_subset_Icc_self hc) (right_mem_Icc.2 <| hc.1.trans hc.2.le) hc.2,
    h.antitoneOn (left_mem_Icc.2 <| hc.1.trans hc.2.le) (Ico_subset_Icc_self hc) hc.1⟩

/--
lemma `StrictAntiOn.mapsTo_Ioc` / 引理 `StrictAntiOn.mapsTo_Ioc`

English:
lemma StrictAntiOn.mapsTo_Ioc
  given: (h : StrictAntiOn f (Icc a b))
  proof: fun _c hc => ⟨h.antitoneOn (Ioc_subset_Icc_self hc) (right_mem_Icc.2 <| hc.1.le.trans hc.2) hc.2,
    h (left_mem_Icc.2 <| hc.1.le.trans hc.2) (Ioc_subset_Icc_self hc) hc.1⟩

中文:
引理 StrictAntiOn.mapsTo_Ioc
  条件: (h : StrictAntiOn f (闭区间 a b))
  证明: fun _c hc => ⟨h.antitoneOn (Ioc_subset_Icc_self hc) (right_mem_Icc.2 <| hc.1.le.trans hc.2) hc.2,
    h (left_mem_Icc.2 <| hc.1.le.trans hc.2) (Ioc_subset_Icc_self hc) hc.1⟩

Depends on / 依赖: Ioc_subset_Icc_self, antitoneOn, h.antitoneOn, le.trans, left_mem_Icc, right_mem_Icc
-/
lemma StrictAntiOn.mapsTo_Ioc (h : StrictAntiOn f (Icc a b)) :
    MapsTo f (Ioc a b) (Ico (f b) (f a)) :=
  fun _c hc => ⟨h.antitoneOn (Ioc_subset_Icc_self hc) (right_mem_Icc.2 <| hc.1.le.trans hc.2) hc.2,
    h (left_mem_Icc.2 <| hc.1.le.trans hc.2) (Ioc_subset_Icc_self hc) hc.1⟩

/--
lemma `StrictMono.mapsTo_Ico` / 引理 `StrictMono.mapsTo_Ico`

English:
lemma StrictMono.mapsTo_Ico
  given: (h : StrictMono f)
  statement: MapsTo f (Ico a b) (Ico (f a) (f b))
  proof: (h.strictMonoOn _).mapsTo_Ico

中文:
引理 严格递增.mapsTo_Ico
  条件: (h : 严格递增 f)
  结论: 映射到 f (左闭右开区间 a b) (左闭右开区间 (f a) (f b))
  证明: (h.strictMonoOn _).mapsTo_Ico

Depends on / 依赖: h.strictMonoOn, mapsTo_Ico, strictMonoOn
-/
lemma StrictMono.mapsTo_Ico (h : StrictMono f) : MapsTo f (Ico a b) (Ico (f a) (f b)) :=
  (h.strictMonoOn _).mapsTo_Ico

/--
lemma `StrictMono.mapsTo_Ioc` / 引理 `StrictMono.mapsTo_Ioc`

English:
lemma StrictMono.mapsTo_Ioc
  given: (h : StrictMono f)
  statement: MapsTo f (Ioc a b) (Ioc (f a) (f b))
  proof: (h.strictMonoOn _).mapsTo_Ioc

中文:
引理 严格递增.mapsTo_Ioc
  条件: (h : 严格递增 f)
  结论: 映射到 f (左开右闭区间 a b) (左开右闭区间 (f a) (f b))
  证明: (h.strictMonoOn _).mapsTo_Ioc

Depends on / 依赖: h.strictMonoOn, mapsTo_Ioc, strictMonoOn
-/
lemma StrictMono.mapsTo_Ioc (h : StrictMono f) : MapsTo f (Ioc a b) (Ioc (f a) (f b)) :=
  (h.strictMonoOn _).mapsTo_Ioc

/--
lemma `StrictAnti.mapsTo_Ico` / 引理 `StrictAnti.mapsTo_Ico`

English:
lemma StrictAnti.mapsTo_Ico
  given: (h : StrictAnti f)
  statement: MapsTo f (Ico a b) (Ioc (f b) (f a))
  proof: (h.strictAntiOn _).mapsTo_Ico

中文:
引理 严格递减.mapsTo_Ico
  条件: (h : 严格递减 f)
  结论: 映射到 f (左闭右开区间 a b) (左开右闭区间 (f b) (f a))
  证明: (h.strictAntiOn _).mapsTo_Ico

Depends on / 依赖: h.strictAntiOn, mapsTo_Ico, strictAntiOn
-/
lemma StrictAnti.mapsTo_Ico (h : StrictAnti f) : MapsTo f (Ico a b) (Ioc (f b) (f a)) :=
  (h.strictAntiOn _).mapsTo_Ico

/--
lemma `StrictAnti.mapsTo_Ioc` / 引理 `StrictAnti.mapsTo_Ioc`

English:
lemma StrictAnti.mapsTo_Ioc
  given: (h : StrictAnti f)
  statement: MapsTo f (Ioc a b) (Ico (f b) (f a))
  proof: (h.strictAntiOn _).mapsTo_Ioc

中文:
引理 严格递减.mapsTo_Ioc
  条件: (h : 严格递减 f)
  结论: 映射到 f (左开右闭区间 a b) (左闭右开区间 (f b) (f a))
  证明: (h.strictAntiOn _).mapsTo_Ioc

Depends on / 依赖: h.strictAntiOn, mapsTo_Ioc, strictAntiOn
-/
lemma StrictAnti.mapsTo_Ioc (h : StrictAnti f) : MapsTo f (Ioc a b) (Ico (f b) (f a)) :=
  (h.strictAntiOn _).mapsTo_Ioc

/--
lemma `StrictMonoOn.image_Ico_subset` / 引理 `StrictMonoOn.image_Ico_subset`

English:
lemma StrictMonoOn.image_Ico_subset
  given: (h : StrictMonoOn f (Icc a b))
  proof: h.mapsTo_Ico.image_subset

中文:
引理 StrictMonoOn.image_Ico_subset
  条件: (h : StrictMonoOn f (闭区间 a b))
  证明: h.mapsTo_Ico.image_subset

Depends on / 依赖: h.mapsTo_Ico.image_subset, image_subset, mapsTo_Ico
-/
lemma StrictMonoOn.image_Ico_subset (h : StrictMonoOn f (Icc a b)) :
    f '' Ico a b subseteq Ico (f a) (f b) := h.mapsTo_Ico.image_subset

/--
lemma `StrictMonoOn.image_Ioc_subset` / 引理 `StrictMonoOn.image_Ioc_subset`

English:
lemma StrictMonoOn.image_Ioc_subset
  given: (h : StrictMonoOn f (Icc a b))
  proof: h.mapsTo_Ioc.image_subset

中文:
引理 StrictMonoOn.image_Ioc_subset
  条件: (h : StrictMonoOn f (闭区间 a b))
  证明: h.mapsTo_Ioc.image_subset

Depends on / 依赖: h.mapsTo_Ioc.image_subset, image_subset, mapsTo_Ioc
-/
lemma StrictMonoOn.image_Ioc_subset (h : StrictMonoOn f (Icc a b)) :
    f '' Ioc a b subseteq Ioc (f a) (f b) :=
  h.mapsTo_Ioc.image_subset

/--
lemma `StrictAntiOn.image_Ico_subset` / 引理 `StrictAntiOn.image_Ico_subset`

English:
lemma StrictAntiOn.image_Ico_subset
  given: (h : StrictAntiOn f (Icc a b))
  proof: h.mapsTo_Ico.image_subset

中文:
引理 StrictAntiOn.image_Ico_subset
  条件: (h : StrictAntiOn f (闭区间 a b))
  证明: h.mapsTo_Ico.image_subset

Depends on / 依赖: h.mapsTo_Ico.image_subset, image_subset, mapsTo_Ico
-/
lemma StrictAntiOn.image_Ico_subset (h : StrictAntiOn f (Icc a b)) :
    f '' Ico a b subseteq Ioc (f b) (f a) := h.mapsTo_Ico.image_subset

/--
lemma `StrictAntiOn.image_Ioc_subset` / 引理 `StrictAntiOn.image_Ioc_subset`

English:
lemma StrictAntiOn.image_Ioc_subset
  given: (h : StrictAntiOn f (Icc a b))
  proof: h.mapsTo_Ioc.image_subset

中文:
引理 StrictAntiOn.image_Ioc_subset
  条件: (h : StrictAntiOn f (闭区间 a b))
  证明: h.mapsTo_Ioc.image_subset

Depends on / 依赖: h.mapsTo_Ioc.image_subset, image_subset, mapsTo_Ioc
-/
lemma StrictAntiOn.image_Ioc_subset (h : StrictAntiOn f (Icc a b)) :
    f '' Ioc a b subseteq Ico (f b) (f a) := h.mapsTo_Ioc.image_subset

/--
lemma `StrictMono.image_Ico_subset` / 引理 `StrictMono.image_Ico_subset`

English:
lemma StrictMono.image_Ico_subset
  given: (h : StrictMono f)
  statement: f '' Ico a b subseteq Ico (f a) (f b)
  proof: (h.strictMonoOn _).image_Ico_subset

中文:
引理 严格递增.image_Ico_subset
  条件: (h : 严格递增 f)
  结论: f '' 左闭右开区间 a b subseteq 左闭右开区间 (f a) (f b)
  证明: (h.strictMonoOn _).image_Ico_subset

Depends on / 依赖: h.strictMonoOn, image_Ico_subset, strictMonoOn
-/
lemma StrictMono.image_Ico_subset (h : StrictMono f) : f '' Ico a b subseteq Ico (f a) (f b) :=
  (h.strictMonoOn _).image_Ico_subset

/--
lemma `StrictMono.image_Ioc_subset` / 引理 `StrictMono.image_Ioc_subset`

English:
lemma StrictMono.image_Ioc_subset
  given: (h : StrictMono f)
  statement: f '' Ioc a b subseteq Ioc (f a) (f b)
  proof: (h.strictMonoOn _).image_Ioc_subset

中文:
引理 严格递增.image_Ioc_subset
  条件: (h : 严格递增 f)
  结论: f '' 左开右闭区间 a b subseteq 左开右闭区间 (f a) (f b)
  证明: (h.strictMonoOn _).image_Ioc_subset

Depends on / 依赖: h.strictMonoOn, image_Ioc_subset, strictMonoOn
-/
lemma StrictMono.image_Ioc_subset (h : StrictMono f) : f '' Ioc a b subseteq Ioc (f a) (f b) :=
  (h.strictMonoOn _).image_Ioc_subset

/--
lemma `StrictAnti.image_Ico_subset` / 引理 `StrictAnti.image_Ico_subset`

English:
lemma StrictAnti.image_Ico_subset
  given: (h : StrictAnti f)
  statement: f '' Ico a b subseteq Ioc (f b) (f a)
  proof: (h.strictAntiOn _).image_Ico_subset

中文:
引理 严格递减.image_Ico_subset
  条件: (h : 严格递减 f)
  结论: f '' 左闭右开区间 a b subseteq 左开右闭区间 (f b) (f a)
  证明: (h.strictAntiOn _).image_Ico_subset

Depends on / 依赖: h.strictAntiOn, image_Ico_subset, strictAntiOn
-/
lemma StrictAnti.image_Ico_subset (h : StrictAnti f) : f '' Ico a b subseteq Ioc (f b) (f a) :=
  (h.strictAntiOn _).image_Ico_subset

/--
lemma `StrictAnti.image_Ioc_subset` / 引理 `StrictAnti.image_Ioc_subset`

English:
lemma StrictAnti.image_Ioc_subset
  given: (h : StrictAnti f)
  statement: f '' Ioc a b subseteq Ico (f b) (f a)
  proof: (h.strictAntiOn _).image_Ioc_subset

中文:
引理 严格递减.image_Ioc_subset
  条件: (h : 严格递减 f)
  结论: f '' 左开右闭区间 a b subseteq 左闭右开区间 (f b) (f a)
  证明: (h.strictAntiOn _).image_Ioc_subset

Depends on / 依赖: h.strictAntiOn, image_Ioc_subset, strictAntiOn
-/
lemma StrictAnti.image_Ioc_subset (h : StrictAnti f) : f '' Ioc a b subseteq Ico (f b) (f a) :=
  (h.strictAntiOn _).image_Ioc_subset

end PartialOrder

namespace Set

/--
lemma `image_subtype_val_Ixx_Ixi` / 引理 `image_subtype_val_Ixx_Ixi`

English:
lemma image_subtype_val_Ixx_Ixi
  statement: {p q r : α -> α -> Prop} {a b : α} (c : {x // p a x ∧ q x b})
  proof: (Subtype.image_preimage_val {x | p a x ∧ q x b} {y | r c.1 y}).trans by
    ext; simp +contextual [@and_comm (r _ _), h]

中文:
引理 image_subtype_val_Ixx_Ixi
  结论: {p q r : α -> α -> 命题} {a b : α} (c : {x // p a x ∧ q x b})
  证明: (Subtype.image_preimage_val {x | p a x ∧ q x b} {y | r c.1 y}).trans by
    ext; simp +contextual [@and_comm (r _ _), h]
-/
private lemma image_subtype_val_Ixx_Ixi {p q r : α -> α -> Prop} {a b : α} (c : {x // p a x ∧ q x b})
    (h : forall {x}, r c x -> p a x) :
    Subtype.val '' {y : {x // p a x ∧ q x b} | r c.1 y.1} = {y : α | r c.1 y ∧ q y b} :=
(Subtype.image_preimage_val {x | p a x ∧ q x b} {y | r c.1 y}).trans by
    ext; simp +contextual [@and_comm (r _ _), h]

/--
lemma `image_subtype_val_Ixx_Iix` / 引理 `image_subtype_val_Ixx_Iix`

English:
lemma image_subtype_val_Ixx_Iix
  statement: {p q r : α -> α -> Prop} {a b : α} (c : {x // p a x ∧ q x b})
  proof: (Subtype.image_preimage_val {x | p a x ∧ q x b} {y | r y c.1}).trans by
    ext; simp +contextual [h]

中文:
引理 image_subtype_val_Ixx_Iix
  结论: {p q r : α -> α -> 命题} {a b : α} (c : {x // p a x ∧ q x b})
  证明: (Subtype.image_preimage_val {x | p a x ∧ q x b} {y | r y c.1}).trans by
    ext; simp +contextual [h]
-/
private lemma image_subtype_val_Ixx_Iix {p q r : α -> α -> Prop} {a b : α} (c : {x // p a x ∧ q x b})
    (h : forall {x}, r x c -> q x b) :
    Subtype.val '' {y : {x // p a x ∧ q x b} | r y.1 c.1} = {y : α | p a y ∧ r y c.1} :=
(Subtype.image_preimage_val {x | p a x ∧ q x b} {y | r y c.1}).trans by
    ext; simp +contextual [h]

variable [Preorder α] {p : α -> Prop}

/--
lemma `preimage_subtype_val_Ici` / 引理 `preimage_subtype_val_Ici`

English:
lemma preimage_subtype_val_Ici
  given: (a : {x // p x})
  statement: (↑) ⁻¹' (Ici a.1) = Ici a
  proof: rfl

中文:
引理 preimage_subtype_val_Ici
  条件: (a : {x // p x})
  结论: (↑) ⁻¹' (左闭右无界区间 a.1) = 左闭右无界区间 a
  证明: rfl
-/
@[simp] lemma preimage_subtype_val_Ici (a : {x // p x}) : (↑) ⁻¹' (Ici a.1) = Ici a := rfl
/--
lemma `preimage_subtype_val_Iic` / 引理 `preimage_subtype_val_Iic`

English:
lemma preimage_subtype_val_Iic
  given: (a : {x // p x})
  statement: (↑) ⁻¹' (Iic a.1) = Iic a
  proof: rfl

中文:
引理 preimage_subtype_val_Iic
  条件: (a : {x // p x})
  结论: (↑) ⁻¹' (左无界右闭区间 a.1) = 左无界右闭区间 a
  证明: rfl
-/
@[simp] lemma preimage_subtype_val_Iic (a : {x // p x}) : (↑) ⁻¹' (Iic a.1) = Iic a := rfl
/--
lemma `preimage_subtype_val_Ioi` / 引理 `preimage_subtype_val_Ioi`

English:
lemma preimage_subtype_val_Ioi
  given: (a : {x // p x})
  statement: (↑) ⁻¹' (Ioi a.1) = Ioi a
  proof: rfl

中文:
引理 preimage_subtype_val_Ioi
  条件: (a : {x // p x})
  结论: (↑) ⁻¹' (左开右无界区间 a.1) = 左开右无界区间 a
  证明: rfl
-/
@[simp] lemma preimage_subtype_val_Ioi (a : {x // p x}) : (↑) ⁻¹' (Ioi a.1) = Ioi a := rfl
/--
lemma `preimage_subtype_val_Iio` / 引理 `preimage_subtype_val_Iio`

English:
lemma preimage_subtype_val_Iio
  given: (a : {x // p x})
  statement: (↑) ⁻¹' (Iio a.1) = Iio a
  proof: rfl

中文:
引理 preimage_subtype_val_Iio
  条件: (a : {x // p x})
  结论: (↑) ⁻¹' (左无界右开区间 a.1) = 左无界右开区间 a
  证明: rfl
-/
@[simp] lemma preimage_subtype_val_Iio (a : {x // p x}) : (↑) ⁻¹' (Iio a.1) = Iio a := rfl
/--
lemma `preimage_subtype_val_Icc` / 引理 `preimage_subtype_val_Icc`

English:
lemma preimage_subtype_val_Icc
  given: (a b : {x // p x})
  statement: (↑) ⁻¹' (Icc a.1 b) = Icc a b
  proof: rfl

中文:
引理 preimage_subtype_val_Icc
  条件: (a b : {x // p x})
  结论: (↑) ⁻¹' (闭区间 a.1 b) = 闭区间 a b
  证明: rfl
-/
@[simp] lemma preimage_subtype_val_Icc (a b : {x // p x}) : (↑) ⁻¹' (Icc a.1 b) = Icc a b := rfl
/--
lemma `preimage_subtype_val_Ico` / 引理 `preimage_subtype_val_Ico`

English:
lemma preimage_subtype_val_Ico
  given: (a b : {x // p x})
  statement: (↑) ⁻¹' (Ico a.1 b) = Ico a b
  proof: rfl

中文:
引理 preimage_subtype_val_Ico
  条件: (a b : {x // p x})
  结论: (↑) ⁻¹' (左闭右开区间 a.1 b) = 左闭右开区间 a b
  证明: rfl
-/
@[simp] lemma preimage_subtype_val_Ico (a b : {x // p x}) : (↑) ⁻¹' (Ico a.1 b) = Ico a b := rfl
/--
lemma `preimage_subtype_val_Ioc` / 引理 `preimage_subtype_val_Ioc`

English:
lemma preimage_subtype_val_Ioc
  given: (a b : {x // p x})
  statement: (↑) ⁻¹' (Ioc a.1 b) = Ioc a b
  proof: rfl

中文:
引理 preimage_subtype_val_Ioc
  条件: (a b : {x // p x})
  结论: (↑) ⁻¹' (左开右闭区间 a.1 b) = 左开右闭区间 a b
  证明: rfl
-/
@[simp] lemma preimage_subtype_val_Ioc (a b : {x // p x}) : (↑) ⁻¹' (Ioc a.1 b) = Ioc a b := rfl
/--
lemma `preimage_subtype_val_Ioo` / 引理 `preimage_subtype_val_Ioo`

English:
lemma preimage_subtype_val_Ioo
  given: (a b : {x // p x})
  statement: (↑) ⁻¹' (Ioo a.1 b) = Ioo a b
  proof: rfl

中文:
引理 preimage_subtype_val_Ioo
  条件: (a b : {x // p x})
  结论: (↑) ⁻¹' (开区间 a.1 b) = 开区间 a b
  证明: rfl
-/
@[simp] lemma preimage_subtype_val_Ioo (a b : {x // p x}) : (↑) ⁻¹' (Ioo a.1 b) = Ioo a b := rfl

/--
theorem `image_subtype_val_Icc_subset` / 定理 `image_subtype_val_Icc_subset`

English:
theorem image_subtype_val_Icc_subset
  given: (a b : {x // p x})
  proof: image_subset_iff.mpr fun _ m => m

中文:
定理 image_subtype_val_Icc_subset
  条件: (a b : {x // p x})
  证明: image_subset_iff.mpr fun _ m => m

Depends on / 依赖: image_subset_iff, image_subset_iff.mpr
-/
theorem image_subtype_val_Icc_subset (a b : {x // p x}) :
    Subtype.val '' Icc a b subseteq Icc a.val b.val :=
  image_subset_iff.mpr fun _ m => m

/--
theorem `image_subtype_val_Ico_subset` / 定理 `image_subtype_val_Ico_subset`

English:
theorem image_subtype_val_Ico_subset
  given: (a b : {x // p x})
  proof: image_subset_iff.mpr fun _ m => m

中文:
定理 image_subtype_val_Ico_subset
  条件: (a b : {x // p x})
  证明: image_subset_iff.mpr fun _ m => m

Depends on / 依赖: image_subset_iff, image_subset_iff.mpr
-/
theorem image_subtype_val_Ico_subset (a b : {x // p x}) :
    Subtype.val '' Ico a b subseteq Ico a.val b.val :=
  image_subset_iff.mpr fun _ m => m

/--
theorem `image_subtype_val_Ioc_subset` / 定理 `image_subtype_val_Ioc_subset`

English:
theorem image_subtype_val_Ioc_subset
  given: (a b : {x // p x})
  proof: image_subset_iff.mpr fun _ m => m

中文:
定理 image_subtype_val_Ioc_subset
  条件: (a b : {x // p x})
  证明: image_subset_iff.mpr fun _ m => m

Depends on / 依赖: image_subset_iff, image_subset_iff.mpr
-/
theorem image_subtype_val_Ioc_subset (a b : {x // p x}) :
    Subtype.val '' Ioc a b subseteq Ioc a.val b.val :=
  image_subset_iff.mpr fun _ m => m

/--
theorem `image_subtype_val_Ioo_subset` / 定理 `image_subtype_val_Ioo_subset`

English:
theorem image_subtype_val_Ioo_subset
  given: (a b : {x // p x})
  proof: image_subset_iff.mpr fun _ m => m

中文:
定理 image_subtype_val_Ioo_subset
  条件: (a b : {x // p x})
  证明: image_subset_iff.mpr fun _ m => m

Depends on / 依赖: image_subset_iff, image_subset_iff.mpr
-/
theorem image_subtype_val_Ioo_subset (a b : {x // p x}) :
    Subtype.val '' Ioo a b subseteq Ioo a.val b.val :=
  image_subset_iff.mpr fun _ m => m

/--
theorem `image_subtype_val_Iic_subset` / 定理 `image_subtype_val_Iic_subset`

English:
theorem image_subtype_val_Iic_subset
  given: (a : {x // p x})
  proof: image_subset_iff.mpr fun _ m => m

中文:
定理 image_subtype_val_Iic_subset
  条件: (a : {x // p x})
  证明: image_subset_iff.mpr fun _ m => m

Depends on / 依赖: image_subset_iff, image_subset_iff.mpr
-/
theorem image_subtype_val_Iic_subset (a : {x // p x}) :
    Subtype.val '' Iic a subseteq Iic a.val :=
  image_subset_iff.mpr fun _ m => m

/--
theorem `image_subtype_val_Iio_subset` / 定理 `image_subtype_val_Iio_subset`

English:
theorem image_subtype_val_Iio_subset
  given: (a : {x // p x})
  proof: image_subset_iff.mpr fun _ m => m

中文:
定理 image_subtype_val_Iio_subset
  条件: (a : {x // p x})
  证明: image_subset_iff.mpr fun _ m => m

Depends on / 依赖: image_subset_iff, image_subset_iff.mpr
-/
theorem image_subtype_val_Iio_subset (a : {x // p x}) :
    Subtype.val '' Iio a subseteq Iio a.val :=
  image_subset_iff.mpr fun _ m => m

/--
theorem `image_subtype_val_Ici_subset` / 定理 `image_subtype_val_Ici_subset`

English:
theorem image_subtype_val_Ici_subset
  given: (a : {x // p x})
  proof: image_subset_iff.mpr fun _ m => m

中文:
定理 image_subtype_val_Ici_subset
  条件: (a : {x // p x})
  证明: image_subset_iff.mpr fun _ m => m

Depends on / 依赖: image_subset_iff, image_subset_iff.mpr
-/
theorem image_subtype_val_Ici_subset (a : {x // p x}) :
    Subtype.val '' Ici a subseteq Ici a.val :=
  image_subset_iff.mpr fun _ m => m

/--
theorem `image_subtype_val_Ioi_subset` / 定理 `image_subtype_val_Ioi_subset`

English:
theorem image_subtype_val_Ioi_subset
  given: (a : {x // p x})
  proof: image_subset_iff.mpr fun _ m => m

@[simp]

中文:
定理 image_subtype_val_Ioi_subset
  条件: (a : {x // p x})
  证明: image_subset_iff.mpr fun _ m => m

@[simp]

Depends on / 依赖: image_subset_iff, image_subset_iff.mpr
-/
theorem image_subtype_val_Ioi_subset (a : {x // p x}) :
    Subtype.val '' Ioi a subseteq Ioi a.val :=
  image_subset_iff.mpr fun _ m => m

@[simp]
/--
lemma `image_subtype_val_Ici_Iic` / 引理 `image_subtype_val_Ici_Iic`

English:
lemma image_subtype_val_Ici_Iic
  given: {a : α} (b : Ici a)
  statement: Subtype.val '' Iic b = Icc a b
  proof: (Subtype.image_preimage_val (Ici a) (Iic b.1)).trans Ici_inter_Iic

@[simp]

中文:
引理 image_subtype_val_Ici_Iic
  条件: {a : α} (b : 左闭右无界区间 a)
  结论: 子类型.val '' 左无界右闭区间 b = 闭区间 a b
  证明: (Subtype.image_preimage_val (Ici a) (Iic b.1)).trans Ici_inter_Iic

@[simp]

Depends on / 依赖: Ici_inter_Iic, Subtype, Subtype.image_preimage_val, image_preimage_val
-/
lemma image_subtype_val_Ici_Iic {a : α} (b : Ici a) : Subtype.val '' Iic b = Icc a b :=
  (Subtype.image_preimage_val (Ici a) (Iic b.1)).trans Ici_inter_Iic

@[simp]
/--
lemma `image_subtype_val_Ici_Iio` / 引理 `image_subtype_val_Ici_Iio`

English:
lemma image_subtype_val_Ici_Iio
  given: {a : α} (b : Ici a)
  statement: Subtype.val '' Iio b = Ico a b
  proof: (Subtype.image_preimage_val (Ici a) (Iio b.1)).trans Ici_inter_Iio

@[simp]

中文:
引理 image_subtype_val_Ici_Iio
  条件: {a : α} (b : 左闭右无界区间 a)
  结论: 子类型.val '' 左无界右开区间 b = 左闭右开区间 a b
  证明: (Subtype.image_preimage_val (Ici a) (Iio b.1)).trans Ici_inter_Iio

@[simp]

Depends on / 依赖: Ici_inter_Iio, Subtype, Subtype.image_preimage_val, image_preimage_val
-/
lemma image_subtype_val_Ici_Iio {a : α} (b : Ici a) : Subtype.val '' Iio b = Ico a b :=
  (Subtype.image_preimage_val (Ici a) (Iio b.1)).trans Ici_inter_Iio

@[simp]
/--
lemma `image_subtype_val_Ici_Ici` / 引理 `image_subtype_val_Ici_Ici`

English:
lemma image_subtype_val_Ici_Ici
  given: {a : α} (b : Ici a)
  statement: Subtype.val '' Ici b = Ici b.1
  proof: (Subtype.image_preimage_val (Ici a) (Ici b.1)).trans inter_eq_right.2 Ici_subset_Ici.2 b.2

@[simp]

中文:
引理 image_subtype_val_Ici_Ici
  条件: {a : α} (b : 左闭右无界区间 a)
  结论: 子类型.val '' 左闭右无界区间 b = 左闭右无界区间 b.1
  证明: (Subtype.image_preimage_val (Ici a) (Ici b.1)).trans inter_eq_right.2 Ici_subset_Ici.2 b.2

@[simp]

Depends on / 依赖: Ici_subset_Ici, Subtype, Subtype.image_preimage_val, image_preimage_val, inter_eq_right
-/
lemma image_subtype_val_Ici_Ici {a : α} (b : Ici a) : Subtype.val '' Ici b = Ici b.1 :=
(Subtype.image_preimage_val (Ici a) (Ici b.1)).trans inter_eq_right.2 Ici_subset_Ici.2 b.2

@[simp]
/--
lemma `image_subtype_val_Ici_Ioi` / 引理 `image_subtype_val_Ici_Ioi`

English:
lemma image_subtype_val_Ici_Ioi
  given: {a : α} (b : Ici a)
  statement: Subtype.val '' Ioi b = Ioi b.1
  proof: (Subtype.image_preimage_val (Ici a) (Ioi b.1)).trans inter_eq_right.2 Ioi_subset_Ici b.2

@[simp]

中文:
引理 image_subtype_val_Ici_Ioi
  条件: {a : α} (b : 左闭右无界区间 a)
  结论: 子类型.val '' 左开右无界区间 b = 左开右无界区间 b.1
  证明: (Subtype.image_preimage_val (Ici a) (Ioi b.1)).trans inter_eq_right.2 Ioi_subset_Ici b.2

@[simp]

Depends on / 依赖: Ioi_subset_Ici, Subtype, Subtype.image_preimage_val, image_preimage_val, inter_eq_right
-/
lemma image_subtype_val_Ici_Ioi {a : α} (b : Ici a) : Subtype.val '' Ioi b = Ioi b.1 :=
(Subtype.image_preimage_val (Ici a) (Ioi b.1)).trans inter_eq_right.2 Ioi_subset_Ici b.2

@[simp]
/--
lemma `image_subtype_val_Iic_Ici` / 引理 `image_subtype_val_Iic_Ici`

English:
lemma image_subtype_val_Iic_Ici
  given: {a : α} (b : Iic a)
  statement: Subtype.val '' Ici b = Icc b.1 a
  proof: (Subtype.image_preimage_val (Iic a) (Ici b)).trans inter_comm _ _

@[simp]

中文:
引理 image_subtype_val_Iic_Ici
  条件: {a : α} (b : 左无界右闭区间 a)
  结论: 子类型.val '' 左闭右无界区间 b = 闭区间 b.1 a
  证明: (Subtype.image_preimage_val (Iic a) (Ici b)).trans inter_comm _ _

@[simp]

Depends on / 依赖: Subtype, Subtype.image_preimage_val, image_preimage_val, inter_comm
-/
lemma image_subtype_val_Iic_Ici {a : α} (b : Iic a) : Subtype.val '' Ici b = Icc b.1 a :=
(Subtype.image_preimage_val (Iic a) (Ici b)).trans inter_comm _ _

@[simp]
/--
lemma `image_subtype_val_Iic_Ioi` / 引理 `image_subtype_val_Iic_Ioi`

English:
lemma image_subtype_val_Iic_Ioi
  given: {a : α} (b : Iic a)
  statement: Subtype.val '' Ioi b = Ioc b.1 a
  proof: (Subtype.image_preimage_val (Iic a) (Ioi b)).trans inter_comm _ _

@[simp]

中文:
引理 image_subtype_val_Iic_Ioi
  条件: {a : α} (b : 左无界右闭区间 a)
  结论: 子类型.val '' 左开右无界区间 b = 左开右闭区间 b.1 a
  证明: (Subtype.image_preimage_val (Iic a) (Ioi b)).trans inter_comm _ _

@[simp]

Depends on / 依赖: Subtype, Subtype.image_preimage_val, image_preimage_val, inter_comm
-/
lemma image_subtype_val_Iic_Ioi {a : α} (b : Iic a) : Subtype.val '' Ioi b = Ioc b.1 a :=
(Subtype.image_preimage_val (Iic a) (Ioi b)).trans inter_comm _ _

@[simp]
/--
lemma `image_subtype_val_Iic_Iic` / 引理 `image_subtype_val_Iic_Iic`

English:
lemma image_subtype_val_Iic_Iic
  given: {a : α} (b : Iic a)
  statement: Subtype.val '' Iic b = Iic b.1
  proof: image_subtype_val_Ici_Ici (α := αᵒᵈ) _

@[simp]

中文:
引理 image_subtype_val_Iic_Iic
  条件: {a : α} (b : 左无界右闭区间 a)
  结论: 子类型.val '' 左无界右闭区间 b = 左无界右闭区间 b.1
  证明: image_subtype_val_Ici_Ici (α := αᵒᵈ) _

@[simp]

Depends on / 依赖: image_subtype_val_Ici_Ici
-/
lemma image_subtype_val_Iic_Iic {a : α} (b : Iic a) : Subtype.val '' Iic b = Iic b.1 :=
  image_subtype_val_Ici_Ici (α := αᵒᵈ) _

@[simp]
/--
lemma `image_subtype_val_Iic_Iio` / 引理 `image_subtype_val_Iic_Iio`

English:
lemma image_subtype_val_Iic_Iio
  given: {a : α} (b : Iic a)
  statement: Subtype.val '' Iio b = Iio b.1
  proof: image_subtype_val_Ici_Ioi (α := αᵒᵈ) _

@[simp]

中文:
引理 image_subtype_val_Iic_Iio
  条件: {a : α} (b : 左无界右闭区间 a)
  结论: 子类型.val '' 左无界右开区间 b = 左无界右开区间 b.1
  证明: image_subtype_val_Ici_Ioi (α := αᵒᵈ) _

@[simp]

Depends on / 依赖: image_subtype_val_Ici_Ioi
-/
lemma image_subtype_val_Iic_Iio {a : α} (b : Iic a) : Subtype.val '' Iio b = Iio b.1 :=
  image_subtype_val_Ici_Ioi (α := αᵒᵈ) _

@[simp]
/--
lemma `image_subtype_val_Ioi_Ici` / 引理 `image_subtype_val_Ioi_Ici`

English:
lemma image_subtype_val_Ioi_Ici
  given: {a : α} (b : Ioi a)
  statement: Subtype.val '' Ici b = Ici b.1
  proof: (Subtype.image_preimage_val (Ioi a) (Ici b.1)).trans inter_eq_right.2 Ici_subset_Ioi.2 b.2

@[simp]

中文:
引理 image_subtype_val_Ioi_Ici
  条件: {a : α} (b : 左开右无界区间 a)
  结论: 子类型.val '' 左闭右无界区间 b = 左闭右无界区间 b.1
  证明: (Subtype.image_preimage_val (Ioi a) (Ici b.1)).trans inter_eq_right.2 Ici_subset_Ioi.2 b.2

@[simp]

Depends on / 依赖: Ici_subset_Ioi, Subtype, Subtype.image_preimage_val, image_preimage_val, inter_eq_right
-/
lemma image_subtype_val_Ioi_Ici {a : α} (b : Ioi a) : Subtype.val '' Ici b = Ici b.1 :=
(Subtype.image_preimage_val (Ioi a) (Ici b.1)).trans inter_eq_right.2 Ici_subset_Ioi.2 b.2

@[simp]
/--
lemma `image_subtype_val_Ioi_Iic` / 引理 `image_subtype_val_Ioi_Iic`

English:
lemma image_subtype_val_Ioi_Iic
  given: {a : α} (b : Ioi a)
  statement: Subtype.val '' Iic b = Ioc a b
  proof: (Subtype.image_preimage_val (Ioi a) (Iic b.1)).trans Ioi_inter_Iic

@[simp]

中文:
引理 image_subtype_val_Ioi_Iic
  条件: {a : α} (b : 左开右无界区间 a)
  结论: 子类型.val '' 左无界右闭区间 b = 左开右闭区间 a b
  证明: (Subtype.image_preimage_val (Ioi a) (Iic b.1)).trans Ioi_inter_Iic

@[simp]

Depends on / 依赖: Ioi_inter_Iic, Subtype, Subtype.image_preimage_val, image_preimage_val
-/
lemma image_subtype_val_Ioi_Iic {a : α} (b : Ioi a) : Subtype.val '' Iic b = Ioc a b :=
  (Subtype.image_preimage_val (Ioi a) (Iic b.1)).trans Ioi_inter_Iic

@[simp]
/--
lemma `image_subtype_val_Ioi_Ioi` / 引理 `image_subtype_val_Ioi_Ioi`

English:
lemma image_subtype_val_Ioi_Ioi
  given: {a : α} (b : Ioi a)
  statement: Subtype.val '' Ioi b = Ioi b.1
  proof: (Subtype.image_preimage_val (Ioi a) (Ioi b.1)).trans inter_eq_right.2 Ioi_subset_Ioi b.2.le

@[simp]

中文:
引理 image_subtype_val_Ioi_Ioi
  条件: {a : α} (b : 左开右无界区间 a)
  结论: 子类型.val '' 左开右无界区间 b = 左开右无界区间 b.1
  证明: (Subtype.image_preimage_val (Ioi a) (Ioi b.1)).trans inter_eq_right.2 Ioi_subset_Ioi b.2.le

@[simp]

Depends on / 依赖: Ioi_subset_Ioi, Subtype, Subtype.image_preimage_val, image_preimage_val, inter_eq_right
-/
lemma image_subtype_val_Ioi_Ioi {a : α} (b : Ioi a) : Subtype.val '' Ioi b = Ioi b.1 :=
(Subtype.image_preimage_val (Ioi a) (Ioi b.1)).trans inter_eq_right.2 Ioi_subset_Ioi b.2.le

@[simp]
/--
lemma `image_subtype_val_Ioi_Iio` / 引理 `image_subtype_val_Ioi_Iio`

English:
lemma image_subtype_val_Ioi_Iio
  given: {a : α} (b : Ioi a)
  statement: Subtype.val '' Iio b = Ioo a b
  proof: (Subtype.image_preimage_val (Ioi a) (Iio b.1)).trans Ioi_inter_Iio

@[simp]

中文:
引理 image_subtype_val_Ioi_Iio
  条件: {a : α} (b : 左开右无界区间 a)
  结论: 子类型.val '' 左无界右开区间 b = 开区间 a b
  证明: (Subtype.image_preimage_val (Ioi a) (Iio b.1)).trans Ioi_inter_Iio

@[simp]

Depends on / 依赖: Ioi_inter_Iio, Subtype, Subtype.image_preimage_val, image_preimage_val
-/
lemma image_subtype_val_Ioi_Iio {a : α} (b : Ioi a) : Subtype.val '' Iio b = Ioo a b :=
  (Subtype.image_preimage_val (Ioi a) (Iio b.1)).trans Ioi_inter_Iio

@[simp]
/--
lemma `image_subtype_val_Iio_Ici` / 引理 `image_subtype_val_Iio_Ici`

English:
lemma image_subtype_val_Iio_Ici
  given: {a : α} (b : Iio a)
  statement: Subtype.val '' Ici b = Ico b.1 a
  proof: (Subtype.image_preimage_val (Iio a) (Ici b)).trans inter_comm _ _

@[simp]

中文:
引理 image_subtype_val_Iio_Ici
  条件: {a : α} (b : 左无界右开区间 a)
  结论: 子类型.val '' 左闭右无界区间 b = 左闭右开区间 b.1 a
  证明: (Subtype.image_preimage_val (Iio a) (Ici b)).trans inter_comm _ _

@[simp]

Depends on / 依赖: Subtype, Subtype.image_preimage_val, image_preimage_val, inter_comm
-/
lemma image_subtype_val_Iio_Ici {a : α} (b : Iio a) : Subtype.val '' Ici b = Ico b.1 a :=
(Subtype.image_preimage_val (Iio a) (Ici b)).trans inter_comm _ _

@[simp]
/--
lemma `image_subtype_val_Iio_Iic` / 引理 `image_subtype_val_Iio_Iic`

English:
lemma image_subtype_val_Iio_Iic
  given: {a : α} (b : Iio a)
  statement: Subtype.val '' Iic b = Iic b.1
  proof: image_subtype_val_Ioi_Ici (α := αᵒᵈ) _

@[simp]

中文:
引理 image_subtype_val_Iio_Iic
  条件: {a : α} (b : 左无界右开区间 a)
  结论: 子类型.val '' 左无界右闭区间 b = 左无界右闭区间 b.1
  证明: image_subtype_val_Ioi_Ici (α := αᵒᵈ) _

@[simp]

Depends on / 依赖: image_subtype_val_Ioi_Ici
-/
lemma image_subtype_val_Iio_Iic {a : α} (b : Iio a) : Subtype.val '' Iic b = Iic b.1 :=
  image_subtype_val_Ioi_Ici (α := αᵒᵈ) _

@[simp]
/--
lemma `image_subtype_val_Iio_Ioi` / 引理 `image_subtype_val_Iio_Ioi`

English:
lemma image_subtype_val_Iio_Ioi
  given: {a : α} (b : Iio a)
  statement: Subtype.val '' Ioi b = Ioo b.1 a
  proof: (Subtype.image_preimage_val (Iio a) (Ioi b)).trans inter_comm _ _

@[simp]

中文:
引理 image_subtype_val_Iio_Ioi
  条件: {a : α} (b : 左无界右开区间 a)
  结论: 子类型.val '' 左开右无界区间 b = 开区间 b.1 a
  证明: (Subtype.image_preimage_val (Iio a) (Ioi b)).trans inter_comm _ _

@[simp]

Depends on / 依赖: Subtype, Subtype.image_preimage_val, image_preimage_val, inter_comm
-/
lemma image_subtype_val_Iio_Ioi {a : α} (b : Iio a) : Subtype.val '' Ioi b = Ioo b.1 a :=
(Subtype.image_preimage_val (Iio a) (Ioi b)).trans inter_comm _ _

@[simp]
/--
lemma `image_subtype_val_Iio_Iio` / 引理 `image_subtype_val_Iio_Iio`

English:
lemma image_subtype_val_Iio_Iio
  given: {a : α} (b : Iio a)
  statement: Subtype.val '' Iio b = Iio b.1
  proof: image_subtype_val_Ioi_Ioi (α := αᵒᵈ) _

@[simp]

中文:
引理 image_subtype_val_Iio_Iio
  条件: {a : α} (b : 左无界右开区间 a)
  结论: 子类型.val '' 左无界右开区间 b = 左无界右开区间 b.1
  证明: image_subtype_val_Ioi_Ioi (α := αᵒᵈ) _

@[simp]

Depends on / 依赖: image_subtype_val_Ioi_Ioi
-/
lemma image_subtype_val_Iio_Iio {a : α} (b : Iio a) : Subtype.val '' Iio b = Iio b.1 :=
  image_subtype_val_Ioi_Ioi (α := αᵒᵈ) _

@[simp]
/--
lemma `image_subtype_val_Icc_Ici` / 引理 `image_subtype_val_Icc_Ici`

English:
lemma image_subtype_val_Icc_Ici
  given: {a b : α} (c : Icc a b)
  statement: Subtype.val '' Ici c = Icc c.1 b
  proof: image_subtype_val_Ixx_Ixi c c.2.1.trans

@[simp]

中文:
引理 image_subtype_val_Icc_Ici
  条件: {a b : α} (c : 闭区间 a b)
  结论: 子类型.val '' 左闭右无界区间 c = 闭区间 c.1 b
  证明: image_subtype_val_Ixx_Ixi c c.2.1.trans

@[simp]

Depends on / 依赖: image_subtype_val_Ixx_Ixi
-/
lemma image_subtype_val_Icc_Ici {a b : α} (c : Icc a b) : Subtype.val '' Ici c = Icc c.1 b :=
  image_subtype_val_Ixx_Ixi c c.2.1.trans

@[simp]
/--
lemma `image_subtype_val_Icc_Iic` / 引理 `image_subtype_val_Icc_Iic`

English:
lemma image_subtype_val_Icc_Iic
  given: {a b : α} (c : Icc a b)
  statement: Subtype.val '' Iic c = Icc a c
  proof: image_subtype_val_Ixx_Iix c (le_trans · c.2.2)

@[simp]

中文:
引理 image_subtype_val_Icc_Iic
  条件: {a b : α} (c : 闭区间 a b)
  结论: 子类型.val '' 左无界右闭区间 c = 闭区间 a c
  证明: image_subtype_val_Ixx_Iix c (le_trans · c.2.2)

@[simp]

Depends on / 依赖: image_subtype_val_Ixx_Iix, le_trans
-/
lemma image_subtype_val_Icc_Iic {a b : α} (c : Icc a b) : Subtype.val '' Iic c = Icc a c :=
  image_subtype_val_Ixx_Iix c (le_trans · c.2.2)

@[simp]
/--
lemma `image_subtype_val_Icc_Ioi` / 引理 `image_subtype_val_Icc_Ioi`

English:
lemma image_subtype_val_Icc_Ioi
  given: {a b : α} (c : Icc a b)
  statement: Subtype.val '' Ioi c = Ioc c.1 b
  proof: image_subtype_val_Ixx_Ixi c (c.2.1.trans <| le_of_lt ·)

@[simp]

中文:
引理 image_subtype_val_Icc_Ioi
  条件: {a b : α} (c : 闭区间 a b)
  结论: 子类型.val '' 左开右无界区间 c = 左开右闭区间 c.1 b
  证明: image_subtype_val_Ixx_Ixi c (c.2.1.trans <| le_of_lt ·)

@[simp]

Depends on / 依赖: image_subtype_val_Ixx_Ixi, le_of_lt
-/
lemma image_subtype_val_Icc_Ioi {a b : α} (c : Icc a b) : Subtype.val '' Ioi c = Ioc c.1 b :=
  image_subtype_val_Ixx_Ixi c (c.2.1.trans <| le_of_lt ·)

@[simp]
/--
lemma `image_subtype_val_Icc_Iio` / 引理 `image_subtype_val_Icc_Iio`

English:
lemma image_subtype_val_Icc_Iio
  given: {a b : α} (c : Icc a b)
  statement: Subtype.val '' Iio c = Ico a c
  proof: image_subtype_val_Ixx_Iix c fun h => (le_of_lt h).trans c.2.2

@[simp]

中文:
引理 image_subtype_val_Icc_Iio
  条件: {a b : α} (c : 闭区间 a b)
  结论: 子类型.val '' 左无界右开区间 c = 左闭右开区间 a c
  证明: image_subtype_val_Ixx_Iix c fun h => (le_of_lt h).trans c.2.2

@[simp]

Depends on / 依赖: image_subtype_val_Ixx_Iix, le_of_lt
-/
lemma image_subtype_val_Icc_Iio {a b : α} (c : Icc a b) : Subtype.val '' Iio c = Ico a c :=
  image_subtype_val_Ixx_Iix c fun h => (le_of_lt h).trans c.2.2

@[simp]
/--
lemma `image_subtype_val_Ico_Ici` / 引理 `image_subtype_val_Ico_Ici`

English:
lemma image_subtype_val_Ico_Ici
  given: {a b : α} (c : Ico a b)
  statement: Subtype.val '' Ici c = Ico c.1 b
  proof: image_subtype_val_Ixx_Ixi c c.2.1.trans

@[simp]

中文:
引理 image_subtype_val_Ico_Ici
  条件: {a b : α} (c : 左闭右开区间 a b)
  结论: 子类型.val '' 左闭右无界区间 c = 左闭右开区间 c.1 b
  证明: image_subtype_val_Ixx_Ixi c c.2.1.trans

@[simp]

Depends on / 依赖: image_subtype_val_Ixx_Ixi
-/
lemma image_subtype_val_Ico_Ici {a b : α} (c : Ico a b) : Subtype.val '' Ici c = Ico c.1 b :=
  image_subtype_val_Ixx_Ixi c c.2.1.trans

@[simp]
/--
lemma `image_subtype_val_Ico_Iic` / 引理 `image_subtype_val_Ico_Iic`

English:
lemma image_subtype_val_Ico_Iic
  given: {a b : α} (c : Ico a b)
  statement: Subtype.val '' Iic c = Icc a c
  proof: image_subtype_val_Ixx_Iix c (lt_of_le_of_lt · c.2.2)

@[simp]

中文:
引理 image_subtype_val_Ico_Iic
  条件: {a b : α} (c : 左闭右开区间 a b)
  结论: 子类型.val '' 左无界右闭区间 c = 闭区间 a c
  证明: image_subtype_val_Ixx_Iix c (lt_of_le_of_lt · c.2.2)

@[simp]

Depends on / 依赖: image_subtype_val_Ixx_Iix, lt_of_le_of_lt
-/
lemma image_subtype_val_Ico_Iic {a b : α} (c : Ico a b) : Subtype.val '' Iic c = Icc a c :=
  image_subtype_val_Ixx_Iix c (lt_of_le_of_lt · c.2.2)

@[simp]
/--
lemma `image_subtype_val_Ico_Ioi` / 引理 `image_subtype_val_Ico_Ioi`

English:
lemma image_subtype_val_Ico_Ioi
  given: {a b : α} (c : Ico a b)
  statement: Subtype.val '' Ioi c = Ioo c.1 b
  proof: image_subtype_val_Ixx_Ixi c (c.2.1.trans <| le_of_lt ·)

@[simp]

中文:
引理 image_subtype_val_Ico_Ioi
  条件: {a b : α} (c : 左闭右开区间 a b)
  结论: 子类型.val '' 左开右无界区间 c = 开区间 c.1 b
  证明: image_subtype_val_Ixx_Ixi c (c.2.1.trans <| le_of_lt ·)

@[simp]

Depends on / 依赖: image_subtype_val_Ixx_Ixi, le_of_lt
-/
lemma image_subtype_val_Ico_Ioi {a b : α} (c : Ico a b) : Subtype.val '' Ioi c = Ioo c.1 b :=
  image_subtype_val_Ixx_Ixi c (c.2.1.trans <| le_of_lt ·)

@[simp]
/--
lemma `image_subtype_val_Ico_Iio` / 引理 `image_subtype_val_Ico_Iio`

English:
lemma image_subtype_val_Ico_Iio
  given: {a b : α} (c : Ico a b)
  statement: Subtype.val '' Iio c = Ico a c
  proof: image_subtype_val_Ixx_Iix c (lt_trans · c.2.2)

@[simp]

中文:
引理 image_subtype_val_Ico_Iio
  条件: {a b : α} (c : 左闭右开区间 a b)
  结论: 子类型.val '' 左无界右开区间 c = 左闭右开区间 a c
  证明: image_subtype_val_Ixx_Iix c (lt_trans · c.2.2)

@[simp]

Depends on / 依赖: image_subtype_val_Ixx_Iix, lt_trans
-/
lemma image_subtype_val_Ico_Iio {a b : α} (c : Ico a b) : Subtype.val '' Iio c = Ico a c :=
  image_subtype_val_Ixx_Iix c (lt_trans · c.2.2)

@[simp]
/--
lemma `image_subtype_val_Ioc_Ici` / 引理 `image_subtype_val_Ioc_Ici`

English:
lemma image_subtype_val_Ioc_Ici
  given: {a b : α} (c : Ioc a b)
  statement: Subtype.val '' Ici c = Icc c.1 b
  proof: image_subtype_val_Ixx_Ixi c c.2.1.trans_le

@[simp]

中文:
引理 image_subtype_val_Ioc_Ici
  条件: {a b : α} (c : 左开右闭区间 a b)
  结论: 子类型.val '' 左闭右无界区间 c = 闭区间 c.1 b
  证明: image_subtype_val_Ixx_Ixi c c.2.1.trans_le

@[simp]

Depends on / 依赖: image_subtype_val_Ixx_Ixi, trans_le
-/
lemma image_subtype_val_Ioc_Ici {a b : α} (c : Ioc a b) : Subtype.val '' Ici c = Icc c.1 b :=
  image_subtype_val_Ixx_Ixi c c.2.1.trans_le

@[simp]
/--
lemma `image_subtype_val_Ioc_Iic` / 引理 `image_subtype_val_Ioc_Iic`

English:
lemma image_subtype_val_Ioc_Iic
  given: {a b : α} (c : Ioc a b)
  statement: Subtype.val '' Iic c = Ioc a c
  proof: image_subtype_val_Ixx_Iix c (le_trans · c.2.2)

@[simp]

中文:
引理 image_subtype_val_Ioc_Iic
  条件: {a b : α} (c : 左开右闭区间 a b)
  结论: 子类型.val '' 左无界右闭区间 c = 左开右闭区间 a c
  证明: image_subtype_val_Ixx_Iix c (le_trans · c.2.2)

@[simp]

Depends on / 依赖: image_subtype_val_Ixx_Iix, le_trans
-/
lemma image_subtype_val_Ioc_Iic {a b : α} (c : Ioc a b) : Subtype.val '' Iic c = Ioc a c :=
  image_subtype_val_Ixx_Iix c (le_trans · c.2.2)

@[simp]
/--
lemma `image_subtype_val_Ioc_Ioi` / 引理 `image_subtype_val_Ioc_Ioi`

English:
lemma image_subtype_val_Ioc_Ioi
  given: {a b : α} (c : Ioc a b)
  statement: Subtype.val '' Ioi c = Ioc c.1 b
  proof: image_subtype_val_Ixx_Ixi c c.2.1.trans

@[simp]

中文:
引理 image_subtype_val_Ioc_Ioi
  条件: {a b : α} (c : 左开右闭区间 a b)
  结论: 子类型.val '' 左开右无界区间 c = 左开右闭区间 c.1 b
  证明: image_subtype_val_Ixx_Ixi c c.2.1.trans

@[simp]

Depends on / 依赖: image_subtype_val_Ixx_Ixi
-/
lemma image_subtype_val_Ioc_Ioi {a b : α} (c : Ioc a b) : Subtype.val '' Ioi c = Ioc c.1 b :=
  image_subtype_val_Ixx_Ixi c c.2.1.trans

@[simp]
/--
lemma `image_subtype_val_Ioc_Iio` / 引理 `image_subtype_val_Ioc_Iio`

English:
lemma image_subtype_val_Ioc_Iio
  given: {a b : α} (c : Ioc a b)
  statement: Subtype.val '' Iio c = Ioo a c
  proof: image_subtype_val_Ixx_Iix c fun h => (le_of_lt h).trans c.2.2

@[simp]

中文:
引理 image_subtype_val_Ioc_Iio
  条件: {a b : α} (c : 左开右闭区间 a b)
  结论: 子类型.val '' 左无界右开区间 c = 开区间 a c
  证明: image_subtype_val_Ixx_Iix c fun h => (le_of_lt h).trans c.2.2

@[simp]

Depends on / 依赖: image_subtype_val_Ixx_Iix, le_of_lt
-/
lemma image_subtype_val_Ioc_Iio {a b : α} (c : Ioc a b) : Subtype.val '' Iio c = Ioo a c :=
  image_subtype_val_Ixx_Iix c fun h => (le_of_lt h).trans c.2.2

@[simp]
/--
lemma `image_subtype_val_Ioo_Ici` / 引理 `image_subtype_val_Ioo_Ici`

English:
lemma image_subtype_val_Ioo_Ici
  given: {a b : α} (c : Ioo a b)
  statement: Subtype.val '' Ici c = Ico c.1 b
  proof: image_subtype_val_Ixx_Ixi c c.2.1.trans_le

@[simp]

中文:
引理 image_subtype_val_Ioo_Ici
  条件: {a b : α} (c : 开区间 a b)
  结论: 子类型.val '' 左闭右无界区间 c = 左闭右开区间 c.1 b
  证明: image_subtype_val_Ixx_Ixi c c.2.1.trans_le

@[simp]

Depends on / 依赖: image_subtype_val_Ixx_Ixi, trans_le
-/
lemma image_subtype_val_Ioo_Ici {a b : α} (c : Ioo a b) : Subtype.val '' Ici c = Ico c.1 b :=
  image_subtype_val_Ixx_Ixi c c.2.1.trans_le

@[simp]
/--
lemma `image_subtype_val_Ioo_Iic` / 引理 `image_subtype_val_Ioo_Iic`

English:
lemma image_subtype_val_Ioo_Iic
  given: {a b : α} (c : Ioo a b)
  statement: Subtype.val '' Iic c = Ioc a c
  proof: image_subtype_val_Ixx_Iix c (lt_of_le_of_lt · c.2.2)

@[simp]

中文:
引理 image_subtype_val_Ioo_Iic
  条件: {a b : α} (c : 开区间 a b)
  结论: 子类型.val '' 左无界右闭区间 c = 左开右闭区间 a c
  证明: image_subtype_val_Ixx_Iix c (lt_of_le_of_lt · c.2.2)

@[simp]

Depends on / 依赖: image_subtype_val_Ixx_Iix, lt_of_le_of_lt
-/
lemma image_subtype_val_Ioo_Iic {a b : α} (c : Ioo a b) : Subtype.val '' Iic c = Ioc a c :=
  image_subtype_val_Ixx_Iix c (lt_of_le_of_lt · c.2.2)

@[simp]
/--
lemma `image_subtype_val_Ioo_Ioi` / 引理 `image_subtype_val_Ioo_Ioi`

English:
lemma image_subtype_val_Ioo_Ioi
  given: {a b : α} (c : Ioo a b)
  statement: Subtype.val '' Ioi c = Ioo c.1 b
  proof: image_subtype_val_Ixx_Ixi c c.2.1.trans

@[simp]

中文:
引理 image_subtype_val_Ioo_Ioi
  条件: {a b : α} (c : 开区间 a b)
  结论: 子类型.val '' 左开右无界区间 c = 开区间 c.1 b
  证明: image_subtype_val_Ixx_Ixi c c.2.1.trans

@[simp]

Depends on / 依赖: image_subtype_val_Ixx_Ixi
-/
lemma image_subtype_val_Ioo_Ioi {a b : α} (c : Ioo a b) : Subtype.val '' Ioi c = Ioo c.1 b :=
  image_subtype_val_Ixx_Ixi c c.2.1.trans

@[simp]
/--
lemma `image_subtype_val_Ioo_Iio` / 引理 `image_subtype_val_Ioo_Iio`

English:
lemma image_subtype_val_Ioo_Iio
  given: {a b : α} (c : Ioo a b)
  statement: Subtype.val '' Iio c = Ioo a c
  proof: image_subtype_val_Ixx_Iix c (lt_trans · c.2.2)

中文:
引理 image_subtype_val_Ioo_Iio
  条件: {a b : α} (c : 开区间 a b)
  结论: 子类型.val '' 左无界右开区间 c = 开区间 a c
  证明: image_subtype_val_Ixx_Iix c (lt_trans · c.2.2)

Depends on / 依赖: image_subtype_val_Ixx_Iix, lt_trans
-/
lemma image_subtype_val_Ioo_Iio {a b : α} (c : Ioo a b) : Subtype.val '' Iio c = Ioo a c :=
  image_subtype_val_Ixx_Iix c (lt_trans · c.2.2)

end Set

section Preorder
variable [Preorder α]

/--
lemma `directedOn_le_Iic` / 引理 `directedOn_le_Iic`

English:
lemma directedOn_le_Iic
  given: (b : α)
  statement: DirectedOn (· <= ·) (Iic b)
  proof: fun _x hx _y hy => ⟨b, le_rfl, hx, hy⟩

中文:
引理 directedOn_le_Iic
  条件: (b : α)
  结论: DirectedOn (· <= ·) (左无界右闭区间 b)
  证明: fun _x hx _y hy => ⟨b, le_rfl, hx, hy⟩

Depends on / 依赖: le_rfl
-/
lemma directedOn_le_Iic (b : α) : DirectedOn (· <= ·) (Iic b) :=
  fun _x hx _y hy => ⟨b, le_rfl, hx, hy⟩

/--
lemma `directedOn_le_Icc` / 引理 `directedOn_le_Icc`

English:
lemma directedOn_le_Icc
  given: (a b : α)
  statement: DirectedOn (· <= ·) (Icc a b)
  proof: fun _x hx _y hy => ⟨b, right_mem_Icc.2 hx.1.trans hx.2, hx.2, hy.2⟩

中文:
引理 directedOn_le_Icc
  条件: (a b : α)
  结论: DirectedOn (· <= ·) (闭区间 a b)
  证明: fun _x hx _y hy => ⟨b, right_mem_Icc.2 hx.1.trans hx.2, hx.2, hy.2⟩

Depends on / 依赖: right_mem_Icc
-/
lemma directedOn_le_Icc (a b : α) : DirectedOn (· <= ·) (Icc a b) :=
fun _x hx _y hy => ⟨b, right_mem_Icc.2 hx.1.trans hx.2, hx.2, hy.2⟩

/--
lemma `directedOn_le_Ioc` / 引理 `directedOn_le_Ioc`

English:
lemma directedOn_le_Ioc
  given: (a b : α)
  statement: DirectedOn (· <= ·) (Ioc a b)
  proof: fun _x hx _y hy => ⟨b, right_mem_Ioc.2 hx.1.trans_le hx.2, hx.2, hy.2⟩

中文:
引理 directedOn_le_Ioc
  条件: (a b : α)
  结论: DirectedOn (· <= ·) (左开右闭区间 a b)
  证明: fun _x hx _y hy => ⟨b, right_mem_Ioc.2 hx.1.trans_le hx.2, hx.2, hy.2⟩

Depends on / 依赖: right_mem_Ioc, trans_le
-/
lemma directedOn_le_Ioc (a b : α) : DirectedOn (· <= ·) (Ioc a b) :=
fun _x hx _y hy => ⟨b, right_mem_Ioc.2 hx.1.trans_le hx.2, hx.2, hy.2⟩

/--
lemma `directedOn_ge_Ici` / 引理 `directedOn_ge_Ici`

English:
lemma directedOn_ge_Ici
  given: (a : α)
  statement: DirectedOn (· >= ·) (Ici a)
  proof: fun _x hx _y hy => ⟨a, le_rfl, hx, hy⟩

中文:
引理 directedOn_ge_Ici
  条件: (a : α)
  结论: DirectedOn (· >= ·) (左闭右无界区间 a)
  证明: fun _x hx _y hy => ⟨a, le_rfl, hx, hy⟩

Depends on / 依赖: le_rfl
-/
lemma directedOn_ge_Ici (a : α) : DirectedOn (· >= ·) (Ici a) :=
  fun _x hx _y hy => ⟨a, le_rfl, hx, hy⟩

/--
lemma `directedOn_ge_Icc` / 引理 `directedOn_ge_Icc`

English:
lemma directedOn_ge_Icc
  given: (a b : α)
  statement: DirectedOn (· >= ·) (Icc a b)
  proof: fun _x hx _y hy => ⟨a, left_mem_Icc.2 hx.1.trans hx.2, hx.1, hy.1⟩

中文:
引理 directedOn_ge_Icc
  条件: (a b : α)
  结论: DirectedOn (· >= ·) (闭区间 a b)
  证明: fun _x hx _y hy => ⟨a, left_mem_Icc.2 hx.1.trans hx.2, hx.1, hy.1⟩

Depends on / 依赖: left_mem_Icc
-/
lemma directedOn_ge_Icc (a b : α) : DirectedOn (· >= ·) (Icc a b) :=
fun _x hx _y hy => ⟨a, left_mem_Icc.2 hx.1.trans hx.2, hx.1, hy.1⟩

/--
lemma `directedOn_ge_Ico` / 引理 `directedOn_ge_Ico`

English:
lemma directedOn_ge_Ico
  given: (a b : α)
  statement: DirectedOn (· >= ·) (Ico a b)
  proof: fun _x hx _y hy => ⟨a, left_mem_Ico.2 hx.1.trans_lt hx.2, hx.1, hy.1⟩

中文:
引理 directedOn_ge_Ico
  条件: (a b : α)
  结论: DirectedOn (· >= ·) (左闭右开区间 a b)
  证明: fun _x hx _y hy => ⟨a, left_mem_Ico.2 hx.1.trans_lt hx.2, hx.1, hy.1⟩

Depends on / 依赖: left_mem_Ico, trans_lt
-/
lemma directedOn_ge_Ico (a b : α) : DirectedOn (· >= ·) (Ico a b) :=
fun _x hx _y hy => ⟨a, left_mem_Ico.2 hx.1.trans_lt hx.2, hx.1, hy.1⟩

end Preorder
