/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Monotone
public import Mathlib.Order.Interval.Set.Disjoint
public import Mathlib.Order.SuccPred.Archimedean

/-!
# Monotonicity on intervals

In this file we prove that `Set.Ici` etc. are monotone/antitone functions. We also prove some lemmas
about functions monotone on intervals in `SuccOrder`s.
-/

public section


open Set

section Ixx

variable {α β : Type*} [Preorder α] [Preorder β] {f g : α -> β} {s : Set α}

/--
theorem `antitone_Ici` / 定理 `antitone_Ici`

English:
theorem antitone_Ici
  statement: Antitone (Ici : α -> Set α)
  proof: fun _ _ => Ici_subset_Ici.2

中文:
定理 antitone_Ici
  结论: 递减 (左闭右无界区间 : α -> 集合 α)
  证明: fun _ _ => Ici_subset_Ici.2

Depends on / 依赖: Ici_subset_Ici
-/
theorem antitone_Ici : Antitone (Ici : α -> Set α) := fun _ _ => Ici_subset_Ici.2

/--
theorem `monotone_Iic` / 定理 `monotone_Iic`

English:
theorem monotone_Iic
  statement: Monotone (Iic : α -> Set α)
  proof: fun _ _ => Iic_subset_Iic.2

中文:
定理 monotone_Iic
  结论: 递增 (左无界右闭区间 : α -> 集合 α)
  证明: fun _ _ => Iic_subset_Iic.2

Depends on / 依赖: Iic_subset_Iic
-/
theorem monotone_Iic : Monotone (Iic : α -> Set α) := fun _ _ => Iic_subset_Iic.2

/--
theorem `antitone_Ioi` / 定理 `antitone_Ioi`

English:
theorem antitone_Ioi
  statement: Antitone (Ioi : α -> Set α)
  proof: fun _ _ => Ioi_subset_Ioi

中文:
定理 antitone_Ioi
  结论: 递减 (左开右无界区间 : α -> 集合 α)
  证明: fun _ _ => Ioi_subset_Ioi

Depends on / 依赖: Ioi_subset_Ioi
-/
theorem antitone_Ioi : Antitone (Ioi : α -> Set α) := fun _ _ => Ioi_subset_Ioi

/--
theorem `monotone_Iio` / 定理 `monotone_Iio`

English:
theorem monotone_Iio
  statement: Monotone (Iio : α -> Set α)
  proof: fun _ _ => Iio_subset_Iio

中文:
定理 monotone_Iio
  结论: 递增 (左无界右开区间 : α -> 集合 α)
  证明: fun _ _ => Iio_subset_Iio

Depends on / 依赖: Iio_subset_Iio
-/
theorem monotone_Iio : Monotone (Iio : α -> Set α) := fun _ _ => Iio_subset_Iio

/--
theorem `Monotone.Ici` / 定理 `Monotone.Ici`

English:
theorem Monotone.Ici
  given: (hf : Monotone f)
  statement: Antitone fun x => Ici (f x)
  proof: antitone_Ici.comp_monotone hf

中文:
定理 递增.左闭右无界区间
  条件: (hf : 递增 f)
  结论: 递减 fun x => 左闭右无界区间 (f x)
  证明: antitone_Ici.comp_monotone hf
-/
protected theorem Monotone.Ici (hf : Monotone f) : Antitone fun x => Ici (f x) :=
  antitone_Ici.comp_monotone hf

/--
theorem `MonotoneOn.Ici` / 定理 `MonotoneOn.Ici`

English:
theorem MonotoneOn.Ici
  given: (hf : MonotoneOn f s)
  statement: AntitoneOn (fun x => Ici (f x)) s
  proof: antitone_Ici.comp_monotoneOn hf

中文:
定理 MonotoneOn.左闭右无界区间
  条件: (hf : MonotoneOn f s)
  结论: AntitoneOn (fun x => 左闭右无界区间 (f x)) s
  证明: antitone_Ici.comp_monotoneOn hf
-/
protected theorem MonotoneOn.Ici (hf : MonotoneOn f s) : AntitoneOn (fun x => Ici (f x)) s :=
  antitone_Ici.comp_monotoneOn hf

/--
theorem `Antitone.Ici` / 定理 `Antitone.Ici`

English:
theorem Antitone.Ici
  given: (hf : Antitone f)
  statement: Monotone fun x => Ici (f x)
  proof: antitone_Ici.comp hf

中文:
定理 递减.左闭右无界区间
  条件: (hf : 递减 f)
  结论: 递增 fun x => 左闭右无界区间 (f x)
  证明: antitone_Ici.comp hf
-/
protected theorem Antitone.Ici (hf : Antitone f) : Monotone fun x => Ici (f x) :=
  antitone_Ici.comp hf

/--
theorem `AntitoneOn.Ici` / 定理 `AntitoneOn.Ici`

English:
theorem AntitoneOn.Ici
  given: (hf : AntitoneOn f s)
  statement: MonotoneOn (fun x => Ici (f x)) s
  proof: antitone_Ici.comp_antitoneOn hf

中文:
定理 AntitoneOn.左闭右无界区间
  条件: (hf : AntitoneOn f s)
  结论: MonotoneOn (fun x => 左闭右无界区间 (f x)) s
  证明: antitone_Ici.comp_antitoneOn hf
-/
protected theorem AntitoneOn.Ici (hf : AntitoneOn f s) : MonotoneOn (fun x => Ici (f x)) s :=
  antitone_Ici.comp_antitoneOn hf

/--
theorem `Monotone.Iic` / 定理 `Monotone.Iic`

English:
theorem Monotone.Iic
  given: (hf : Monotone f)
  statement: Monotone fun x => Iic (f x)
  proof: monotone_Iic.comp hf

中文:
定理 递增.左无界右闭区间
  条件: (hf : 递增 f)
  结论: 递增 fun x => 左无界右闭区间 (f x)
  证明: monotone_Iic.comp hf
-/
protected theorem Monotone.Iic (hf : Monotone f) : Monotone fun x => Iic (f x) :=
  monotone_Iic.comp hf

/--
theorem `MonotoneOn.Iic` / 定理 `MonotoneOn.Iic`

English:
theorem MonotoneOn.Iic
  given: (hf : MonotoneOn f s)
  statement: MonotoneOn (fun x => Iic (f x)) s
  proof: monotone_Iic.comp_monotoneOn hf

中文:
定理 MonotoneOn.左无界右闭区间
  条件: (hf : MonotoneOn f s)
  结论: MonotoneOn (fun x => 左无界右闭区间 (f x)) s
  证明: monotone_Iic.comp_monotoneOn hf
-/
protected theorem MonotoneOn.Iic (hf : MonotoneOn f s) : MonotoneOn (fun x => Iic (f x)) s :=
  monotone_Iic.comp_monotoneOn hf

/--
theorem `Antitone.Iic` / 定理 `Antitone.Iic`

English:
theorem Antitone.Iic
  given: (hf : Antitone f)
  statement: Antitone fun x => Iic (f x)
  proof: monotone_Iic.comp_antitone hf

中文:
定理 递减.左无界右闭区间
  条件: (hf : 递减 f)
  结论: 递减 fun x => 左无界右闭区间 (f x)
  证明: monotone_Iic.comp_antitone hf
-/
protected theorem Antitone.Iic (hf : Antitone f) : Antitone fun x => Iic (f x) :=
  monotone_Iic.comp_antitone hf

/--
theorem `AntitoneOn.Iic` / 定理 `AntitoneOn.Iic`

English:
theorem AntitoneOn.Iic
  given: (hf : AntitoneOn f s)
  statement: AntitoneOn (fun x => Iic (f x)) s
  proof: monotone_Iic.comp_antitoneOn hf

中文:
定理 AntitoneOn.左无界右闭区间
  条件: (hf : AntitoneOn f s)
  结论: AntitoneOn (fun x => 左无界右闭区间 (f x)) s
  证明: monotone_Iic.comp_antitoneOn hf
-/
protected theorem AntitoneOn.Iic (hf : AntitoneOn f s) : AntitoneOn (fun x => Iic (f x)) s :=
  monotone_Iic.comp_antitoneOn hf

/--
theorem `Monotone.Ioi` / 定理 `Monotone.Ioi`

English:
theorem Monotone.Ioi
  given: (hf : Monotone f)
  statement: Antitone fun x => Ioi (f x)
  proof: antitone_Ioi.comp_monotone hf

中文:
定理 递增.左开右无界区间
  条件: (hf : 递增 f)
  结论: 递减 fun x => 左开右无界区间 (f x)
  证明: antitone_Ioi.comp_monotone hf
-/
protected theorem Monotone.Ioi (hf : Monotone f) : Antitone fun x => Ioi (f x) :=
  antitone_Ioi.comp_monotone hf

/--
theorem `MonotoneOn.Ioi` / 定理 `MonotoneOn.Ioi`

English:
theorem MonotoneOn.Ioi
  given: (hf : MonotoneOn f s)
  statement: AntitoneOn (fun x => Ioi (f x)) s
  proof: antitone_Ioi.comp_monotoneOn hf

中文:
定理 MonotoneOn.左开右无界区间
  条件: (hf : MonotoneOn f s)
  结论: AntitoneOn (fun x => 左开右无界区间 (f x)) s
  证明: antitone_Ioi.comp_monotoneOn hf
-/
protected theorem MonotoneOn.Ioi (hf : MonotoneOn f s) : AntitoneOn (fun x => Ioi (f x)) s :=
  antitone_Ioi.comp_monotoneOn hf

/--
theorem `Antitone.Ioi` / 定理 `Antitone.Ioi`

English:
theorem Antitone.Ioi
  given: (hf : Antitone f)
  statement: Monotone fun x => Ioi (f x)
  proof: antitone_Ioi.comp hf

中文:
定理 递减.左开右无界区间
  条件: (hf : 递减 f)
  结论: 递增 fun x => 左开右无界区间 (f x)
  证明: antitone_Ioi.comp hf
-/
protected theorem Antitone.Ioi (hf : Antitone f) : Monotone fun x => Ioi (f x) :=
  antitone_Ioi.comp hf

/--
theorem `AntitoneOn.Ioi` / 定理 `AntitoneOn.Ioi`

English:
theorem AntitoneOn.Ioi
  given: (hf : AntitoneOn f s)
  statement: MonotoneOn (fun x => Ioi (f x)) s
  proof: antitone_Ioi.comp_antitoneOn hf

中文:
定理 AntitoneOn.左开右无界区间
  条件: (hf : AntitoneOn f s)
  结论: MonotoneOn (fun x => 左开右无界区间 (f x)) s
  证明: antitone_Ioi.comp_antitoneOn hf
-/
protected theorem AntitoneOn.Ioi (hf : AntitoneOn f s) : MonotoneOn (fun x => Ioi (f x)) s :=
  antitone_Ioi.comp_antitoneOn hf

/--
theorem `Monotone.Iio` / 定理 `Monotone.Iio`

English:
theorem Monotone.Iio
  given: (hf : Monotone f)
  statement: Monotone fun x => Iio (f x)
  proof: monotone_Iio.comp hf

中文:
定理 递增.左无界右开区间
  条件: (hf : 递增 f)
  结论: 递增 fun x => 左无界右开区间 (f x)
  证明: monotone_Iio.comp hf
-/
protected theorem Monotone.Iio (hf : Monotone f) : Monotone fun x => Iio (f x) :=
  monotone_Iio.comp hf

/--
theorem `MonotoneOn.Iio` / 定理 `MonotoneOn.Iio`

English:
theorem MonotoneOn.Iio
  given: (hf : MonotoneOn f s)
  statement: MonotoneOn (fun x => Iio (f x)) s
  proof: monotone_Iio.comp_monotoneOn hf

中文:
定理 MonotoneOn.左无界右开区间
  条件: (hf : MonotoneOn f s)
  结论: MonotoneOn (fun x => 左无界右开区间 (f x)) s
  证明: monotone_Iio.comp_monotoneOn hf
-/
protected theorem MonotoneOn.Iio (hf : MonotoneOn f s) : MonotoneOn (fun x => Iio (f x)) s :=
  monotone_Iio.comp_monotoneOn hf

/--
theorem `Antitone.Iio` / 定理 `Antitone.Iio`

English:
theorem Antitone.Iio
  given: (hf : Antitone f)
  statement: Antitone fun x => Iio (f x)
  proof: monotone_Iio.comp_antitone hf

中文:
定理 递减.左无界右开区间
  条件: (hf : 递减 f)
  结论: 递减 fun x => 左无界右开区间 (f x)
  证明: monotone_Iio.comp_antitone hf
-/
protected theorem Antitone.Iio (hf : Antitone f) : Antitone fun x => Iio (f x) :=
  monotone_Iio.comp_antitone hf

/--
theorem `AntitoneOn.Iio` / 定理 `AntitoneOn.Iio`

English:
theorem AntitoneOn.Iio
  given: (hf : AntitoneOn f s)
  statement: AntitoneOn (fun x => Iio (f x)) s
  proof: monotone_Iio.comp_antitoneOn hf

中文:
定理 AntitoneOn.左无界右开区间
  条件: (hf : AntitoneOn f s)
  结论: AntitoneOn (fun x => 左无界右开区间 (f x)) s
  证明: monotone_Iio.comp_antitoneOn hf
-/
protected theorem AntitoneOn.Iio (hf : AntitoneOn f s) : AntitoneOn (fun x => Iio (f x)) s :=
  monotone_Iio.comp_antitoneOn hf

/--
theorem `Monotone.Icc` / 定理 `Monotone.Icc`

English:
theorem Monotone.Icc
  given: (hf : Monotone f) (hg : Antitone g)
  proof: hf.Ici.inter hg.Iic

中文:
定理 递增.闭区间
  条件: (hf : 递增 f) (hg : 递减 g)
  证明: hf.Ici.inter hg.Iic
-/
protected theorem Monotone.Icc (hf : Monotone f) (hg : Antitone g) :
    Antitone fun x => Icc (f x) (g x) :=
  hf.Ici.inter hg.Iic

/--
theorem `MonotoneOn.Icc` / 定理 `MonotoneOn.Icc`

English:
theorem MonotoneOn.Icc
  given: (hf : MonotoneOn f s) (hg : AntitoneOn g s)
  proof: hf.Ici.inter hg.Iic

中文:
定理 MonotoneOn.闭区间
  条件: (hf : MonotoneOn f s) (hg : AntitoneOn g s)
  证明: hf.Ici.inter hg.Iic
-/
protected theorem MonotoneOn.Icc (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => Icc (f x) (g x)) s :=
  hf.Ici.inter hg.Iic

/--
theorem `Antitone.Icc` / 定理 `Antitone.Icc`

English:
theorem Antitone.Icc
  given: (hf : Antitone f) (hg : Monotone g)
  proof: hf.Ici.inter hg.Iic

中文:
定理 递减.闭区间
  条件: (hf : 递减 f) (hg : 递增 g)
  证明: hf.Ici.inter hg.Iic
-/
protected theorem Antitone.Icc (hf : Antitone f) (hg : Monotone g) :
    Monotone fun x => Icc (f x) (g x) :=
  hf.Ici.inter hg.Iic

/--
theorem `AntitoneOn.Icc` / 定理 `AntitoneOn.Icc`

English:
theorem AntitoneOn.Icc
  given: (hf : AntitoneOn f s) (hg : MonotoneOn g s)
  proof: hf.Ici.inter hg.Iic

中文:
定理 AntitoneOn.闭区间
  条件: (hf : AntitoneOn f s) (hg : MonotoneOn g s)
  证明: hf.Ici.inter hg.Iic
-/
protected theorem AntitoneOn.Icc (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => Icc (f x) (g x)) s :=
  hf.Ici.inter hg.Iic

/--
theorem `Monotone.Ico` / 定理 `Monotone.Ico`

English:
theorem Monotone.Ico
  given: (hf : Monotone f) (hg : Antitone g)
  proof: hf.Ici.inter hg.Iio

中文:
定理 递增.左闭右开区间
  条件: (hf : 递增 f) (hg : 递减 g)
  证明: hf.Ici.inter hg.Iio
-/
protected theorem Monotone.Ico (hf : Monotone f) (hg : Antitone g) :
    Antitone fun x => Ico (f x) (g x) :=
  hf.Ici.inter hg.Iio

/--
theorem `MonotoneOn.Ico` / 定理 `MonotoneOn.Ico`

English:
theorem MonotoneOn.Ico
  given: (hf : MonotoneOn f s) (hg : AntitoneOn g s)
  proof: hf.Ici.inter hg.Iio

中文:
定理 MonotoneOn.左闭右开区间
  条件: (hf : MonotoneOn f s) (hg : AntitoneOn g s)
  证明: hf.Ici.inter hg.Iio
-/
protected theorem MonotoneOn.Ico (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => Ico (f x) (g x)) s :=
  hf.Ici.inter hg.Iio

/--
theorem `Antitone.Ico` / 定理 `Antitone.Ico`

English:
theorem Antitone.Ico
  given: (hf : Antitone f) (hg : Monotone g)
  proof: hf.Ici.inter hg.Iio

中文:
定理 递减.左闭右开区间
  条件: (hf : 递减 f) (hg : 递增 g)
  证明: hf.Ici.inter hg.Iio
-/
protected theorem Antitone.Ico (hf : Antitone f) (hg : Monotone g) :
    Monotone fun x => Ico (f x) (g x) :=
  hf.Ici.inter hg.Iio

/--
theorem `AntitoneOn.Ico` / 定理 `AntitoneOn.Ico`

English:
theorem AntitoneOn.Ico
  given: (hf : AntitoneOn f s) (hg : MonotoneOn g s)
  proof: hf.Ici.inter hg.Iio

中文:
定理 AntitoneOn.左闭右开区间
  条件: (hf : AntitoneOn f s) (hg : MonotoneOn g s)
  证明: hf.Ici.inter hg.Iio
-/
protected theorem AntitoneOn.Ico (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => Ico (f x) (g x)) s :=
  hf.Ici.inter hg.Iio

/--
theorem `Monotone.Ioc` / 定理 `Monotone.Ioc`

English:
theorem Monotone.Ioc
  given: (hf : Monotone f) (hg : Antitone g)
  proof: hf.Ioi.inter hg.Iic

中文:
定理 递增.左开右闭区间
  条件: (hf : 递增 f) (hg : 递减 g)
  证明: hf.Ioi.inter hg.Iic
-/
protected theorem Monotone.Ioc (hf : Monotone f) (hg : Antitone g) :
    Antitone fun x => Ioc (f x) (g x) :=
  hf.Ioi.inter hg.Iic

/--
theorem `MonotoneOn.Ioc` / 定理 `MonotoneOn.Ioc`

English:
theorem MonotoneOn.Ioc
  given: (hf : MonotoneOn f s) (hg : AntitoneOn g s)
  proof: hf.Ioi.inter hg.Iic

中文:
定理 MonotoneOn.左开右闭区间
  条件: (hf : MonotoneOn f s) (hg : AntitoneOn g s)
  证明: hf.Ioi.inter hg.Iic
-/
protected theorem MonotoneOn.Ioc (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => Ioc (f x) (g x)) s :=
  hf.Ioi.inter hg.Iic

/--
theorem `Antitone.Ioc` / 定理 `Antitone.Ioc`

English:
theorem Antitone.Ioc
  given: (hf : Antitone f) (hg : Monotone g)
  proof: hf.Ioi.inter hg.Iic

中文:
定理 递减.左开右闭区间
  条件: (hf : 递减 f) (hg : 递增 g)
  证明: hf.Ioi.inter hg.Iic
-/
protected theorem Antitone.Ioc (hf : Antitone f) (hg : Monotone g) :
    Monotone fun x => Ioc (f x) (g x) :=
  hf.Ioi.inter hg.Iic

/--
theorem `AntitoneOn.Ioc` / 定理 `AntitoneOn.Ioc`

English:
theorem AntitoneOn.Ioc
  given: (hf : AntitoneOn f s) (hg : MonotoneOn g s)
  proof: hf.Ioi.inter hg.Iic

中文:
定理 AntitoneOn.左开右闭区间
  条件: (hf : AntitoneOn f s) (hg : MonotoneOn g s)
  证明: hf.Ioi.inter hg.Iic
-/
protected theorem AntitoneOn.Ioc (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => Ioc (f x) (g x)) s :=
  hf.Ioi.inter hg.Iic

/--
theorem `Monotone.Ioo` / 定理 `Monotone.Ioo`

English:
theorem Monotone.Ioo
  given: (hf : Monotone f) (hg : Antitone g)
  proof: hf.Ioi.inter hg.Iio

中文:
定理 递增.开区间
  条件: (hf : 递增 f) (hg : 递减 g)
  证明: hf.Ioi.inter hg.Iio
-/
protected theorem Monotone.Ioo (hf : Monotone f) (hg : Antitone g) :
    Antitone fun x => Ioo (f x) (g x) :=
  hf.Ioi.inter hg.Iio

/--
theorem `MonotoneOn.Ioo` / 定理 `MonotoneOn.Ioo`

English:
theorem MonotoneOn.Ioo
  given: (hf : MonotoneOn f s) (hg : AntitoneOn g s)
  proof: hf.Ioi.inter hg.Iio

中文:
定理 MonotoneOn.开区间
  条件: (hf : MonotoneOn f s) (hg : AntitoneOn g s)
  证明: hf.Ioi.inter hg.Iio
-/
protected theorem MonotoneOn.Ioo (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => Ioo (f x) (g x)) s :=
  hf.Ioi.inter hg.Iio

/--
theorem `Antitone.Ioo` / 定理 `Antitone.Ioo`

English:
theorem Antitone.Ioo
  given: (hf : Antitone f) (hg : Monotone g)
  proof: hf.Ioi.inter hg.Iio

中文:
定理 递减.开区间
  条件: (hf : 递减 f) (hg : 递增 g)
  证明: hf.Ioi.inter hg.Iio
-/
protected theorem Antitone.Ioo (hf : Antitone f) (hg : Monotone g) :
    Monotone fun x => Ioo (f x) (g x) :=
  hf.Ioi.inter hg.Iio

/--
theorem `AntitoneOn.Ioo` / 定理 `AntitoneOn.Ioo`

English:
theorem AntitoneOn.Ioo
  given: (hf : AntitoneOn f s) (hg : MonotoneOn g s)
  proof: hf.Ioi.inter hg.Iio

中文:
定理 AntitoneOn.开区间
  条件: (hf : AntitoneOn f s) (hg : MonotoneOn g s)
  证明: hf.Ioi.inter hg.Iio
-/
protected theorem AntitoneOn.Ioo (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => Ioo (f x) (g x)) s :=
  hf.Ioi.inter hg.Iio

end Ixx

section iUnion

variable {α β : Type*} [SemilatticeSup α] [LinearOrder β] {f g : α -> β} {a b : β}

/--
theorem `iUnion_Ioo_of_mono_of_isGLB_of_isLUB` / 定理 `iUnion_Ioo_of_mono_of_isGLB_of_isLUB`

English:
theorem iUnion_Ioo_of_mono_of_isGLB_of_isLUB
  statement: (hf : Antitone f) (hg : Monotone g)
  proof: calc
    ⋃ x, Ioo (f x) (g x) = (⋃ x, Ioi (f x)) inter ⋃ x, Iio (g x) :=
      iUnion_inter_of_monotone hf.Ioi hg.Iio
    _ = Ioi a inter Iio b := congr_arg₂ (· inter ·) ha.iUnion_Ioi_eq hb.iUnion_Iio_eq

中文:
定理 iUnion_Ioo_of_mono_of_isGLB_of_isLUB
  结论: (hf : 递减 f) (hg : 递增 g)
  证明: calc
    ⋃ x, Ioo (f x) (g x) = (⋃ x, Ioi (f x)) inter ⋃ x, Iio (g x) :=
      iUnion_inter_of_monotone hf.Ioi hg.Iio
    _ = Ioi a inter Iio b := congr_arg₂ (· inter ·) ha.iUnion_Ioi_eq hb.iUnion_Iio_eq

Depends on / 依赖: ha.iUnion_Ioi_eq, hb.iUnion_Iio_eq, hf.Ioi, hg.Iio, iUnion_Iio_eq, iUnion_Ioi_eq, iUnion_inter_of_monotone
-/
theorem iUnion_Ioo_of_mono_of_isGLB_of_isLUB (hf : Antitone f) (hg : Monotone g)
    (ha : IsGLB (range f) a) (hb : IsLUB (range g) b) : ⋃ x, Ioo (f x) (g x) = Ioo a b :=
  calc
    ⋃ x, Ioo (f x) (g x) = (⋃ x, Ioi (f x)) inter ⋃ x, Iio (g x) :=
      iUnion_inter_of_monotone hf.Ioi hg.Iio
    _ = Ioi a inter Iio b := congr_arg₂ (· inter ·) ha.iUnion_Ioi_eq hb.iUnion_Iio_eq

end iUnion

section SuccOrder

open Order

variable {α β : Type*} [PartialOrder α] [Preorder β] {ψ : α -> β}

/--
theorem `strictMonoOn_Iic_of_lt_succ` / 定理 `strictMonoOn_Iic_of_lt_succ`

English:
theorem strictMonoOn_Iic_of_lt_succ
  statement: [SuccOrder α] [IsSuccArchimedean α] {n : α}
  proof: strictMonoOn_of_lt_succ ordConnected_Iic fun _a ha' _ ha =>
hψ _ (succ_le_iff_of_not_isMax ha').1 ha

中文:
定理 strictMonoOn_Iic_of_lt_succ
  结论: [Succ序 α] [是SuccArchimedean α] {n : α}
  证明: strictMonoOn_of_lt_succ ordConnected_Iic fun _a ha' _ ha =>
hψ _ (succ_le_iff_of_not_isMax ha').1 ha

Depends on / 依赖: ordConnected_Iic, strictMonoOn_of_lt_succ, succ_le_iff_of_not_isMax
-/
theorem strictMonoOn_Iic_of_lt_succ [SuccOrder α] [IsSuccArchimedean α] {n : α}
    (hψ : forall m, m < n -> ψ m < ψ (succ m)) : StrictMonoOn ψ (Set.Iic n) :=
  strictMonoOn_of_lt_succ ordConnected_Iic fun _a ha' _ ha =>
hψ _ (succ_le_iff_of_not_isMax ha').1 ha

/--
theorem `strictAntiOn_Iic_of_succ_lt` / 定理 `strictAntiOn_Iic_of_succ_lt`

English:
theorem strictAntiOn_Iic_of_succ_lt
  statement: [SuccOrder α] [IsSuccArchimedean α] {n : α}
  proof: fun i hi j hj hij =>
  @strictMonoOn_Iic_of_lt_succ α βᵒᵈ _ _ ψ _ _ n hψ i hi j hj hij

中文:
定理 strictAntiOn_Iic_of_succ_lt
  结论: [Succ序 α] [是SuccArchimedean α] {n : α}
  证明: fun i hi j hj hij =>
  @strictMonoOn_Iic_of_lt_succ α βᵒᵈ _ _ ψ _ _ n hψ i hi j hj hij
-/
theorem strictAntiOn_Iic_of_succ_lt [SuccOrder α] [IsSuccArchimedean α] {n : α}
    (hψ : forall m, m < n -> ψ (succ m) < ψ m) : StrictAntiOn ψ (Set.Iic n) := fun i hi j hj hij =>
  @strictMonoOn_Iic_of_lt_succ α βᵒᵈ _ _ ψ _ _ n hψ i hi j hj hij

/--
theorem `strictMonoOn_Ici_of_pred_lt` / 定理 `strictMonoOn_Ici_of_pred_lt`

English:
theorem strictMonoOn_Ici_of_pred_lt
  statement: [PredOrder α] [IsPredArchimedean α] {n : α}
  proof: fun i hi j hj hij =>
  @strictMonoOn_Iic_of_lt_succ αᵒᵈ βᵒᵈ _ _ ψ _ _ n hψ j hj i hi hij

中文:
定理 strictMonoOn_Ici_of_pred_lt
  结论: [Pred序 α] [是PredArchimedean α] {n : α}
  证明: fun i hi j hj hij =>
  @strictMonoOn_Iic_of_lt_succ αᵒᵈ βᵒᵈ _ _ ψ _ _ n hψ j hj i hi hij
-/
theorem strictMonoOn_Ici_of_pred_lt [PredOrder α] [IsPredArchimedean α] {n : α}
    (hψ : forall m, n < m -> ψ (pred m) < ψ m) : StrictMonoOn ψ (Set.Ici n) := fun i hi j hj hij =>
  @strictMonoOn_Iic_of_lt_succ αᵒᵈ βᵒᵈ _ _ ψ _ _ n hψ j hj i hi hij

/--
theorem `strictAntiOn_Ici_of_lt_pred` / 定理 `strictAntiOn_Ici_of_lt_pred`

English:
theorem strictAntiOn_Ici_of_lt_pred
  statement: [PredOrder α] [IsPredArchimedean α] {n : α}
  proof: fun i hi j hj hij =>
  @strictAntiOn_Iic_of_succ_lt αᵒᵈ βᵒᵈ _ _ ψ _ _ n hψ j hj i hi hij

中文:
定理 strictAntiOn_Ici_of_lt_pred
  结论: [Pred序 α] [是PredArchimedean α] {n : α}
  证明: fun i hi j hj hij =>
  @strictAntiOn_Iic_of_succ_lt αᵒᵈ βᵒᵈ _ _ ψ _ _ n hψ j hj i hi hij
-/
theorem strictAntiOn_Ici_of_lt_pred [PredOrder α] [IsPredArchimedean α] {n : α}
    (hψ : forall m, n < m -> ψ m < ψ (pred m)) : StrictAntiOn ψ (Set.Ici n) := fun i hi j hj hij =>
  @strictAntiOn_Iic_of_succ_lt αᵒᵈ βᵒᵈ _ _ ψ _ _ n hψ j hj i hi hij

end SuccOrder

section LinearOrder

open Order

variable {α : Type*} [LinearOrder α]

/--
theorem `StrictMonoOn.Iic_id_le` / 定理 `StrictMonoOn.Iic_id_le`

English:
theorem StrictMonoOn.Iic_id_le
  statement: [SuccOrder α] [IsSuccArchimedean α] [OrderBot α] {n : α} {φ : α -> α}
  proof: by
  revert hφ
  refine
    Succ.rec_bot (fun n => StrictMonoOn φ (Set.Iic n) -> forall m <= n, m <= φ m)
      (fun _ _ hm => hm.trans bot_le) ?_ _
  rintro k ih hφ m hm
  by_cases hk : IsMax k
  · rw [succ_eq_iff_isMax.2 hk] at hm
    exact ih (hφ.mono <| Iic_subset_Iic.2 (le_succ _)) _ hm
  obtain rfl | h := le_succ_iff_eq_or_le.1 hm
  · specialize ih (StrictMonoOn.mono hφ fun x hx => le_trans hx (le_succ _)) k le_rfl
    nth_grw 1 [ih]
    refine succ_le_of_lt (hφ (le_succ _) le_rfl ?_)
    exact lt_succ_of_not_isMax hk
  · exact ih (StrictMonoOn.mono hφ fun x hx => le_trans hx (le_succ _)) _ h

中文:
定理 StrictMonoOn.Iic_id_le
  结论: [Succ序 α] [是SuccArchimedean α] [有底序 α] {n : α} {φ : α -> α}
  证明: by
  revert hφ
  refine
    Succ.rec_bot (fun n => StrictMonoOn φ (Set.Iic n) -> forall m <= n, m <= φ m)
      (fun _ _ hm => hm.trans bot_le) ?_ _
  rintro k ih hφ m hm
  by_cases hk : IsMax k
  · rw [succ_eq_iff_isMax.2 hk] at hm
    exact ih (hφ.mono <| Iic_subset_Iic.2 (le_succ _)) _ hm
  obtain rfl | h := le_succ_iff_eq_or_le.1 hm
  · specialize ih (StrictMonoOn.mono hφ fun x hx => le_trans hx (le_succ _)) k le_rfl
    nth_grw 1 [ih]
    refine succ_le_of_lt (hφ (le_succ _) le_rfl ?_)
    exact lt_succ_of_not_isMax hk
  · exact ih (StrictMonoOn.mono hφ fun x hx => le_trans hx (le_succ _)) _ h

Depends on / 依赖: Iic_subset_Iic, Set.Iic, StrictMonoOn, StrictMonoOn.mono, Succ.rec_bot, bot_le, hm.trans, le_rfl, le_succ, le_succ_iff_eq_or_le, le_trans, lt_succ_of_not_isMax, nth_grw, rec_bot, revert, specialize, succ_eq_iff_isMax, succ_le_of_lt
-/
theorem StrictMonoOn.Iic_id_le [SuccOrder α] [IsSuccArchimedean α] [OrderBot α] {n : α} {φ : α -> α}
    (hφ : StrictMonoOn φ (Set.Iic n)) : forall m <= n, m <= φ m := by
  revert hφ
  refine
    Succ.rec_bot (fun n => StrictMonoOn φ (Set.Iic n) -> forall m <= n, m <= φ m)
      (fun _ _ hm => hm.trans bot_le) ?_ _
  rintro k ih hφ m hm
  by_cases hk : IsMax k
  · rw [succ_eq_iff_isMax.2 hk] at hm
    exact ih (hφ.mono <| Iic_subset_Iic.2 (le_succ _)) _ hm
  obtain rfl | h := le_succ_iff_eq_or_le.1 hm
  · specialize ih (StrictMonoOn.mono hφ fun x hx => le_trans hx (le_succ _)) k le_rfl
    nth_grw 1 [ih]
    refine succ_le_of_lt (hφ (le_succ _) le_rfl ?_)
    exact lt_succ_of_not_isMax hk
  · exact ih (StrictMonoOn.mono hφ fun x hx => le_trans hx (le_succ _)) _ h

/--
theorem `StrictMonoOn.Ici_le_id` / 定理 `StrictMonoOn.Ici_le_id`

English:
theorem StrictMonoOn.Ici_le_id
  statement: [PredOrder α] [IsPredArchimedean α] [OrderTop α] {n : α} {φ : α -> α}
  proof: StrictMonoOn.Iic_id_le (α := αᵒᵈ) fun _ hi _ hj hij => hφ hj hi hij

中文:
定理 StrictMonoOn.Ici_le_id
  结论: [Pred序 α] [是PredArchimedean α] [有顶序 α] {n : α} {φ : α -> α}
  证明: StrictMonoOn.Iic_id_le (α := αᵒᵈ) fun _ hi _ hj hij => hφ hj hi hij

Depends on / 依赖: Iic_id_le, StrictMonoOn, StrictMonoOn.Iic_id_le
-/
theorem StrictMonoOn.Ici_le_id [PredOrder α] [IsPredArchimedean α] [OrderTop α] {n : α} {φ : α -> α}
    (hφ : StrictMonoOn φ (Set.Ici n)) : forall m, n <= m -> φ m <= m :=
  StrictMonoOn.Iic_id_le (α := αᵒᵈ) fun _ hi _ hj hij => hφ hj hi hij

end LinearOrder
