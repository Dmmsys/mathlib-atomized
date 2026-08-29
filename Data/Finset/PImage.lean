/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Finset.Option
public import Mathlib.Data.PFun
public import Mathlib.Data.Part

/-!
# Image of a `Finset α` under a partially defined function

In this file we define `Part.toFinset` and `Finset.pimage`. We also prove some trivial lemmas about
these definitions.

## Tags

finite set, image, partial function
-/

@[expose] public section


variable {α β : Type*}

namespace Part

/--
Definition of `toFinset` / `toFinset` 的定义

English:
definition toFinset
  signature: (o : Part α) [Decidable o.Dom]
  body: o.toOption.toFinset

@[simp]

中文:
定义 toFinset
  签名: (o : Part α) [可判定 o.Dom]
  定义体: o.toOption.toFinset

@[simp]

Depends on / 依赖: o.toOption.toFinset, toFinset, toOption
-/
def toFinset (o : Part α) [Decidable o.Dom] : Finset α :=
  o.toOption.toFinset

@[simp]
/--
theorem `mem_toFinset` / 定理 `mem_toFinset`

English:
theorem mem_toFinset
  given: {o : Part α} [Decidable o.Dom] {x : α}
  statement: x in o.toFinset ↔ x in o
  proof: by
  simp [toFinset]

@[simp]

中文:
定理 mem_toFinset
  条件: {o : Part α} [可判定 o.Dom] {x : α}
  结论: x in o.toFinset ↔ x in o
  证明: by
  simp [toFinset]

@[simp]

Depends on / 依赖: toFinset
-/
theorem mem_toFinset {o : Part α} [Decidable o.Dom] {x : α} : x in o.toFinset ↔ x in o := by
  simp [toFinset]

@[simp]
/--
theorem `toFinset_none` / 定理 `toFinset_none`

English:
theorem toFinset_none
  given: [Decidable (none : Part α).Dom]
  statement: none.toFinset = (∅ : Finset α)
  proof: by
  simp [toFinset]

@[simp]

中文:
定理 toFinset_none
  条件: [可判定 (none : Part α).Dom]
  结论: none.toFinset = (∅ : 有限集 α)
  证明: by
  simp [toFinset]

@[simp]

Depends on / 依赖: toFinset
-/
theorem toFinset_none [Decidable (none : Part α).Dom] : none.toFinset = (∅ : Finset α) := by
  simp [toFinset]

@[simp]
/--
theorem `toFinset_some` / 定理 `toFinset_some`

English:
theorem toFinset_some
  given: {a : α} [Decidable (some a).Dom]
  statement: (some a).toFinset = {a}
  proof: by
  simp [toFinset]

@[simp]

中文:
定理 toFinset_some
  条件: {a : α} [可判定 (some a).Dom]
  结论: (some a).toFinset = {a}
  证明: by
  simp [toFinset]

@[simp]

Depends on / 依赖: toFinset
-/
theorem toFinset_some {a : α} [Decidable (some a).Dom] : (some a).toFinset = {a} := by
  simp [toFinset]

@[simp]
/--
theorem `coe_toFinset` / 定理 `coe_toFinset`

English:
theorem coe_toFinset
  given: (o : Part α) [Decidable o.Dom]
  statement: (o.toFinset : Set α) = { x | x in o }
  proof: Set.ext fun _ => mem_toFinset

中文:
定理 coe_toFinset
  条件: (o : Part α) [可判定 o.Dom]
  结论: (o.toFinset : 集合 α) = { x | x in o }
  证明: Set.ext fun _ => mem_toFinset

Depends on / 依赖: Set.ext, mem_toFinset
-/
theorem coe_toFinset (o : Part α) [Decidable o.Dom] : (o.toFinset : Set α) = { x | x in o } :=
  Set.ext fun _ => mem_toFinset

end Part

namespace Finset

variable [DecidableEq β] {f g : α ->. β} [forall x, Decidable (f x).Dom] [forall x, Decidable (g x).Dom]
  {s t : Finset α} {b : β}

/--
Definition of `pimage` / `pimage` 的定义

English:
definition pimage
  signature: (f : α ->. β) [forall x, Decidable (f x).Dom] (s : Finset α)
  body: s.biUnion fun x => (f x).toFinset

@[simp]

中文:
定义 pimage
  签名: (f : α ->. β) [对任意 x, 可判定 (f x).Dom] (s : 有限集 α)
  定义体: s.biUnion fun x => (f x).toFinset

@[simp]

Depends on / 依赖: biUnion, s.biUnion, toFinset
-/
def pimage (f : α ->. β) [forall x, Decidable (f x).Dom] (s : Finset α) : Finset β :=
  s.biUnion fun x => (f x).toFinset

@[simp]
/--
theorem `mem_pimage` / 定理 `mem_pimage`

English:
theorem mem_pimage
  statement: b in s.pimage f ↔ exists a in s, b in f a
  proof: by
  simp [pimage]

@[simp, norm_cast]

中文:
定理 mem_pimage
  结论: b in s.pimage f ↔ 存在 a in s, b in f a
  证明: by
  simp [pimage]

@[simp, norm_cast]

Depends on / 依赖: pimage
-/
theorem mem_pimage : b in s.pimage f ↔ exists a in s, b in f a := by
  simp [pimage]

@[simp, norm_cast]
/--
theorem `coe_pimage` / 定理 `coe_pimage`

English:
theorem coe_pimage
  statement: (s.pimage f : Set β) = f.image s
  proof: Set.ext fun _ => mem_pimage

中文:
定理 coe_pimage
  结论: (s.pimage f : 集合 β) = f.像 s
  证明: Set.ext fun _ => mem_pimage

Depends on / 依赖: Set.ext, mem_pimage
-/
theorem coe_pimage : (s.pimage f : Set β) = f.image s :=
  Set.ext fun _ => mem_pimage

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `pimage_some` / 定理 `pimage_some`

English:
theorem pimage_some
  given: (s : Finset α) (f : α -> β) [forall x, Decidable (Part.some <| f x).Dom]
  proof: by
  ext
  simp [eq_comm]

中文:
定理 pimage_some
  条件: (s : 有限集 α) (f : α -> β) [对任意 x, 可判定 (Part.some <| f x).Dom]
  证明: by
  ext
  simp [eq_comm]

Depends on / 依赖: eq_comm
-/
theorem pimage_some (s : Finset α) (f : α -> β) [forall x, Decidable (Part.some <| f x).Dom] :
    (s.pimage fun x => Part.some (f x)) = s.image f := by
  ext
  simp [eq_comm]

/--
theorem `pimage_congr` / 定理 `pimage_congr`

English:
theorem pimage_congr
  given: (h₁ : s = t) (h₂ : forall x in t, f x = g x)
  statement: s.pimage f = t.pimage g
  proof: by
  aesop

中文:
定理 pimage_congr
  条件: (h₁ : s = t) (h₂ : 对任意 x in t, f x = g x)
  结论: s.pimage f = t.pimage g
  证明: by
  aesop
-/
theorem pimage_congr (h₁ : s = t) (h₂ : forall x in t, f x = g x) : s.pimage f = t.pimage g := by
  aesop

/--
theorem `pimage_eq_image_filter` / 定理 `pimage_eq_image_filter`

English:
theorem pimage_eq_image_filter
  statement: s.pimage f =
  proof: by
  aesop (add simp Part.mem_eq)

中文:
定理 pimage_eq_image_filter
  结论: s.pimage f =
  证明: by
  aesop (add simp Part.mem_eq)

Depends on / 依赖: Part.mem_eq, mem_eq
-/
theorem pimage_eq_image_filter : s.pimage f =
    {x in s | (f x).Dom}.attach.image
      fun x : { x // x in filter (fun x => (f x).Dom) s } =>
        (f x).get (mem_filter.mp x.coe_prop).2 := by
  aesop (add simp Part.mem_eq)

/--
theorem `pimage_union` / 定理 `pimage_union`

English:
theorem pimage_union
  given: [DecidableEq α]
  statement: (s union t).pimage f = s.pimage f union t.pimage f
  proof: coe_inj.1 by
  simp only [coe_pimage, coe_union, ← PFun.image_union]

@[simp]

中文:
定理 pimage_union
  条件: [DecidableEq α]
  结论: (s union t).pimage f = s.pimage f union t.pimage f
  证明: coe_inj.1 by
  simp only [coe_pimage, coe_union, ← PFun.image_union]

@[simp]

Depends on / 依赖: PFun.image_union, coe_inj, coe_pimage, coe_union, image_union
-/
theorem pimage_union [DecidableEq α] : (s union t).pimage f = s.pimage f union t.pimage f :=
coe_inj.1 by
  simp only [coe_pimage, coe_union, ← PFun.image_union]

@[simp]
/--
theorem `pimage_empty` / 定理 `pimage_empty`

English:
theorem pimage_empty
  statement: pimage f ∅ = ∅
  proof: by
  ext
  simp

中文:
定理 pimage_empty
  结论: pimage f ∅ = ∅
  证明: by
  ext
  simp
-/
theorem pimage_empty : pimage f ∅ = ∅ := by
  ext
  simp

/--
theorem `pimage_subset` / 定理 `pimage_subset`

English:
theorem pimage_subset
  given: {t : Finset β}
  statement: s.pimage f subseteq t ↔ forall x in s, forall y in f x, y in t
  proof: by
  simp [subset_iff, @forall_comm _ β]

@[gcongr, mono]

中文:
定理 pimage_subset
  条件: {t : 有限集 β}
  结论: s.pimage f subseteq t ↔ 对任意 x in s, 对任意 y in f x, y in t
  证明: by
  simp [subset_iff, @forall_comm _ β]

@[gcongr, mono]

Depends on / 依赖: forall_comm, subset_iff
-/
theorem pimage_subset {t : Finset β} : s.pimage f subseteq t ↔ forall x in s, forall y in f x, y in t := by
  simp [subset_iff, @forall_comm _ β]

@[gcongr, mono]
/--
theorem `pimage_mono` / 定理 `pimage_mono`

English:
theorem pimage_mono
  given: (h : s subseteq t)
  statement: s.pimage f subseteq t.pimage f
  proof: pimage_subset.2 fun x hx _ hy => mem_pimage.2 ⟨x, h hx, hy⟩

中文:
定理 pimage_mono
  条件: (h : s subseteq t)
  结论: s.pimage f subseteq t.pimage f
  证明: pimage_subset.2 fun x hx _ hy => mem_pimage.2 ⟨x, h hx, hy⟩

Depends on / 依赖: mem_pimage, pimage_subset
-/
theorem pimage_mono (h : s subseteq t) : s.pimage f subseteq t.pimage f :=
  pimage_subset.2 fun x hx _ hy => mem_pimage.2 ⟨x, h hx, hy⟩

/--
theorem `pimage_inter` / 定理 `pimage_inter`

English:
theorem pimage_inter
  given: [DecidableEq α]
  statement: (s inter t).pimage f subseteq s.pimage f inter t.pimage f
  proof: by
  simp only [← coe_subset, coe_pimage, coe_inter, PFun.image_inter]

中文:
定理 pimage_inter
  条件: [DecidableEq α]
  结论: (s inter t).pimage f subseteq s.pimage f inter t.pimage f
  证明: by
  simp only [← coe_subset, coe_pimage, coe_inter, PFun.image_inter]

Depends on / 依赖: PFun.image_inter, coe_inter, coe_pimage, coe_subset, image_inter
-/
theorem pimage_inter [DecidableEq α] : (s inter t).pimage f subseteq s.pimage f inter t.pimage f := by
  simp only [← coe_subset, coe_pimage, coe_inter, PFun.image_inter]

end Finset
