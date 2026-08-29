/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Set.Prod

/-!
# Finite products of types

This file defines the product of types over a list. For `l : List ι` and `α : ι → Type v` we define
`List.TProd α l = l.foldr (fun i β ↦ α i × β) PUnit`.
This type should not be used if `∀ i, α i` or `∀ i ∈ l, α i` can be used instead
(in the last expression, we could also replace the list `l` by a set or a finset).
This type is used as an intermediary between binary products and finitary products.
The application of this type is finitary product measures, but it could be used in any
construction/theorem that is easier to define/prove on binary products than on finitary products.

* Once we have the construction on binary products (like binary product measures in
  `MeasureTheory.prod`), we can easily define a finitary version on the type `TProd l α`
  by iterating. Properties can also be easily extended from the binary case to the finitary case
  by iterating.
* Then we can use the equivalence `List.TProd.piEquivTProd` below (or enhanced versions of it,
  like a `MeasurableEquiv` for product measures) to get the construction on `∀ i : ι, α i`, at
  least when assuming `[Fintype ι] [Encodable ι]` (using `Encodable.sortedUniv`).
  Using `attribute [local instance] Fintype.toEncodable` we can get rid of the argument
  `[Encodable ι]`.

## Main definitions

* We have the equivalence `TProd.piEquivTProd : (∀ i, α i) ≃ TProd α l`
  if `l` contains every element of `ι` exactly once.
* The product of sets is `Set.tprod : (∀ i, Set (α i)) → Set (TProd α l)`.
-/

@[expose] public section


open List Function
universe u v
variable {ι : Type u} {α : ι -> Type v} {i j : ι} {l : List ι}

namespace List

variable (α) in
/--
Definition of `TProd` / `TProd` 的定义

English:
abbreviation TProd
  signature: (l : List ι)
  body: l.foldr (fun i β => α i × β) PUnit

中文:
缩写 TProd
  签名: (l : 列表 ι)
  定义体: l.foldr (fun i β => α i × β) PUnit

Depends on / 依赖: l.foldr
-/
abbrev TProd (l : List ι) : Type v :=
  l.foldr (fun i β => α i × β) PUnit

namespace TProd

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : forall (l : List ι) (_f : forall i, α i), TProd α l

中文:
定义 mk
  签名: : 对任意 (l : 列表 ι) (_f : 对任意 i, α i), TProd α l
-/
protected def mk : forall (l : List ι) (_f : forall i, α i), TProd α l
  | [] => fun _ => PUnit.unit
  | i :: is => fun f => (f i, TProd.mk is f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Inhabited (α i)] : Inhabited (TProd α l)
  body: ⟨TProd.mk l default⟩

@[simp]

中文:
实例 [对任意
  签名: i, 可居 (α i)] : 可居 (TProd α l)
  定义体: ⟨TProd.mk l default⟩

@[simp]

Depends on / 依赖: TProd.mk
-/
instance [forall i, Inhabited (α i)] : Inhabited (TProd α l) :=
  ⟨TProd.mk l default⟩

@[simp]
/--
theorem `fst_mk` / 定理 `fst_mk`

English:
theorem fst_mk
  given: (i : ι) (l : List ι) (f : forall i, α i)
  statement: (TProd.mk (i :: l) f).1 = f i
  proof: rfl

@[simp]

中文:
定理 fst_mk
  条件: (i : ι) (l : 列表 ι) (f : 对任意 i, α i)
  结论: (TProd.mk (i :: l) f).1 = f i
  证明: rfl

@[simp]
-/
theorem fst_mk (i : ι) (l : List ι) (f : forall i, α i) : (TProd.mk (i :: l) f).1 = f i :=
  rfl

@[simp]
/--
theorem `snd_mk` / 定理 `snd_mk`

English:
theorem snd_mk
  given: (i : ι) (l : List ι) (f : forall i, α i)
  proof: rfl

中文:
定理 snd_mk
  条件: (i : ι) (l : 列表 ι) (f : 对任意 i, α i)
  证明: rfl
-/
theorem snd_mk (i : ι) (l : List ι) (f : forall i, α i) :
    (TProd.mk.{u, v} (i :: l) f).2 = TProd.mk.{u, v} l f :=
  rfl

variable [DecidableEq ι]

/--
Definition of `elim` / `elim` 的定义

English:
definition elim
  signature: : forall {l : List ι} (_ : TProd α l) {i : ι} (_ : i in l), α i

中文:
定义 elim
  签名: : 对任意 {l : 列表 ι} (_ : TProd α l) {i : ι} (_ : i in l), α i
-/
protected def elim : forall {l : List ι} (_ : TProd α l) {i : ι} (_ : i in l), α i
  | i :: is, v, j, hj =>
    if hji : j = i then by
      subst hji
      exact v.1
    else TProd.elim v.2 ((List.mem_cons.mp hj).resolve_left hji)

@[simp]
/--
theorem `elim_self` / 定理 `elim_self`

English:
theorem elim_self
  given: (v : TProd α (i :: l))
  statement: v.elim mem_cons_self = v.1
  proof: by simp [TProd.elim]

@[simp]

中文:
定理 elim_self
  条件: (v : TProd α (i :: l))
  结论: v.elim mem_cons_self = v.1
  证明: by simp [TProd.elim]

@[simp]

Depends on / 依赖: TProd.elim
-/
theorem elim_self (v : TProd α (i :: l)) : v.elim mem_cons_self = v.1 := by simp [TProd.elim]

@[simp]
/--
theorem `elim_of_ne` / 定理 `elim_of_ne`

English:
theorem elim_of_ne
  given: (hj : j in i :: l) (hji : j != i) (v : TProd α (i :: l))
  proof: by simp [TProd.elim, hji]

@[simp]

中文:
定理 elim_of_ne
  条件: (hj : j in i :: l) (hji : j != i) (v : TProd α (i :: l))
  证明: by simp [TProd.elim, hji]

@[simp]

Depends on / 依赖: TProd.elim
-/
theorem elim_of_ne (hj : j in i :: l) (hji : j != i) (v : TProd α (i :: l)) :
    v.elim hj = TProd.elim v.2 ((List.mem_cons.mp hj).resolve_left hji) := by simp [TProd.elim, hji]

@[simp]
/--
theorem `elim_of_mem` / 定理 `elim_of_mem`

English:
theorem elim_of_mem
  given: (hl : (i :: l).Nodup) (hj : j in l) (v : TProd α (i :: l))
  proof: by
  apply elim_of_ne
  rintro rfl
  exact hl.notMem hj

中文:
定理 elim_of_mem
  条件: (hl : (i :: l).Nodup) (hj : j in l) (v : TProd α (i :: l))
  证明: by
  apply elim_of_ne
  rintro rfl
  exact hl.notMem hj

Depends on / 依赖: elim_of_ne, hl.notMem, notMem
-/
theorem elim_of_mem (hl : (i :: l).Nodup) (hj : j in l) (v : TProd α (i :: l)) :
    v.elim (mem_cons_of_mem _ hj) = TProd.elim v.2 hj := by
  apply elim_of_ne
  rintro rfl
  exact hl.notMem hj

/--
theorem `elim_mk` / 定理 `elim_mk`

English:
theorem elim_mk
  statement: forall (l : List ι) (f : forall i, α i) {i : ι} (hi : i in l), (TProd.mk l f).elim hi = f i

中文:
定理 elim_mk
  结论: 对任意 (l : 列表 ι) (f : 对任意 i, α i) {i : ι} (hi : i in l), (TProd.mk l f).elim hi = f i
-/
theorem elim_mk : forall (l : List ι) (f : forall i, α i) {i : ι} (hi : i in l), (TProd.mk l f).elim hi = f i
  | i :: is, f, j, hj => by
    by_cases hji : j = i
    · subst hji
      simp
    · rw [TProd.elim_of_ne _ hji, snd_mk, elim_mk is]

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext

中文:
定理 ext
-/
theorem ext :
    forall {l : List ι} (_ : l.Nodup) {v w : TProd α l}
      (_ : forall (i) (hi : i in l), v.elim hi = w.elim hi), v = w
  | [], _, v, w, _ => PUnit.ext v w
  | i :: is, hl, v, w, hvw => by
    apply Prod.ext
    · rw [← elim_self v, hvw, elim_self]
    refine ext (nodup_cons.mp hl).2 fun j hj => ?_
    rw [← elim_of_mem hl]; rw [hvw]; rw [elim_of_mem hl]

/-- A version of `TProd.elim` when `l` contains all elements. In this case we get a function into
  `Π i, α i`. -/
@[simp]
/--
Definition of `elim'` / `elim'` 的定义

English:
definition elim'
  signature: (h : forall i, i in l) (v : TProd α l) (i : ι)
  body: v.elim (h i)

中文:
定义 elim'
  签名: (h : 对任意 i, i in l) (v : TProd α l) (i : ι)
  定义体: v.elim (h i)
-/
protected def elim' (h : forall i, i in l) (v : TProd α l) (i : ι) : α i :=
  v.elim (h i)

/--
theorem `mk_elim` / 定理 `mk_elim`

English:
theorem mk_elim
  given: (hnd : l.Nodup) (h : forall i, i in l) (v : TProd α l)
  statement: TProd.mk l (v.elim' h) = v
  proof: TProd.ext hnd fun i hi => by simp [elim_mk]

中文:
定理 mk_elim
  条件: (hnd : l.Nodup) (h : 对任意 i, i in l) (v : TProd α l)
  结论: TProd.mk l (v.elim' h) = v
  证明: TProd.ext hnd fun i hi => by simp [elim_mk]

Depends on / 依赖: TProd.ext, elim_mk
-/
theorem mk_elim (hnd : l.Nodup) (h : forall i, i in l) (v : TProd α l) : TProd.mk l (v.elim' h) = v :=
  TProd.ext hnd fun i hi => by simp [elim_mk]

/--
Definition of `piEquivTProd` / `piEquivTProd` 的定义

English:
definition piEquivTProd
  signature: (hnd : l.Nodup) (h : forall i, i in l)
  body: ⟨TProd.mk l, TProd.elim' h, fun f => funext fun i => elim_mk l f (h i), mk_elim hnd h⟩

中文:
定义 piEquivTProd
  签名: (hnd : l.Nodup) (h : 对任意 i, i in l)
  定义体: ⟨TProd.mk l, TProd.elim' h, fun f => funext fun i => elim_mk l f (h i), mk_elim hnd h⟩

Depends on / 依赖: TProd.elim, TProd.mk, elim_mk, mk_elim
-/
def piEquivTProd (hnd : l.Nodup) (h : forall i, i in l) : (forall i, α i) ≃ TProd α l :=
  ⟨TProd.mk l, TProd.elim' h, fun f => funext fun i => elim_mk l f (h i), mk_elim hnd h⟩

end TProd

end List

namespace Set

/-- A product of sets in `TProd α l`. -/
@[simp]
/--
Definition of `tprod` / `tprod` 的定义

English:
definition tprod
  signature: : forall (l : List ι) (_t : forall i, Set (α i)), Set (TProd α l)

中文:
定义 tprod
  签名: : 对任意 (l : 列表 ι) (_t : 对任意 i, 集合 (α i)), 集合 (TProd α l)
-/
protected def tprod : forall (l : List ι) (_t : forall i, Set (α i)), Set (TProd α l)
  | [], _ => univ
  | i :: is, t => t i ×ˢ Set.tprod is t

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mk_preimage_tprod` / 定理 `mk_preimage_tprod`

English:
theorem mk_preimage_tprod
  proof: by
      change f in TProd.mk l ⁻¹' Set.tprod l t ↔ f in { x | x in l }.pi t
      rw [mk_preimage_tprod l t]
    -- `simp [Set.TProd, TProd.mk, this]` can close this goal but is slow.
    rw [Set.tprod]; rw [TProd.mk]; rw [mem_preimage]; rw [mem_pi]; rw [prodMk_mem_set_prod_eq]
    simp_rw [mem_ofP

中文:
定理 mk_preimage_tprod
  证明: by
      change f in TProd.mk l ⁻¹' Set.tprod l t ↔ f in { x | x in l }.pi t
      rw [mk_preimage_tprod l t]
    -- `simp [Set.TProd, TProd.mk, this]` can close this goal but is slow.
    rw [Set.tprod]; rw [TProd.mk]; rw [mem_preimage]; rw [mem_pi]; rw [prodMk_mem_set_prod_eq]
    simp_rw [mem_ofP

Depends on / 依赖: Set.tprod, TProd.mk, mk_preimage_tprod
-/
theorem mk_preimage_tprod :
    forall (l : List ι) (t : forall i, Set (α i)), TProd.mk l ⁻¹' Set.tprod l t = { i | i in l }.pi t
  | [], t => by simp [Set.tprod]
  | i :: l, t => by
    ext f
    have h : TProd.mk l f in Set.tprod l t ↔ forall i : ι, i in l -> f i in t i := by
      change f in TProd.mk l ⁻¹' Set.tprod l t ↔ f in { x | x in l }.pi t
      rw [mk_preimage_tprod l t]
    -- `simp [Set.TProd, TProd.mk, this]` can close this goal but is slow.
    rw [Set.tprod]; rw [TProd.mk]; rw [mem_preimage]; rw [mem_pi]; rw [prodMk_mem_set_prod_eq]
    simp_rw [mem_ofPred_eq, mem_cons]
    rw [forall_eq_or_imp]; rw [and_congr_right_iff]
    exact fun _ => h

/--
theorem `elim_preimage_pi` / 定理 `elim_preimage_pi`

English:
theorem elim_preimage_pi
  statement: [DecidableEq ι] {l : List ι} (hnd : l.Nodup) (h : forall i, i in l)
  proof: by
  have h2 : { i | i in l } = univ := by
    ext i
    simp [h]
  rw [← h2]; rw [← mk_preimage_tprod]; rw [preimage_preimage]
  simp only [TProd.mk_elim hnd h]
  dsimp

中文:
定理 elim_preimage_pi
  结论: [DecidableEq ι] {l : 列表 ι} (hnd : l.Nodup) (h : 对任意 i, i in l)
  证明: by
  have h2 : { i | i in l } = univ := by
    ext i
    simp [h]
  rw [← h2]; rw [← mk_preimage_tprod]; rw [preimage_preimage]
  simp only [TProd.mk_elim hnd h]
  dsimp

Depends on / 依赖: TProd.mk_elim, mk_elim, mk_preimage_tprod, preimage_preimage
-/
theorem elim_preimage_pi [DecidableEq ι] {l : List ι} (hnd : l.Nodup) (h : forall i, i in l)
    (t : forall i, Set (α i)) : TProd.elim' h ⁻¹' pi univ t = Set.tprod l t := by
  have h2 : { i | i in l } = univ := by
    ext i
    simp [h]
  rw [← h2]; rw [← mk_preimage_tprod]; rw [preimage_preimage]
  simp only [TProd.mk_elim hnd h]
  dsimp

end Set
