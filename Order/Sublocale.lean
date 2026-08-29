/-
Copyright (c) 2025 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chriara Cimino, Christian Krause
-/
module

public import Mathlib.Order.Nucleus
public import Mathlib.Order.SupClosed

/-!
# Sublocale

Locales are the dual concept to frames. Locale theory is a branch of point-free topology, where
intuitively locales are like topological spaces which may or may not have enough points.
Sublocales of a locale generalize the concept of subspaces in topology to the point-free setting.

## TODO

Create separate definitions for `sInf_mem` and `HImpClosed` (also useful for `CompleteSublattice`)

## References

* [J. Picada A. Pultr, *Frames and Locales*][picado2012]
* https://ncatlab.org/nlab/show/sublocale
* https://ncatlab.org/nlab/show/nucleus
-/

@[expose] public section

variable {X : Type*} [Order.Frame X]
open Set

/--
Definition of `Sublocale` / `Sublocale` 的定义

English:
structure Sublocale
  parameters: (X : Type*) [Order.Frame X]
  axioms and operations (3):
    - carrier : Set X
    - sInf_mem' : forall s subseteq carrier, sInf s in carrier
    - himp_mem' : forall a b, b in carrier -> a ⇨ b in carrier

中文:
结构 Sublocale
  参数: (X : 类型) [Order.Frame X]
  公理与运算 (3 个):
    - carrier : Set X
    - sInf_mem' : 对任意 s subseteq carrier, sInf s in carrier
    - himp_mem' : 对任意 a b, b in carrier -> a ⇨ b in carrier
-/
structure Sublocale (X : Type*) [Order.Frame X] where
  /-- The set corresponding to the sublocale. -/
  carrier : Set X
  /-- A sublocale is closed under all meets.

  Do NOT use directly. Use `Sublocale.sInf_mem` instead. -/
  sInf_mem' : forall s subseteq carrier, sInf s in carrier
  /-- A sublocale is closed under heyting implication.

  Do NOT use directly. Use `Sublocale.himp_mem` instead. -/
  himp_mem' : forall a b, b in carrier -> a ⇨ b in carrier

namespace Sublocale

variable {ι : Sort*} {S T : Sublocale X} {s : Set X} {f : ι -> X} {a b : X}

/--
Instance `instSetLike` / 实例 `instSetLike`

English:
instance instSetLike
  signature: : SetLike (Sublocale X) X where
  body: x.carrier
  coe_injective s1 s2 h := by cases s1; congr

中文:
实例 instSetLike
  签名: : SetLike (Sublocale X) X where
  定义体: x.carrier
  coe_injective s1 s2 h := by cases s1; congr

Depends on / 依赖: carrier, x.carrier
-/
instance instSetLike : SetLike (Sublocale X) X where
  coe x := x.carrier
  coe_injective s1 s2 h := by cases s1; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Sublocale X)
  body: .ofSetLike (Sublocale X) X

中文:
实例 :
  签名: PartialOrder (Sublocale X)
  定义体: .ofSetLike (Sublocale X) X

Depends on / 依赖: Sublocale, ofSetLike
-/
instance : PartialOrder (Sublocale X) := .ofSetLike (Sublocale X) X

/--
lemma `mem_carrier` / 引理 `mem_carrier`

English:
lemma mem_carrier
  statement: a in S.carrier ↔ a in S
  proof: .rfl

中文:
引理 mem_carrier
  结论: a in S.carrier ↔ a in S
  证明: .rfl
-/
@[simp] lemma mem_carrier : a in S.carrier ↔ a in S := .rfl

/--
lemma `mem_mk` / 引理 `mem_mk`

English:
lemma mem_mk
  given: (carrier : Set X) (sInf_mem' himp_mem')
  proof: .rfl

@[simp, gcongr]

中文:
引理 mem_mk
  条件: (carrier : Set X) (sInf_mem' himp_mem')
  证明: .rfl

@[simp, gcongr]
-/
@[simp] lemma mem_mk (carrier : Set X) (sInf_mem' himp_mem') :
    a in mk carrier sInf_mem' himp_mem' ↔ a in carrier := .rfl

@[simp, gcongr]
/--
lemma `mk_le_mk` / 引理 `mk_le_mk`

English:
lemma mk_le_mk
  given: (carrier₁ carrier₂ : Set X) (sInf_mem'₁ sInf_mem'₂ himp_mem'₁ himp_mem'₂)
  proof: .rfl

initialize_simps_projections Sublocale (carrier -> coe, as_prefix coe)

中文:
引理 mk_le_mk
  条件: (carrier₁ carrier₂ : Set X) (sInf_mem'₁ sInf_mem'₂ himp_mem'₁ himp_mem'₂)
  证明: .rfl

initialize_simps_projections Sublocale (carrier -> coe, as_prefix coe)
-/
lemma mk_le_mk (carrier₁ carrier₂ : Set X) (sInf_mem'₁ sInf_mem'₂ himp_mem'₁ himp_mem'₂) :
    mk carrier₁ sInf_mem'₁ himp_mem'₁ <= mk carrier₂ sInf_mem'₂ himp_mem'₂ ↔ carrier₁ subseteq carrier₂ :=
  .rfl

initialize_simps_projections Sublocale (carrier -> coe, as_prefix coe)

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: (h : forall x, x in S ↔ x in T)
  statement: S = T
  proof: SetLike.ext h

中文:
引理 ext
  条件: (h : 对任意 x, x in S ↔ x in T)
  结论: S = T
  证明: SetLike.ext h
-/
@[ext] lemma ext (h : forall x, x in S ↔ x in T) : S = T := SetLike.ext h

/--
lemma `sInf_mem` / 引理 `sInf_mem`

English:
lemma sInf_mem
  given: (hs : s subseteq S)
  statement: sInf s in S
  proof: S.sInf_mem' _ hs

中文:
引理 sInf_mem
  条件: (hs : s subseteq S)
  结论: sInf s in S
  证明: S.sInf_mem' _ hs

Depends on / 依赖: S.sInf_mem, sInf_mem
-/
lemma sInf_mem (hs : s subseteq S) : sInf s in S := S.sInf_mem' _ hs
/--
lemma `iInf_mem` / 引理 `iInf_mem`

English:
lemma iInf_mem
  given: (hf : forall i, f i in S)
  statement: ⨅ i, f i in S
  proof: S.sInf_mem by simpa [range_subset_iff]

中文:
引理 iInf_mem
  条件: (hf : 对任意 i, f i in S)
  结论: ⨅ i, f i in S
  证明: S.sInf_mem by simpa [range_subset_iff]

Depends on / 依赖: S.sInf_mem, range_subset_iff, sInf_mem
-/
lemma iInf_mem (hf : forall i, f i in S) : ⨅ i, f i in S := S.sInf_mem by simpa [range_subset_iff]

/--
lemma `infClosed` / 引理 `infClosed`

English:
lemma infClosed
  statement: InfClosed (S : Set X)
  proof: by
  rintro a ha b hb; rw [← sInf_pair]; exact S.sInf_mem (pair_subset ha hb)

中文:
引理 infClosed
  结论: InfClosed (S : Set X)
  证明: by
  rintro a ha b hb; rw [← sInf_pair]; exact S.sInf_mem (pair_subset ha hb)

Depends on / 依赖: S.sInf_mem, pair_subset, sInf_mem, sInf_pair
-/
lemma infClosed : InfClosed (S : Set X) := by
  rintro a ha b hb; rw [← sInf_pair]; exact S.sInf_mem (pair_subset ha hb)

/--
lemma `inf_mem` / 引理 `inf_mem`

English:
lemma inf_mem
  given: (ha : a in S) (hb : b in S)
  statement: a ⊓ b in S
  proof: S.infClosed ha hb

中文:
引理 inf_mem
  条件: (ha : a in S) (hb : b in S)
  结论: a ⊓ b in S
  证明: S.infClosed ha hb

Depends on / 依赖: S.infClosed, infClosed
-/
lemma inf_mem (ha : a in S) (hb : b in S) : a ⊓ b in S := S.infClosed ha hb

/--
lemma `top_mem` / 引理 `top_mem`

English:
lemma top_mem
  statement: ⊤ in S
  proof: by simpa using S.sInf_mem empty_subset _

中文:
引理 top_mem
  结论: ⊤ in S
  证明: by simpa using S.sInf_mem empty_subset _

Depends on / 依赖: S.sInf_mem, empty_subset, sInf_mem
-/
lemma top_mem : ⊤ in S := by simpa using S.sInf_mem empty_subset _

/--
lemma `himp_mem` / 引理 `himp_mem`

English:
lemma himp_mem
  given: (hb : b in S)
  statement: a ⇨ b in S
  proof: S.himp_mem' _ _ hb

中文:
引理 himp_mem
  条件: (hb : b in S)
  结论: a ⇨ b in S
  证明: S.himp_mem' _ _ hb

Depends on / 依赖: S.himp_mem, himp_mem
-/
lemma himp_mem (hb : b in S) : a ⇨ b in S := S.himp_mem' _ _ hb

/--
Instance `carrier.instSemilatticeInf` / 实例 `carrier.instSemilatticeInf`

English:
instance carrier.instSemilatticeInf
  signature: : SemilatticeInf S
  body: Subtype.semilatticeInf fun _ _ => inf_mem

中文:
实例 carrier.instSemilatticeInf
  签名: : SemilatticeInf S
  定义体: Subtype.semilatticeInf fun _ _ => inf_mem

Depends on / 依赖: Subtype, Subtype.semilatticeInf, inf_mem, semilatticeInf
-/
instance carrier.instSemilatticeInf : SemilatticeInf S := Subtype.semilatticeInf fun _ _ => inf_mem

/--
Instance `carrier.instOrderTop` / 实例 `carrier.instOrderTop`

English:
instance carrier.instOrderTop
  signature: : OrderTop S
  body: Subtype.orderTop top_mem

中文:
实例 carrier.instOrderTop
  签名: : OrderTop S
  定义体: Subtype.orderTop top_mem

Depends on / 依赖: Subtype, Subtype.orderTop, orderTop, top_mem
-/
instance carrier.instOrderTop : OrderTop S := Subtype.orderTop top_mem

/--
Instance `carrier.instHImp` / 实例 `carrier.instHImp`

English:
instance carrier.instHImp
  signature: : HImp S where himp a b
  body: ⟨a ⇨ b, S.himp_mem b.2⟩

中文:
实例 carrier.instHImp
  签名: : HImp S where himp a b
  定义体: ⟨a ⇨ b, S.himp_mem b.2⟩

Depends on / 依赖: S.himp_mem, himp_mem
-/
instance carrier.instHImp : HImp S where himp a b := ⟨a ⇨ b, S.himp_mem b.2⟩

/--
Instance `carrier.instInfSet` / 实例 `carrier.instInfSet`

English:
instance carrier.instInfSet
  signature: : InfSet S where
  body: ⟨sInf (Subtype.val '' x), S.sInf_mem' _
    (by simp_rw [image_subset_iff, subset_def]; simp)⟩

中文:
实例 carrier.instInfSet
  签名: : InfSet S where
  定义体: ⟨sInf (Subtype.val '' x), S.sInf_mem' _
    (by simp_rw [image_subset_iff, subset_def]; simp)⟩

Depends on / 依赖: S.sInf_mem, Subtype, Subtype.val, sInf_mem
-/
instance carrier.instInfSet : InfSet S where
  sInf x := ⟨sInf (Subtype.val '' x), S.sInf_mem' _
    (by simp_rw [image_subset_iff, subset_def]; simp)⟩

/--
lemma `coe_inf` / 引理 `coe_inf`

English:
lemma coe_inf
  given: (a b : S)
  statement: (a ⊓ b).val = ↑a ⊓ ↑b
  proof: rfl

中文:
引理 coe_inf
  条件: (a b : S)
  结论: (a ⊓ b).val = ↑a ⊓ ↑b
  证明: rfl
-/
@[simp, norm_cast] lemma coe_inf (a b : S) : (a ⊓ b).val = ↑a ⊓ ↑b := rfl
/--
lemma `coe_sInf` / 引理 `coe_sInf`

English:
lemma coe_sInf
  given: (s : Set S)
  statement: (sInf s).val = sInf (Subtype.val '' s)
  proof: rfl

中文:
引理 coe_sInf
  条件: (s : Set S)
  结论: (sInf s).val = sInf (Subtype.val '' s)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_sInf (s : Set S) : (sInf s).val = sInf (Subtype.val '' s) := rfl
/--
lemma `coe_iInf` / 引理 `coe_iInf`

English:
lemma coe_iInf
  given: (f : ι -> S)
  statement: (⨅ i, f i).val = ⨅ i, (f i).val
  proof: by
  simp [iInf, ← range_comp, Function.comp_def]

中文:
引理 coe_iInf
  条件: (f : ι -> S)
  结论: (⨅ i, f i).val = ⨅ i, (f i).val
  证明: by
  simp [iInf, ← range_comp, Function.comp_def]
-/
@[simp, norm_cast] lemma coe_iInf (f : ι -> S) : (⨅ i, f i).val = ⨅ i, (f i).val := by
  simp [iInf, ← range_comp, Function.comp_def]

/--
Instance `carrier.instCompleteLattice` / 实例 `carrier.instCompleteLattice`

English:
instance carrier.instCompleteLattice
  signature: : CompleteLattice S where
  body: instSemilatticeInf
  __ := instOrderTop
__ := completeLatticeOfInf S by simp [isGLB_iff_le_iff, lowerBounds, ← Subtype.coe_le_coe]

中文:
实例 carrier.instCompleteLattice
  签名: : CompleteLattice S where
  定义体: instSemilatticeInf
  __ := instOrderTop
__ := completeLatticeOfInf S by simp [isGLB_iff_le_iff, lowerBounds, ← Subtype.coe_le_coe]

Depends on / 依赖: instSemilatticeInf
-/
instance carrier.instCompleteLattice : CompleteLattice S where
  __ := instSemilatticeInf
  __ := instOrderTop
__ := completeLatticeOfInf S by simp [isGLB_iff_le_iff, lowerBounds, ← Subtype.coe_le_coe]

/--
lemma `coe_himp` / 引理 `coe_himp`

English:
lemma coe_himp
  given: (a b : S)
  statement: (a ⇨ b).val = a.val ⇨ b.val
  proof: rfl

中文:
引理 coe_himp
  条件: (a b : S)
  结论: (a ⇨ b).val = a.val ⇨ b.val
  证明: rfl
-/
@[simp, norm_cast] lemma coe_himp (a b : S) : (a ⇨ b).val = a.val ⇨ b.val := rfl

/--
Instance `carrier.instHeytingAlgebra` / 实例 `carrier.instHeytingAlgebra`

English:
instance carrier.instHeytingAlgebra
  signature: : HeytingAlgebra S where
  body: by simp [← Subtype.coe_le_coe, ← @Sublocale.coe_inf, himp]
  compl a := a ⇨ ⊥
  himp_bot _ := rfl

中文:
实例 carrier.instHeytingAlgebra
  签名: : HeytingAlgebra S where
  定义体: by simp [← Subtype.coe_le_coe, ← @Sublocale.coe_inf, himp]
  compl a := a ⇨ ⊥
  himp_bot _ := rfl

Depends on / 依赖: Sublocale, Sublocale.coe_inf, Subtype, Subtype.coe_le_coe, coe_inf, coe_le_coe, himp_bot
-/
instance carrier.instHeytingAlgebra : HeytingAlgebra S where
  le_himp_iff a b c := by simp [← Subtype.coe_le_coe, ← @Sublocale.coe_inf, himp]
  compl a := a ⇨ ⊥
  himp_bot _ := rfl

/--
Instance `carrier.instFrame` / 实例 `carrier.instFrame`

English:
instance carrier.instFrame
  signature: : Order.Frame S where
  body: carrier.instHeytingAlgebra
  __ := carrier.instCompleteLattice

中文:
实例 carrier.instFrame
  签名: : Order.Frame S where
  定义体: carrier.instHeytingAlgebra
  __ := carrier.instCompleteLattice

Depends on / 依赖: carrier, carrier.instHeytingAlgebra, instHeytingAlgebra
-/
instance carrier.instFrame : Order.Frame S where
  __ := carrier.instHeytingAlgebra
  __ := carrier.instCompleteLattice

set_option backward.privateInPublic true in
/--
Definition of `restrictAux` / `restrictAux` 的定义

English:
definition restrictAux
  signature: (S : Sublocale X) (a : X)
  body: sInf {s : S | a <= s}

中文:
定义 restrictAux
  签名: (S : Sublocale X) (a : X)
  定义体: sInf {s : S | a <= s}
-/
private def restrictAux (S : Sublocale X) (a : X) : S := sInf {s : S | a <= s}

/--
lemma `le_restrictAux` / 引理 `le_restrictAux`

English:
lemma le_restrictAux
  statement: a <= S.restrictAux a
  proof: by simp +contextual [restrictAux]

中文:
引理 le_restrictAux
  结论: a <= S.restrictAux a
  证明: by simp +contextual [restrictAux]
-/
private lemma le_restrictAux : a <= S.restrictAux a := by simp +contextual [restrictAux]

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
/--
Definition of `giAux` / `giAux` 的定义

English:
definition giAux
  signature: (S : Sublocale X)
  body: ⟨x, by
    rw [le_antisymm le_restrictAux hx]
exact S.sInf_mem by simp +contextual [Set.subset_def]⟩
  gc a b := by
    constructor <;> intro h
    · exact le_trans (by simp +contextual [restrictAux]) h
    · exact sInf_le (by simp [h])
  le_l_u x := by simp [restrictAux]
  choice_eq a h := by simp 

中文:
定义 giAux
  签名: (S : Sublocale X)
  定义体: ⟨x, by
    rw [le_antisymm le_restrictAux hx]
exact S.sInf_mem by simp +contextual [Set.subset_def]⟩
  gc a b := by
    constructor <;> intro h
    · exact le_trans (by simp +contextual [restrictAux]) h
    · exact sInf_le (by simp [h])
  le_l_u x := by simp [restrictAux]
  choice_eq a h := by simp 
-/
private def giAux (S : Sublocale X) : GaloisInsertion S.restrictAux Subtype.val where
  choice x hx := ⟨x, by
    rw [le_antisymm le_restrictAux hx]
exact S.sInf_mem by simp +contextual [Set.subset_def]⟩
  gc a b := by
    constructor <;> intro h
    · exact le_trans (by simp +contextual [restrictAux]) h
    · exact sInf_le (by simp [h])
  le_l_u x := by simp [restrictAux]
  choice_eq a h := by simp [le_antisymm_iff, restrictAux, sInf_le]

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (S : Sublocale X)
  body: sInf {s : S | x <= s}
  map_inf' a b := by
    change Sublocale.restrictAux S (a ⊓ b) = Sublocale.restrictAux S a ⊓ Sublocale.restrictAux S b
    refine eq_of_forall_ge_iff (fun s => Iff.symm ?_)
    calc
      _ ↔ S.restrictAux a <= S.restrictAux b ⇨ s := by simp
      _ ↔ S.restrictAux b <= a ⇨ s 

中文:
定义 restrict
  签名: (S : Sublocale X)
  定义体: sInf {s : S | x <= s}
  map_inf' a b := by
    change Sublocale.restrictAux S (a ⊓ b) = Sublocale.restrictAux S a ⊓ Sublocale.restrictAux S b
    refine eq_of_forall_ge_iff (fun s => Iff.symm ?_)
    calc
      _ ↔ S.restrictAux a <= S.restrictAux b ⇨ s := by simp
      _ ↔ S.restrictAux b <= a ⇨ s 
-/
def restrict (S : Sublocale X) : FrameHom X S where
  toFun x := sInf {s : S | x <= s}
  map_inf' a b := by
    change Sublocale.restrictAux S (a ⊓ b) = Sublocale.restrictAux S a ⊓ Sublocale.restrictAux S b
    refine eq_of_forall_ge_iff (fun s => Iff.symm ?_)
    calc
      _ ↔ S.restrictAux a <= S.restrictAux b ⇨ s := by simp
      _ ↔ S.restrictAux b <= a ⇨ s := by rw [S.giAux.gc.le_iff_le, @le_himp_comm, coe_himp]
      _ ↔ b <= a ⇨ s := by
        set c : S := ⟨a ⇨ s, S.himp_mem s.coe_prop⟩
        change Sublocale.restrictAux S b <= c.val ↔ b <= c
        rw [S.giAux.u_le_u_iff]; rw [S.giAux.gc.le_iff_le]
      _ ↔ S.restrictAux (a ⊓ b) <= s := by simp [inf_comm, S.giAux.gc.le_iff_le]
  map_sSup' s := by
    change Sublocale.restrictAux S (sSup s) = _
    rw [S.giAux.gc.l_sSup]; rw [sSup_image]
    rfl
  map_top' := by
    refine le_antisymm le_top ?_
    change _ <= restrictAux S ⊤
    rw [← Subtype.coe_le_coe]; rw [S.giAux.gc.u_top]
    simp [restrictAux, sInf]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `giRestrict` / `giRestrict` 的定义

English:
definition giRestrict
  signature: (S : Sublocale X)
  body: S.giAux

中文:
定义 giRestrict
  签名: (S : Sublocale X)
  定义体: S.giAux

Depends on / 依赖: S.giAux
-/
def giRestrict (S : Sublocale X) : GaloisInsertion S.restrict Subtype.val := S.giAux

/--
lemma `restrict_of_mem` / 引理 `restrict_of_mem`

English:
lemma restrict_of_mem
  given: (ha : a in S)
  statement: S.restrict a = ⟨a, ha⟩
  proof: S.giRestrict.l_u_eq ⟨a, ha⟩

中文:
引理 restrict_of_mem
  条件: (ha : a in S)
  结论: S.restrict a = ⟨a, ha⟩
  证明: S.giRestrict.l_u_eq ⟨a, ha⟩
-/
@[simp] lemma restrict_of_mem (ha : a in S) : S.restrict a = ⟨a, ha⟩ := S.giRestrict.l_u_eq ⟨a, ha⟩

/-- The restriction from the locale X into a sublocale is a nucleus. -/
@[simps]
/--
Definition of `toNucleus` / `toNucleus` 的定义

English:
definition toNucleus
  signature: (S : Sublocale X)
  body: S.restrict x
  map_inf' _ _ := by simp [S.giRestrict.gc.u_inf]
  idempotent' _ := by rw [S.giRestrict.gc.l_u_l_eq_l]
  le_apply' _ := S.giRestrict.gc.le_u_l _

中文:
定义 toNucleus
  签名: (S : Sublocale X)
  定义体: S.restrict x
  map_inf' _ _ := by simp [S.giRestrict.gc.u_inf]
  idempotent' _ := by rw [S.giRestrict.gc.l_u_l_eq_l]
  le_apply' _ := S.giRestrict.gc.le_u_l _

Depends on / 依赖: S.restrict, restrict
-/
def toNucleus (S : Sublocale X) : Nucleus X where
  toFun x := S.restrict x
  map_inf' _ _ := by simp [S.giRestrict.gc.u_inf]
  idempotent' _ := by rw [S.giRestrict.gc.l_u_l_eq_l]
  le_apply' _ := S.giRestrict.gc.le_u_l _

/--
lemma `range_toNucleus` / 引理 `range_toNucleus`

English:
lemma range_toNucleus
  statement: range S.toNucleus = S
  proof: by
  ext x
  constructor
  · simp +contextual [eq_comm]
  · intro hx
    exact ⟨x, by simp_all⟩

中文:
引理 range_toNucleus
  结论: range S.toNucleus = S
  证明: by
  ext x
  constructor
  · simp +contextual [eq_comm]
  · intro hx
    exact ⟨x, by simp_all⟩
-/
@[simp] lemma range_toNucleus : range S.toNucleus = S := by
  ext x
  constructor
  · simp +contextual [eq_comm]
  · intro hx
    exact ⟨x, by simp_all⟩

/--
lemma `toNucleus_le_toNucleus` / 引理 `toNucleus_le_toNucleus`

English:
lemma toNucleus_le_toNucleus
  statement: S.toNucleus <= T.toNucleus ↔ T <= S
  proof: by
  simp [← Nucleus.range_subset_range]

中文:
引理 toNucleus_le_toNucleus
  结论: S.toNucleus <= T.toNucleus ↔ T <= S
  证明: by
  simp [← Nucleus.range_subset_range]
-/
@[simp] lemma toNucleus_le_toNucleus : S.toNucleus <= T.toNucleus ↔ T <= S := by
  simp [← Nucleus.range_subset_range]

end Sublocale

namespace Nucleus

/-- The range of a nucleus is a sublocale. -/
@[simps]
/--
Definition of `toSublocale` / `toSublocale` 的定义

English:
definition toSublocale
  signature: (n : Nucleus X)
  body: range n
  sInf_mem' a h := by
    rw [mem_range]
    refine le_antisymm (le_sInf_iff.mpr (fun b h1 => ?_)) le_apply
    simp_rw [subset_def, mem_range] at h
    rw [← h b h1]
    exact n.monotone (sInf_le h1)
  himp_mem' a b h := by rw [mem_range, ← h, map_himp_apply] at *

@[simp]

中文:
定义 toSublocale
  签名: (n : Nucleus X)
  定义体: range n
  sInf_mem' a h := by
    rw [mem_range]
    refine le_antisymm (le_sInf_iff.mpr (fun b h1 => ?_)) le_apply
    simp_rw [subset_def, mem_range] at h
    rw [← h b h1]
    exact n.monotone (sInf_le h1)
  himp_mem' a b h := by rw [mem_range, ← h, map_himp_apply] at *

@[simp]
-/
def toSublocale (n : Nucleus X) : Sublocale X where
  carrier := range n
  sInf_mem' a h := by
    rw [mem_range]
    refine le_antisymm (le_sInf_iff.mpr (fun b h1 => ?_)) le_apply
    simp_rw [subset_def, mem_range] at h
    rw [← h b h1]
    exact n.monotone (sInf_le h1)
  himp_mem' a b h := by rw [mem_range, ← h, map_himp_apply] at *

@[simp]
/--
lemma `mem_toSublocale` / 引理 `mem_toSublocale`

English:
lemma mem_toSublocale
  given: {n : Nucleus X} {x : X}
  statement: x in n.toSublocale ↔ exists y, n y = x
  proof: .rfl

中文:
引理 mem_toSublocale
  条件: {n : Nucleus X} {x : X}
  结论: x in n.toSublocale ↔ 存在 y, n y = x
  证明: .rfl
-/
lemma mem_toSublocale {n : Nucleus X} {x : X} : x in n.toSublocale ↔ exists y, n y = x := .rfl

/--
lemma `toSublocale_le_toSublocale` / 引理 `toSublocale_le_toSublocale`

English:
lemma toSublocale_le_toSublocale
  given: {m n : Nucleus X}
  proof: by simp [← SetLike.coe_subset_coe]

中文:
引理 toSublocale_le_toSublocale
  条件: {m n : Nucleus X}
  证明: by simp [← SetLike.coe_subset_coe]
-/
@[simp, gcongr] lemma toSublocale_le_toSublocale {m n : Nucleus X} :
    m.toSublocale <= n.toSublocale ↔ n <= m := by simp [← SetLike.coe_subset_coe]

/--
lemma `restrict_toSublocale` / 引理 `restrict_toSublocale`

English:
lemma restrict_toSublocale
  given: (n : Nucleus X) (x : X)
  proof: by
  ext
  simpa [Sublocale.restrict, sInf_image, le_antisymm_iff (a := iInf _)] using
    ⟨iInf₂_le_of_le ⟨n x, x, rfl⟩ n.le_apply le_rfl, fun y hxy => by simpa using n.monotone hxy⟩

中文:
引理 restrict_toSublocale
  条件: (n : Nucleus X) (x : X)
  证明: by
  ext
  simpa [Sublocale.restrict, sInf_image, le_antisymm_iff (a := iInf _)] using
    ⟨iInf₂_le_of_le ⟨n x, x, rfl⟩ n.le_apply le_rfl, fun y hxy => by simpa using n.monotone hxy⟩
-/
@[simp] lemma restrict_toSublocale (n : Nucleus X) (x : X) :
    n.toSublocale.restrict x = ⟨n x, x, rfl⟩ := by
  ext
  simpa [Sublocale.restrict, sInf_image, le_antisymm_iff (a := iInf _)] using
    ⟨iInf₂_le_of_le ⟨n x, x, rfl⟩ n.le_apply le_rfl, fun y hxy => by simpa using n.monotone hxy⟩

end Nucleus

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `nucleusIsoSublocale` / `nucleusIsoSublocale` 的定义

English:
definition nucleusIsoSublocale
  signature: : (Nucleus X)ᵒᵈ ≃o Sublocale X where
  body: n.ofDual.toSublocale
  invFun s := .toDual s.toNucleus
  left_inv := by simp [Function.LeftInverse, Nucleus.ext_iff]
  right_inv S := by ext x; simpa using ⟨by simp +contextual [eq_comm], fun hx => ⟨x, by simp [hx]⟩⟩
  map_rel_iff' := by simp

中文:
定义 nucleusIsoSublocale
  签名: : (Nucleus X)ᵒᵈ ≃o Sublocale X where
  定义体: n.ofDual.toSublocale
  invFun s := .toDual s.toNucleus
  left_inv := by simp [Function.LeftInverse, Nucleus.ext_iff]
  right_inv S := by ext x; simpa using ⟨by simp +contextual [eq_comm], fun hx => ⟨x, by simp [hx]⟩⟩
  map_rel_iff' := by simp

Depends on / 依赖: n.ofDual.toSublocale, ofDual, toSublocale
-/
def nucleusIsoSublocale : (Nucleus X)ᵒᵈ ≃o Sublocale X where
  toFun n := n.ofDual.toSublocale
  invFun s := .toDual s.toNucleus
  left_inv := by simp [Function.LeftInverse, Nucleus.ext_iff]
  right_inv S := by ext x; simpa using ⟨by simp +contextual [eq_comm], fun hx => ⟨x, by simp [hx]⟩⟩
  map_rel_iff' := by simp

/--
lemma `nucleusIsoSublocale.eq_toSublocale` / 引理 `nucleusIsoSublocale.eq_toSublocale`

English:
lemma nucleusIsoSublocale.eq_toSublocale
  statement: Nucleus.toSublocale = @nucleusIsoSublocale X _
  proof: rfl

中文:
引理 nucleusIsoSublocale.eq_toSublocale
  结论: Nucleus.toSublocale = @nucleusIsoSublocale X _
  证明: rfl
-/
lemma nucleusIsoSublocale.eq_toSublocale : Nucleus.toSublocale = @nucleusIsoSublocale X _ := rfl
/--
lemma `nucleusIsoSublocale.symm_eq_toNucleus` / 引理 `nucleusIsoSublocale.symm_eq_toNucleus`

English:
lemma nucleusIsoSublocale.symm_eq_toNucleus
  proof: rfl

中文:
引理 nucleusIsoSublocale.symm_eq_toNucleus
  证明: rfl
-/
lemma nucleusIsoSublocale.symm_eq_toNucleus :
  Sublocale.toNucleus = (@nucleusIsoSublocale X _).symm := rfl

/--
Instance `Sublocale.instCompleteLattice` / 实例 `Sublocale.instCompleteLattice`

English:
instance Sublocale.instCompleteLattice
  signature: : CompleteLattice (Sublocale X)
  body: nucleusIsoSublocale.toGaloisInsertion.liftCompleteLattice

中文:
实例 Sublocale.instCompleteLattice
  签名: : CompleteLattice (Sublocale X)
  定义体: nucleusIsoSublocale.toGaloisInsertion.liftCompleteLattice

Depends on / 依赖: liftCompleteLattice, nucleusIsoSublocale, nucleusIsoSublocale.toGaloisInsertion.liftCompleteLattice, toGaloisInsertion
-/
instance Sublocale.instCompleteLattice : CompleteLattice (Sublocale X) :=
  nucleusIsoSublocale.toGaloisInsertion.liftCompleteLattice

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Sublocale.instCoframe` / 实例 `Sublocale.instCoframe`

English:
instance Sublocale.instCoframe
  signature: : Order.Coframe (Sublocale X)
  body: .ofMinimalAxioms {
  iInf_sup_le_sup_sInf a s := by simp [← toNucleus_le_toNucleus,
    nucleusIsoSublocale.symm_eq_toNucleus, nucleusIsoSublocale.symm.map_sup,
    nucleusIsoSublocale.symm.map_sInf, sup_iInf_eq, nucleusIsoSublocale.symm.map_iInf] }

中文:
实例 Sublocale.instCoframe
  签名: : Order.Coframe (Sublocale X)
  定义体: .ofMinimalAxioms {
  iInf_sup_le_sup_sInf a s := by simp [← toNucleus_le_toNucleus,
    nucleusIsoSublocale.symm_eq_toNucleus, nucleusIsoSublocale.symm.map_sup,
    nucleusIsoSublocale.symm.map_sInf, sup_iInf_eq, nucleusIsoSublocale.symm.map_iInf] }

Depends on / 依赖: ofMinimalAxioms
-/
instance Sublocale.instCoframe : Order.Coframe (Sublocale X) := .ofMinimalAxioms {
  iInf_sup_le_sup_sInf a s := by simp [← toNucleus_le_toNucleus,
    nucleusIsoSublocale.symm_eq_toNucleus, nucleusIsoSublocale.symm.map_sup,
    nucleusIsoSublocale.symm.map_sInf, sup_iInf_eq, nucleusIsoSublocale.symm.map_iInf] }
