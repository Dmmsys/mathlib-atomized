/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Gabin Kolly
-/
module

public import Mathlib.Data.Fintype.Order
public import Mathlib.Order.Closure
public import Mathlib.ModelTheory.Semantics
public import Mathlib.ModelTheory.Encoding

/-!
# First-Order Substructures

This file defines substructures of first-order structures in a similar manner to the various
substructures appearing in the algebra library.

## Main Definitions

- A `FirstOrder.Language.Substructure` is defined so that `L.Substructure M` is the type of all
    substructures of the `L`-structure `M`.
- `FirstOrder.Language.Substructure.closure` is defined so that if `s : Set M`, `closure L s` is
    the least substructure of `M` containing `s`.
- `FirstOrder.Language.Substructure.comap` is defined so that `s.comap f` is the preimage of the
    substructure `s` under the homomorphism `f`, as a substructure.
- `FirstOrder.Language.Substructure.map` is defined so that `s.map f` is the image of the
    substructure `s` under the homomorphism `f`, as a substructure.
- `FirstOrder.Language.Hom.range` is defined so that `f.range` is the range of the
    homomorphism `f`, as a substructure.
- `FirstOrder.Language.Hom.domRestrict` and `FirstOrder.Language.Hom.codRestrict` restrict
    the domain and codomain respectively of first-order homomorphisms to substructures.
- `FirstOrder.Language.Embedding.domRestrict` and `FirstOrder.Language.Embedding.codRestrict`
    restrict the domain and codomain respectively of first-order embeddings to substructures.
- `FirstOrder.Language.Substructure.inclusion` is the inclusion embedding between substructures.
- `FirstOrder.Language.Substructure.PartialEquiv` is defined so that `PartialEquiv L M N` is
  the type of equivalences between substructures of `M` and `N`.

## Main Results

- `L.Substructure M` forms a `CompleteLattice`.
-/

@[expose] public section

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {M : Type w} {N P : Type*}
variable [L.Structure M] [L.Structure N] [L.Structure P]

open FirstOrder Cardinal

open Structure

section ClosedUnder

open Set

variable {n : Nat} (f : L.Functions n) (s : Set M)

/--
Definition of `ClosedUnder` / `ClosedUnder` 的定义

English:
definition ClosedUnder
  signature: : Prop
  body: forall x : Fin n -> M, (forall i : Fin n, x i in s) -> funMap f x in s

中文:
定义 ClosedUnder
  签名: : 命题
  定义体: forall x : Fin n -> M, (forall i : Fin n, x i in s) -> funMap f x in s

Depends on / 依赖: funMap
-/
def ClosedUnder : Prop :=
  forall x : Fin n -> M, (forall i : Fin n, x i in s) -> funMap f x in s

variable (L)

@[simp]
/--
theorem `closedUnder_univ` / 定理 `closedUnder_univ`

English:
theorem closedUnder_univ
  statement: ClosedUnder f (univ : Set M)
  proof: fun _ _ => mem_univ _

中文:
定理 closedUnder_univ
  结论: ClosedUnder f (univ : 集合 M)
  证明: fun _ _ => mem_univ _

Depends on / 依赖: mem_univ
-/
theorem closedUnder_univ : ClosedUnder f (univ : Set M) := fun _ _ => mem_univ _

variable {L f s} {t : Set M}

namespace ClosedUnder

/--
theorem `inter` / 定理 `inter`

English:
theorem inter
  given: (hs : ClosedUnder f s) (ht : ClosedUnder f t)
  statement: ClosedUnder f (s inter t)
  proof: fun x h =>
  mem_inter (hs x fun i => mem_of_mem_inter_left (h i)) (ht x fun i => mem_of_mem_inter_right (h i))

中文:
定理 inter
  条件: (hs : ClosedUnder f s) (ht : ClosedUnder f t)
  结论: ClosedUnder f (s inter t)
  证明: fun x h =>
  mem_inter (hs x fun i => mem_of_mem_inter_left (h i)) (ht x fun i => mem_of_mem_inter_right (h i))
-/
theorem inter (hs : ClosedUnder f s) (ht : ClosedUnder f t) : ClosedUnder f (s inter t) := fun x h =>
  mem_inter (hs x fun i => mem_of_mem_inter_left (h i)) (ht x fun i => mem_of_mem_inter_right (h i))

/--
theorem `inf` / 定理 `inf`

English:
theorem inf
  given: (hs : ClosedUnder f s) (ht : ClosedUnder f t)
  statement: ClosedUnder f (s ⊓ t)
  proof: hs.inter ht

中文:
定理 下确界
  条件: (hs : ClosedUnder f s) (ht : ClosedUnder f t)
  结论: ClosedUnder f (s ⊓ t)
  证明: hs.inter ht

Depends on / 依赖: hs.inter
-/
theorem inf (hs : ClosedUnder f s) (ht : ClosedUnder f t) : ClosedUnder f (s ⊓ t) :=
  hs.inter ht

variable {S : Set (Set M)}

/--
theorem `sInf` / 定理 `sInf`

English:
theorem sInf
  given: (hS : forall s, s in S -> ClosedUnder f s)
  statement: ClosedUnder f (sInf S)
  proof: fun x h s hs =>
  hS s hs x fun i => h i s hs

中文:
定理 sInf
  条件: (hS : 对任意 s, s in S -> ClosedUnder f s)
  结论: ClosedUnder f (sInf S)
  证明: fun x h s hs =>
  hS s hs x fun i => h i s hs
-/
theorem sInf (hS : forall s, s in S -> ClosedUnder f s) : ClosedUnder f (sInf S) := fun x h s hs =>
  hS s hs x fun i => h i s hs

end ClosedUnder

end ClosedUnder

variable (L) (M)

/--
Definition of `Substructure` / `Substructure` 的定义

English:
structure Substructure
  parameters: where
  axioms and operations (2):
    - carrier : Set M
    - fun_mem : forall {n}, forall f : L.Functions n, ClosedUnder f carrier

中文:
结构 子结构
  参数: where
  公理与运算 (2 个):
    - carrier : 集合 M
    - fun_mem : 对任意 {n}, 对任意 f : L.函数 n, ClosedUnder f carrier
-/
structure Substructure where
  /-- The underlying set of this substructure -/
  carrier : Set M
  fun_mem : forall {n}, forall f : L.Functions n, ClosedUnder f carrier

variable {L} {M}

namespace Substructure

attribute [coe] Substructure.carrier

/--
Instance `instSetLike` / 实例 `instSetLike`

English:
instance instSetLike
  signature: : SetLike (L.Substructure M) M
  body: ⟨Substructure.carrier, fun p q h => by cases p; cases q; congr⟩

中文:
实例 instSetLike
  签名: : 集合状 (L.子结构 M) M
  定义体: ⟨Substructure.carrier, fun p q h => by cases p; cases q; congr⟩

Depends on / 依赖: Substructure, Substructure.carrier, carrier
-/
instance instSetLike : SetLike (L.Substructure M) M :=
  ⟨Substructure.carrier, fun p q h => by cases p; cases q; congr⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (L.Substructure M)
  body: .ofSetLike (L.Substructure M) M

中文:
实例 :
  签名: 偏序 (L.子结构 M)
  定义体: .ofSetLike (L.Substructure M) M

Depends on / 依赖: L.Substructure, Substructure, ofSetLike
-/
instance : PartialOrder (L.Substructure M) := .ofSetLike (L.Substructure M) M

/--
Definition of `Simps.coe` / `Simps.coe` 的定义

English:
definition Simps.coe
  signature: (S : L.Substructure M)
  body: S

initialize_simps_projections Substructure (carrier -> coe, as_prefix coe)

@[simp]

中文:
定义 Simps.coe
  签名: (S : L.子结构 M)
  定义体: S

initialize_simps_projections Substructure (carrier -> coe, as_prefix coe)

@[simp]
-/
def Simps.coe (S : L.Substructure M) : Set M :=
  S

initialize_simps_projections Substructure (carrier -> coe, as_prefix coe)

@[simp]
/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  given: {s : L.Substructure M} {x : M}
  statement: x in s.carrier ↔ x in s
  proof: Iff.rfl

中文:
定理 mem_carrier
  条件: {s : L.子结构 M} {x : M}
  结论: x in s.carrier ↔ x in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier {s : L.Substructure M} {x : M} : x in s.carrier ↔ x in s :=
  Iff.rfl

/-- Two substructures are equal if they have the same elements. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {S T : L.Substructure M} (h : forall x, x in S ↔ x in T)
  statement: S = T
  proof: SetLike.ext h

中文:
定理 ext
  条件: {S T : L.子结构 M} (h : 对任意 x, x in S ↔ x in T)
  结论: S = T
  证明: SetLike.ext h

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext {S T : L.Substructure M} (h : forall x, x in S ↔ x in T) : S = T :=
  SetLike.ext h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (S : L.Substructure M) (s : Set M) (hs : s = S)
  body: s
  fun_mem _ f := hs.symm ▸ S.fun_mem _ f

中文:
定义 copy
  签名: (S : L.子结构 M) (s : 集合 M) (hs : s = S)
  定义体: s
  fun_mem _ f := hs.symm ▸ S.fun_mem _ f
-/
protected def copy (S : L.Substructure M) (s : Set M) (hs : s = S) : L.Substructure M where
  carrier := s
  fun_mem _ f := hs.symm ▸ S.fun_mem _ f

end Substructure

variable {S : L.Substructure M}

/--
theorem `Term.realize_mem` / 定理 `Term.realize_mem`

English:
theorem Term.realize_mem
  given: {α : Type*} (t : L.Term α) (xs : α -> M) (h : forall a, xs a in S)
  proof: by
  induction t with
  | var a => exact h a
  | func f ts ih => exact Substructure.fun_mem _ _ _ ih

中文:
定理 项.realize_mem
  条件: {α : 类型} (t : L.项 α) (xs : α -> M) (h : 对任意 a, xs a in S)
  证明: by
  induction t with
  | var a => exact h a
  | func f ts ih => exact Substructure.fun_mem _ _ _ ih

Depends on / 依赖: Substructure, Substructure.fun_mem, fun_mem
-/
theorem Term.realize_mem {α : Type*} (t : L.Term α) (xs : α -> M) (h : forall a, xs a in S) :
    t.realize xs in S := by
  induction t with
  | var a => exact h a
  | func f ts ih => exact Substructure.fun_mem _ _ _ ih

namespace Substructure

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: {s : Set M} (hs : s = S)
  statement: (S.copy s hs : Set M) = s
  proof: rfl

中文:
定理 coe_copy
  条件: {s : 集合 M} (hs : s = S)
  结论: (S.copy s hs : 集合 M) = s
  证明: rfl
-/
theorem coe_copy {s : Set M} (hs : s = S) : (S.copy s hs : Set M) = s :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: {s : Set M} (hs : s = S)
  statement: S.copy s hs = S
  proof: SetLike.coe_injective hs

中文:
定理 copy_eq
  条件: {s : 集合 M} (hs : s = S)
  结论: S.copy s hs = S
  证明: SetLike.coe_injective hs

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S :=
  SetLike.coe_injective hs

/--
theorem `constants_mem` / 定理 `constants_mem`

English:
theorem constants_mem
  given: (c : L.Constants)
  statement: (c : M) in S
  proof: mem_carrier.2 (S.fun_mem c _ finZeroElim)

中文:
定理 constants_mem
  条件: (c : L.Constants)
  结论: (c : M) in S
  证明: mem_carrier.2 (S.fun_mem c _ finZeroElim)

Depends on / 依赖: S.fun_mem, finZeroElim, fun_mem, mem_carrier
-/
theorem constants_mem (c : L.Constants) : (c : M) in S :=
  mem_carrier.2 (S.fun_mem c _ finZeroElim)

/--
Instance `instTop` / 实例 `instTop`

English:
instance instTop
  signature: : Top (L.Substructure M)
  body: ⟨{ carrier := Set.univ
      fun_mem := fun {_} _ _ _ => Set.mem_univ _ }⟩

中文:
实例 instTop
  签名: : 顶元素 (L.子结构 M)
  定义体: ⟨{ carrier := Set.univ
      fun_mem := fun {_} _ _ _ => Set.mem_univ _ }⟩

Depends on / 依赖: Set.mem_univ, Set.univ, carrier, fun_mem, mem_univ
-/
instance instTop : Top (L.Substructure M) :=
  ⟨{ carrier := Set.univ
      fun_mem := fun {_} _ _ _ => Set.mem_univ _ }⟩

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited (L.Substructure M)
  body: ⟨⊤⟩

@[simp]

中文:
实例 instInhabited
  签名: : 可居 (L.子结构 M)
  定义体: ⟨⊤⟩

@[simp]
-/
instance instInhabited : Inhabited (L.Substructure M) :=
  ⟨⊤⟩

@[simp]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  given: (x : M)
  statement: x in (⊤ : L.Substructure M)
  proof: Set.mem_univ x

@[simp]

中文:
定理 mem_top
  条件: (x : M)
  结论: x in (⊤ : L.子结构 M)
  证明: Set.mem_univ x

@[simp]

Depends on / 依赖: Set.mem_univ, mem_univ
-/
theorem mem_top (x : M) : x in (⊤ : L.Substructure M) :=
  Set.mem_univ x

@[simp]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: ((⊤ : L.Substructure M) : Set M) = Set.univ
  proof: rfl

中文:
定理 coe_top
  结论: ((⊤ : L.子结构 M) : 集合 M) = 集合.univ
  证明: rfl
-/
theorem coe_top : ((⊤ : L.Substructure M) : Set M) = Set.univ :=
  rfl

/--
Instance `instInf` / 实例 `instInf`

English:
instance instInf
  signature: : Min (L.Substructure M)
  body: ⟨fun S₁ S₂ =>
    { carrier := (S₁ : Set M) inter (S₂ : Set M)
      fun_mem := fun {_} f => (S₁.fun_mem f).inf (S₂.fun_mem f) }⟩

@[simp]

中文:
实例 instInf
  签名: : 最小值 (L.子结构 M)
  定义体: ⟨fun S₁ S₂ =>
    { carrier := (S₁ : Set M) inter (S₂ : Set M)
      fun_mem := fun {_} f => (S₁.fun_mem f).inf (S₂.fun_mem f) }⟩

@[simp]

Depends on / 依赖: carrier, fun_mem
-/
instance instInf : Min (L.Substructure M) :=
  ⟨fun S₁ S₂ =>
    { carrier := (S₁ : Set M) inter (S₂ : Set M)
      fun_mem := fun {_} f => (S₁.fun_mem f).inf (S₂.fun_mem f) }⟩

@[simp]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (p p' : L.Substructure M)
  proof: rfl

@[simp]

中文:
定理 coe_inf
  条件: (p p' : L.子结构 M)
  证明: rfl

@[simp]
-/
theorem coe_inf (p p' : L.Substructure M) :
    ((p ⊓ p' : L.Substructure M) : Set M) = (p : Set M) inter (p' : Set M) :=
  rfl

@[simp]
/--
theorem `mem_inf` / 定理 `mem_inf`

English:
theorem mem_inf
  given: {p p' : L.Substructure M} {x : M}
  statement: x in p ⊓ p' ↔ x in p ∧ x in p'
  proof: Iff.rfl

中文:
定理 mem_inf
  条件: {p p' : L.子结构 M} {x : M}
  结论: x in p ⊓ p' ↔ x in p ∧ x in p'
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_inf {p p' : L.Substructure M} {x : M} : x in p ⊓ p' ↔ x in p ∧ x in p' :=
  Iff.rfl

/--
Instance `instInfSet` / 实例 `instInfSet`

English:
instance instInfSet
  signature: : InfSet (L.Substructure M)
  body: ⟨fun s =>
    { carrier := ⋂ t in s, (t : Set M)
      fun_mem := fun {n} f =>
        ClosedUnder.sInf
          (by
            rintro _ ⟨t, rfl⟩
            by_cases h : t in s
            · simpa [h] using! t.fun_mem f
            · simp [h]) }⟩

@[simp, norm_cast]

中文:
实例 instInfSet
  签名: : 下确界集 (L.子结构 M)
  定义体: ⟨fun s =>
    { carrier := ⋂ t in s, (t : Set M)
      fun_mem := fun {n} f =>
        ClosedUnder.sInf
          (by
            rintro _ ⟨t, rfl⟩
            by_cases h : t in s
            · simpa [h] using! t.fun_mem f
            · simp [h]) }⟩

@[simp, norm_cast]

Depends on / 依赖: ClosedUnder, ClosedUnder.sInf, carrier, fun_mem, t.fun_mem
-/
instance instInfSet : InfSet (L.Substructure M) :=
  ⟨fun s =>
    { carrier := ⋂ t in s, (t : Set M)
      fun_mem := fun {n} f =>
        ClosedUnder.sInf
          (by
            rintro _ ⟨t, rfl⟩
            by_cases h : t in s
            · simpa [h] using! t.fun_mem f
            · simp [h]) }⟩

@[simp, norm_cast]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: (S : Set (L.Substructure M))
  proof: rfl

中文:
定理 coe_sInf
  条件: (S : 集合 (L.子结构 M))
  证明: rfl
-/
theorem coe_sInf (S : Set (L.Substructure M)) :
    ((sInf S : L.Substructure M) : Set M) = ⋂ s in S, (s : Set M) :=
  rfl

/--
theorem `mem_sInf` / 定理 `mem_sInf`

English:
theorem mem_sInf
  given: {S : Set (L.Substructure M)} {x : M}
  statement: x in sInf S ↔ forall p in S, x in p
  proof: Set.mem_iInter₂

中文:
定理 mem_sInf
  条件: {S : 集合 (L.子结构 M)} {x : M}
  结论: x in sInf S ↔ 对任意 p in S, x in p
  证明: Set.mem_iInter₂

Depends on / 依赖: Set.mem_iInter
-/
theorem mem_sInf {S : Set (L.Substructure M)} {x : M} : x in sInf S ↔ forall p in S, x in p :=
  Set.mem_iInter₂

/--
theorem `mem_iInf` / 定理 `mem_iInf`

English:
theorem mem_iInf
  given: {ι : Sort*} {S : ι -> L.Substructure M} {x : M}
  proof: by simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp, norm_cast]

中文:
定理 mem_iInf
  条件: {ι : 类型层*} {S : ι -> L.子结构 M} {x : M}
  证明: by simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp, norm_cast]

Depends on / 依赖: Set.forall_mem_range, forall_mem_range, mem_sInf
-/
theorem mem_iInf {ι : Sort*} {S : ι -> L.Substructure M} {x : M} :
    x in ⨅ i, S i ↔ forall i, x in S i := by simp only [iInf, mem_sInf, Set.forall_mem_range]

@[simp, norm_cast]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι : Sort*} {S : ι -> L.Substructure M}
  proof: by
  simp only [iInf, coe_sInf, Set.biInter_range]

中文:
定理 coe_iInf
  条件: {ι : 类型层*} {S : ι -> L.子结构 M}
  证明: by
  simp only [iInf, coe_sInf, Set.biInter_range]

Depends on / 依赖: Set.biInter_range, biInter_range, coe_sInf
-/
theorem coe_iInf {ι : Sort*} {S : ι -> L.Substructure M} :
    ((⨅ i, S i : L.Substructure M) : Set M) = ⋂ i, (S i : Set M) := by
  simp only [iInf, coe_sInf, Set.biInter_range]

/--
Instance `instCompleteLattice` / 实例 `instCompleteLattice`

English:
instance instCompleteLattice
  signature: : CompleteLattice (L.Substructure M)
  body: { completeLatticeOfInf (L.Substructure M) fun _ =>
      IsGLB.of_image
        (fun {S T : L.Substructure M} => show (S : Set M) <= T ↔ S <= T from SetLike.coe_subset_coe)
        isGLB_biInf with
    le := (· <= ·)
    lt := (· < ·)
    top := ⊤
    le_top := fun _ x _ => mem_top x
    inf := (· ⊓ ·)
    sInf := InfSet.sInf
    le_inf := fun _a _b _c ha hb _x hx => ⟨ha hx, hb hx⟩
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right }

中文:
实例 instCompleteLattice
  签名: : 完备格 (L.子结构 M)
  定义体: { completeLatticeOfInf (L.Substructure M) fun _ =>
      IsGLB.of_image
        (fun {S T : L.Substructure M} => show (S : Set M) <= T ↔ S <= T from SetLike.coe_subset_coe)
        isGLB_biInf with
    le := (· <= ·)
    lt := (· < ·)
    top := ⊤
    le_top := fun _ x _ => mem_top x
    inf := (· ⊓ ·)
    sInf := InfSet.sInf
    le_inf := fun _a _b _c ha hb _x hx => ⟨ha hx, hb hx⟩
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right }

Depends on / 依赖: And.left, And.right, InfSet, InfSet.sInf, IsGLB.of_image, L.Substructure, SetLike, SetLike.coe_subset_coe, Substructure, coe_subset_coe, completeLatticeOfInf, inf_le_left, inf_le_right, isGLB_biInf, le_inf, le_top, mem_top, of_image
-/
instance instCompleteLattice : CompleteLattice (L.Substructure M) :=
  { completeLatticeOfInf (L.Substructure M) fun _ =>
      IsGLB.of_image
        (fun {S T : L.Substructure M} => show (S : Set M) <= T ↔ S <= T from SetLike.coe_subset_coe)
        isGLB_biInf with
    le := (· <= ·)
    lt := (· < ·)
    top := ⊤
    le_top := fun _ x _ => mem_top x
    inf := (· ⊓ ·)
    sInf := InfSet.sInf
    le_inf := fun _a _b _c ha hb _x hx => ⟨ha hx, hb hx⟩
    inf_le_left := fun _ _ _ => And.left
    inf_le_right := fun _ _ _ => And.right }

variable (L)

/--
Definition of `closure` / `closure` 的定义

English:
definition closure
  signature: : LowerAdjoint ((↑) : L.Substructure M -> Set M)
  body: ⟨fun s => sInf { S | s subseteq S }, fun _ _ =>
    ⟨Set.Subset.trans fun _x hx => mem_sInf.2 fun _S hS => hS hx, fun h => sInf_le h⟩⟩

中文:
定义 closure
  签名: : LowerAdjoint ((↑) : L.子结构 M -> 集合 M)
  定义体: ⟨fun s => sInf { S | s subseteq S }, fun _ _ =>
    ⟨Set.Subset.trans fun _x hx => mem_sInf.2 fun _S hS => hS hx, fun h => sInf_le h⟩⟩

Depends on / 依赖: Set.Subset.trans, Subset, mem_sInf, sInf_le, subseteq
-/
def closure : LowerAdjoint ((↑) : L.Substructure M -> Set M) :=
  ⟨fun s => sInf { S | s subseteq S }, fun _ _ =>
    ⟨Set.Subset.trans fun _x hx => mem_sInf.2 fun _S hS => hS hx, fun h => sInf_le h⟩⟩

variable {L} {s : Set M}

/--
theorem `mem_closure` / 定理 `mem_closure`

English:
theorem mem_closure
  given: {x : M}
  statement: x in closure L s ↔ forall S : L.Substructure M, s subseteq S -> x in S
  proof: mem_sInf

中文:
定理 mem_closure
  条件: {x : M}
  结论: x in closure L s ↔ 对任意 S : L.子结构 M, s subseteq S -> x in S
  证明: mem_sInf

Depends on / 依赖: mem_sInf
-/
theorem mem_closure {x : M} : x in closure L s ↔ forall S : L.Substructure M, s subseteq S -> x in S :=
  mem_sInf

/-- The substructure generated by a set includes the set. -/
@[simp]
/--
theorem `subset_closure` / 定理 `subset_closure`

English:
theorem subset_closure
  statement: s subseteq closure L s
  proof: (closure L).le_closure s

中文:
定理 subset_closure
  结论: s subseteq closure L s
  证明: (closure L).le_closure s

Depends on / 依赖: closure, le_closure
-/
theorem subset_closure : s subseteq closure L s :=
  (closure L).le_closure s

/--
theorem `notMem_of_notMem_closure` / 定理 `notMem_of_notMem_closure`

English:
theorem notMem_of_notMem_closure
  given: {P : M} (hP : P ∉ closure L s)
  statement: P ∉ s
  proof: fun h =>
  hP (subset_closure h)

@[simp]

中文:
定理 notMem_of_notMem_closure
  条件: {P : M} (hP : P ∉ closure L s)
  结论: P ∉ s
  证明: fun h =>
  hP (subset_closure h)

@[simp]
-/
theorem notMem_of_notMem_closure {P : M} (hP : P ∉ closure L s) : P ∉ s := fun h =>
  hP (subset_closure h)

@[simp]
/--
theorem `closed` / 定理 `closed`

English:
theorem closed
  given: (S : L.Substructure M)
  statement: (S : Set M) in (closure L).closed
  proof: congr rfl ((closure L).eq_of_le Set.Subset.rfl fun _x xS => mem_closure.2 fun _T hT => hT xS)

中文:
定理 closed
  条件: (S : L.子结构 M)
  结论: (S : 集合 M) in (closure L).closed
  证明: congr rfl ((closure L).eq_of_le Set.Subset.rfl fun _x xS => mem_closure.2 fun _T hT => hT xS)

Depends on / 依赖: Set.Subset.rfl, Subset, closure, eq_of_le, mem_closure
-/
theorem closed (S : L.Substructure M) : (S : Set M) in (closure L).closed :=
  congr rfl ((closure L).eq_of_le Set.Subset.rfl fun _x xS => mem_closure.2 fun _T hT => hT xS)

open Set

/-- A substructure `S` includes `closure L s` if and only if it includes `s`. -/
@[simp]
/--
theorem `closure_le` / 定理 `closure_le`

English:
theorem closure_le
  statement: closure L s <= S ↔ s subseteq S
  proof: (closure L).closure_le_closed_iff_le s S.closed

中文:
定理 closure_le
  结论: closure L s <= S ↔ s subseteq S
  证明: (closure L).closure_le_closed_iff_le s S.closed

Depends on / 依赖: S.closed, closed, closure, closure_le_closed_iff_le
-/
theorem closure_le : closure L s <= S ↔ s subseteq S :=
  (closure L).closure_le_closed_iff_le s S.closed

/-- Substructure closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure L s ≤ closure L t`. -/
@[gcongr]
/--
theorem `closure_mono` / 定理 `closure_mono`

English:
theorem closure_mono
  given: ⦃s t
  statement: Set M⦄ (h : s subseteq t) : closure L s <= closure L t
  proof: (closure L).monotone h

中文:
定理 closure_mono
  条件: ⦃s t
  结论: 集合 M⦄ (h : s subseteq t) : closure L s <= closure L t
  证明: (closure L).monotone h

Depends on / 依赖: closure, monotone
-/
theorem closure_mono ⦃s t : Set M⦄ (h : s subseteq t) : closure L s <= closure L t :=
  (closure L).monotone h

/--
theorem `closure_eq_of_le` / 定理 `closure_eq_of_le`

English:
theorem closure_eq_of_le
  given: (h₁ : s subseteq S) (h₂ : S <= closure L s)
  statement: closure L s = S
  proof: (closure L).eq_of_le h₁ h₂

中文:
定理 closure_eq_of_le
  条件: (h₁ : s subseteq S) (h₂ : S <= closure L s)
  结论: closure L s = S
  证明: (closure L).eq_of_le h₁ h₂

Depends on / 依赖: closure, eq_of_le
-/
theorem closure_eq_of_le (h₁ : s subseteq S) (h₂ : S <= closure L s) : closure L s = S :=
  (closure L).eq_of_le h₁ h₂

/--
theorem `coe_closure_eq_range_term_realize` / 定理 `coe_closure_eq_range_term_realize`

English:
theorem coe_closure_eq_range_term_realize
  proof: by
  let S : L.Substructure M := ⟨range (Term.realize (L := L) ((↑) : s -> M)), fun {n} f x hx => by
    simp only [mem_range] at *
    refine ⟨func f fun i => Classical.choose (hx i), ?_⟩
    simp only [Term.realize, fun i => Classical.choose_spec (hx i)]⟩
  change _ = (S : Set M)
  rw [← SetLike.ext'_iff]
  refine closure_eq_of_le (fun x hx => ⟨var ⟨x, hx⟩, rfl⟩) (le_sInf fun S' hS' => ?_)
  rintro _ ⟨t, rfl⟩
  exact t.realize_mem _ fun i => hS' i.2

中文:
定理 coe_closure_eq_range_term_realize
  证明: by
  let S : L.Substructure M := ⟨range (Term.realize (L := L) ((↑) : s -> M)), fun {n} f x hx => by
    simp only [mem_range] at *
    refine ⟨func f fun i => Classical.choose (hx i), ?_⟩
    simp only [Term.realize, fun i => Classical.choose_spec (hx i)]⟩
  change _ = (S : Set M)
  rw [← SetLike.ext'_iff]
  refine closure_eq_of_le (fun x hx => ⟨var ⟨x, hx⟩, rfl⟩) (le_sInf fun S' hS' => ?_)
  rintro _ ⟨t, rfl⟩
  exact t.realize_mem _ fun i => hS' i.2

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, L.Substructure, SetLike, SetLike.ext, Substructure, Term.realize, _iff, choose_spec, closure_eq_of_le, le_sInf, mem_range, realize, realize_mem, t.realize_mem
-/
theorem coe_closure_eq_range_term_realize :
    (closure L s : Set M) = range (@Term.realize L _ _ _ ((↑) : s -> M)) := by
  let S : L.Substructure M := ⟨range (Term.realize (L := L) ((↑) : s -> M)), fun {n} f x hx => by
    simp only [mem_range] at *
    refine ⟨func f fun i => Classical.choose (hx i), ?_⟩
    simp only [Term.realize, fun i => Classical.choose_spec (hx i)]⟩
  change _ = (S : Set M)
  rw [← SetLike.ext'_iff]
  refine closure_eq_of_le (fun x hx => ⟨var ⟨x, hx⟩, rfl⟩) (le_sInf fun S' hS' => ?_)
  rintro _ ⟨t, rfl⟩
  exact t.realize_mem _ fun i => hS' i.2

/--
Instance `small_closure` / 实例 `small_closure`

English:
instance small_closure
  signature: [Small.{u} s]
  body: by
  rw [← SetLike.coe_sort_coe]; rw [Substructure.coe_closure_eq_range_term_realize]
  exact small_range _

中文:
实例 small_closure
  签名: [Small.{u} s]
  定义体: by
  rw [← SetLike.coe_sort_coe]; rw [Substructure.coe_closure_eq_range_term_realize]
  exact small_range _

Depends on / 依赖: SetLike, SetLike.coe_sort_coe, Substructure, Substructure.coe_closure_eq_range_term_realize, coe_closure_eq_range_term_realize, coe_sort_coe, small_range
-/
instance small_closure [Small.{u} s] : Small.{u} (closure L s) := by
  rw [← SetLike.coe_sort_coe]; rw [Substructure.coe_closure_eq_range_term_realize]
  exact small_range _

/--
theorem `mem_closure_iff_exists_term` / 定理 `mem_closure_iff_exists_term`

English:
theorem mem_closure_iff_exists_term
  given: {x : M}
  proof: by
  rw [← SetLike.mem_coe]; rw [coe_closure_eq_range_term_realize]; rw [mem_range]

中文:
定理 mem_closure_iff_存在_term
  条件: {x : M}
  证明: by
  rw [← SetLike.mem_coe]; rw [coe_closure_eq_range_term_realize]; rw [mem_range]

Depends on / 依赖: SetLike, SetLike.mem_coe, coe_closure_eq_range_term_realize, mem_coe, mem_range
-/
theorem mem_closure_iff_exists_term {x : M} :
    x in closure L s ↔ exists t : L.Term s, t.realize ((↑) : s -> M) = x := by
  rw [← SetLike.mem_coe]; rw [coe_closure_eq_range_term_realize]; rw [mem_range]

/--
theorem `lift_card_closure_le_card_term` / 定理 `lift_card_closure_le_card_term`

English:
theorem lift_card_closure_le_card_term
  statement: Cardinal.lift.{max u w} #(closure L s) <= #(L.Term s)
  proof: by
  rw [← SetLike.coe_sort_coe]; rw [coe_closure_eq_range_term_realize]
  rw [← Cardinal.lift_id'.{w]; rw [max u w} #(L.Term s)]
  exact Cardinal.mk_range_le_lift

中文:
定理 lift_card_closure_le_card_term
  结论: 基数.lift.{最大值 u w} #(closure L s) <= #(L.项 s)
  证明: by
  rw [← SetLike.coe_sort_coe]; rw [coe_closure_eq_range_term_realize]
  rw [← Cardinal.lift_id'.{w]; rw [max u w} #(L.Term s)]
  exact Cardinal.mk_range_le_lift

Depends on / 依赖: Cardinal, Cardinal.lift_id, Cardinal.mk_range_le_lift, L.Term, SetLike, SetLike.coe_sort_coe, coe_closure_eq_range_term_realize, coe_sort_coe, lift_id, mk_range_le_lift
-/
theorem lift_card_closure_le_card_term : Cardinal.lift.{max u w} #(closure L s) <= #(L.Term s) := by
  rw [← SetLike.coe_sort_coe]; rw [coe_closure_eq_range_term_realize]
  rw [← Cardinal.lift_id'.{w]; rw [max u w} #(L.Term s)]
  exact Cardinal.mk_range_le_lift

/--
theorem `lift_card_closure_le` / 定理 `lift_card_closure_le`

English:
theorem lift_card_closure_le
  proof: by
  rw [← lift_umax]
  refine lift_card_closure_le_card_term.trans (Term.card_le.trans ?_)
  rw [mk_sum]; rw [lift_umax.{w]; rw [u}]

中文:
定理 lift_card_closure_le
  证明: by
  rw [← lift_umax]
  refine lift_card_closure_le_card_term.trans (Term.card_le.trans ?_)
  rw [mk_sum]; rw [lift_umax.{w]; rw [u}]

Depends on / 依赖: Term.card_le.trans, card_le, lift_card_closure_le_card_term, lift_card_closure_le_card_term.trans, lift_umax, mk_sum
-/
theorem lift_card_closure_le :
    Cardinal.lift.{u, w} #(closure L s) <=
      max ℵ₀ (Cardinal.lift.{u, w} #s + Cardinal.lift.{w, u} #(Σ i, L.Functions i)) := by
  rw [← lift_umax]
  refine lift_card_closure_le_card_term.trans (Term.card_le.trans ?_)
  rw [mk_sum]; rw [lift_umax.{w]; rw [u}]

/--
lemma `mem_closed_iff` / 引理 `mem_closed_iff`

English:
lemma mem_closed_iff
  given: (s : Set M)
  proof: by
  refine ⟨fun h n f => ?_, fun h => ?_⟩
  · rw [← h]
    exact Substructure.fun_mem _ _
  · have h' : closure L s = ⟨s, h⟩ := closure_eq_of_le (refl _) subset_closure
    exact congr_arg _ h'

中文:
引理 mem_closed_iff
  条件: (s : 集合 M)
  证明: by
  refine ⟨fun h n f => ?_, fun h => ?_⟩
  · rw [← h]
    exact Substructure.fun_mem _ _
  · have h' : closure L s = ⟨s, h⟩ := closure_eq_of_le (refl _) subset_closure
    exact congr_arg _ h'

Depends on / 依赖: Substructure, Substructure.fun_mem, closure, closure_eq_of_le, congr_arg, fun_mem, subset_closure
-/
lemma mem_closed_iff (s : Set M) :
    s in (closure L).closed ↔ forall {n}, forall f : L.Functions n, ClosedUnder f s := by
  refine ⟨fun h n f => ?_, fun h => ?_⟩
  · rw [← h]
    exact Substructure.fun_mem _ _
  · have h' : closure L s = ⟨s, h⟩ := closure_eq_of_le (refl _) subset_closure
    exact congr_arg _ h'

variable (L)

/--
lemma `mem_closed_of_isRelational` / 引理 `mem_closed_of_isRelational`

English:
lemma mem_closed_of_isRelational
  given: [L.IsRelational] (s : Set M)
  statement: s in (closure L).closed
  proof: (mem_closed_iff s).2 isEmptyElim

@[simp]

中文:
引理 mem_closed_of_isRelational
  条件: [L.IsRelational] (s : 集合 M)
  结论: s in (closure L).closed
  证明: (mem_closed_iff s).2 isEmptyElim

@[simp]

Depends on / 依赖: isEmptyElim, mem_closed_iff
-/
lemma mem_closed_of_isRelational [L.IsRelational] (s : Set M) : s in (closure L).closed :=
  (mem_closed_iff s).2 isEmptyElim

@[simp]
/--
lemma `closure_eq_of_isRelational` / 引理 `closure_eq_of_isRelational`

English:
lemma closure_eq_of_isRelational
  given: [L.IsRelational] (s : Set M)
  statement: closure L s = s
  proof: LowerAdjoint.closure_eq_self_of_mem_closed _ (mem_closed_of_isRelational L s)

@[simp]

中文:
引理 closure_eq_of_isRelational
  条件: [L.IsRelational] (s : 集合 M)
  结论: closure L s = s
  证明: LowerAdjoint.closure_eq_self_of_mem_closed _ (mem_closed_of_isRelational L s)

@[simp]

Depends on / 依赖: LowerAdjoint, LowerAdjoint.closure_eq_self_of_mem_closed, closure_eq_self_of_mem_closed, mem_closed_of_isRelational
-/
lemma closure_eq_of_isRelational [L.IsRelational] (s : Set M) : closure L s = s :=
  LowerAdjoint.closure_eq_self_of_mem_closed _ (mem_closed_of_isRelational L s)

@[simp]
/--
lemma `mem_closure_iff_of_isRelational` / 引理 `mem_closure_iff_of_isRelational`

English:
lemma mem_closure_iff_of_isRelational
  given: [L.IsRelational] (s : Set M) (m : M)
  proof: by
  rw [← SetLike.mem_coe]; rw [closure_eq_of_isRelational]

中文:
引理 mem_closure_iff_of_isRelational
  条件: [L.IsRelational] (s : 集合 M) (m : M)
  证明: by
  rw [← SetLike.mem_coe]; rw [closure_eq_of_isRelational]

Depends on / 依赖: SetLike, SetLike.mem_coe, closure_eq_of_isRelational, mem_coe
-/
lemma mem_closure_iff_of_isRelational [L.IsRelational] (s : Set M) (m : M) :
    m in closure L s ↔ m in s := by
  rw [← SetLike.mem_coe]; rw [closure_eq_of_isRelational]

/--
theorem `_root_.Set.Countable.substructure_closure` / 定理 `_root_.Set.Countable.substructure_closure`

English:
theorem _root_.Set.Countable.substructure_closure
  proof: by
  have : Countable s := h.to_subtype
  rw [← mk_le_aleph0_iff]; rw [← lift_le_aleph0]
  exact lift_card_closure_le_card_term.trans mk_le_aleph0

中文:
定理 _root_.集合.可数.substructure_closure
  证明: by
  have : Countable s := h.to_subtype
  rw [← mk_le_aleph0_iff]; rw [← lift_le_aleph0]
  exact lift_card_closure_le_card_term.trans mk_le_aleph0

Depends on / 依赖: Countable, h.to_subtype, lift_card_closure_le_card_term, lift_card_closure_le_card_term.trans, lift_le_aleph0, mk_le_aleph0, mk_le_aleph0_iff, to_subtype
-/
theorem _root_.Set.Countable.substructure_closure
    [Countable (Σ l, L.Functions l)] (h : s.Countable) : Countable.{w + 1} (closure L s) := by
  have : Countable s := h.to_subtype
  rw [← mk_le_aleph0_iff]; rw [← lift_le_aleph0]
  exact lift_card_closure_le_card_term.trans mk_le_aleph0

variable {L} (S)

/-- An induction principle for closure membership. If `p` holds for all elements of `s`, and
is preserved under function symbols, then `p` holds for all elements of the closure of `s`. -/
@[elab_as_elim]
/--
theorem `closure_induction` / 定理 `closure_induction`

English:
theorem closure_induction
  statement: {p : M -> Prop} {x} (h : x in closure L s) (Hs : forall x in s, p x)
  proof: (@closure_le L M _ ⟨Set.ofPred p, fun {_} => Hfun⟩ _).2 Hs h

中文:
定理 closure_induction
  结论: {p : M -> 命题} {x} (h : x in closure L s) (Hs : 对任意 x in s, p x)
  证明: (@closure_le L M _ ⟨Set.ofPred p, fun {_} => Hfun⟩ _).2 Hs h

Depends on / 依赖: Set.ofPred, closure_le, ofPred
-/
theorem closure_induction {p : M -> Prop} {x} (h : x in closure L s) (Hs : forall x in s, p x)
    (Hfun : forall {n : Nat} (f : L.Functions n), ClosedUnder f (Set.ofPred p)) : p x :=
  (@closure_le L M _ ⟨Set.ofPred p, fun {_} => Hfun⟩ _).2 Hs h

/-- If `s` is a dense set in a structure `M`, `Substructure.closure L s = ⊤`, then in order to prove
that some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`, and verify
that `p` is preserved under function symbols. -/
@[elab_as_elim]
/--
theorem `dense_induction` / 定理 `dense_induction`

English:
theorem dense_induction
  statement: {p : M -> Prop} (x : M) {s : Set M} (hs : closure L s = ⊤)
  proof: by
  have : forall x in closure L s, p x := fun x hx => closure_induction hx Hs fun {n} => Hfun
  simpa [hs] using this x

中文:
定理 dense_induction
  结论: {p : M -> 命题} (x : M) {s : 集合 M} (hs : closure L s = ⊤)
  证明: by
  have : forall x in closure L s, p x := fun x hx => closure_induction hx Hs fun {n} => Hfun
  simpa [hs] using this x

Depends on / 依赖: closure, closure_induction
-/
theorem dense_induction {p : M -> Prop} (x : M) {s : Set M} (hs : closure L s = ⊤)
    (Hs : forall x in s, p x) (Hfun : forall {n : Nat} (f : L.Functions n), ClosedUnder f (Set.ofPred p)) :
    p x := by
  have : forall x in closure L s, p x := fun x hx => closure_induction hx Hs fun {n} => Hfun
  simpa [hs] using this x

variable (L) (M)

/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion (@closure L M _) (↑) where
  body: closure L s
  gc := (closure L).gc
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl

中文:
定义 gi
  签名: : Galois嵌入 (@closure L M _) (↑) where
  定义体: closure L s
  gc := (closure L).gc
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl
-/
protected def gi : GaloisInsertion (@closure L M _) (↑) where
  choice s _ := closure L s
  gc := (closure L).gc
  le_l_u _ := subset_closure
  choice_eq _ _ := rfl

variable {L} {M}

/-- Closure of a substructure `S` equals `S`. -/
@[simp]
/--
theorem `closure_eq` / 定理 `closure_eq`

English:
theorem closure_eq
  statement: closure L (S : Set M) = S
  proof: (Substructure.gi L M).l_u_eq S

@[simp]

中文:
定理 closure_eq
  结论: closure L (S : 集合 M) = S
  证明: (Substructure.gi L M).l_u_eq S

@[simp]

Depends on / 依赖: Substructure, Substructure.gi, l_u_eq
-/
theorem closure_eq : closure L (S : Set M) = S :=
  (Substructure.gi L M).l_u_eq S

@[simp]
/--
theorem `closure_empty` / 定理 `closure_empty`

English:
theorem closure_empty
  statement: closure L (∅ : Set M) = ⊥
  proof: (Substructure.gi L M).gc.l_bot

@[simp]

中文:
定理 closure_empty
  结论: closure L (∅ : 集合 M) = ⊥
  证明: (Substructure.gi L M).gc.l_bot

@[simp]

Depends on / 依赖: Substructure, Substructure.gi, gc.l_bot, l_bot
-/
theorem closure_empty : closure L (∅ : Set M) = ⊥ :=
  (Substructure.gi L M).gc.l_bot

@[simp]
/--
theorem `closure_univ` / 定理 `closure_univ`

English:
theorem closure_univ
  statement: closure L (univ : Set M) = ⊤
  proof: @coe_top L M _ ▸ closure_eq ⊤

中文:
定理 closure_univ
  结论: closure L (univ : 集合 M) = ⊤
  证明: @coe_top L M _ ▸ closure_eq ⊤

Depends on / 依赖: closure_eq, coe_top
-/
theorem closure_univ : closure L (univ : Set M) = ⊤ :=
  @coe_top L M _ ▸ closure_eq ⊤

/--
theorem `closure_union` / 定理 `closure_union`

English:
theorem closure_union
  given: (s t : Set M)
  statement: closure L (s union t) = closure L s ⊔ closure L t
  proof: (Substructure.gi L M).gc.l_sup

中文:
定理 closure_union
  条件: (s t : 集合 M)
  结论: closure L (s union t) = closure L s ⊔ closure L t
  证明: (Substructure.gi L M).gc.l_sup

Depends on / 依赖: Substructure, Substructure.gi, gc.l_sup, l_sup
-/
theorem closure_union (s t : Set M) : closure L (s union t) = closure L s ⊔ closure L t :=
  (Substructure.gi L M).gc.l_sup

/--
theorem `closure_iUnion` / 定理 `closure_iUnion`

English:
theorem closure_iUnion
  given: {ι} (s : ι -> Set M)
  statement: closure L (⋃ i, s i) = ⨆ i, closure L (s i)
  proof: (Substructure.gi L M).gc.l_iSup

中文:
定理 closure_iUnion
  条件: {ι} (s : ι -> 集合 M)
  结论: closure L (⋃ i, s i) = ⨆ i, closure L (s i)
  证明: (Substructure.gi L M).gc.l_iSup

Depends on / 依赖: Substructure, Substructure.gi, gc.l_iSup, l_iSup
-/
theorem closure_iUnion {ι} (s : ι -> Set M) : closure L (⋃ i, s i) = ⨆ i, closure L (s i) :=
  (Substructure.gi L M).gc.l_iSup

/--
theorem `closure_insert` / 定理 `closure_insert`

English:
theorem closure_insert
  given: (s : Set M) (m : M)
  statement: closure L (insert m s) = closure L {m} ⊔ closure L s
  proof: closure_union {m} s

中文:
定理 closure_insert
  条件: (s : 集合 M) (m : M)
  结论: closure L (insert m s) = closure L {m} ⊔ closure L s
  证明: closure_union {m} s

Depends on / 依赖: closure_union
-/
theorem closure_insert (s : Set M) (m : M) : closure L (insert m s) = closure L {m} ⊔ closure L s :=
  closure_union {m} s

/--
Instance `small_bot` / 实例 `small_bot`

English:
instance small_bot
  signature: : Small.{u} (⊥ : L.Substructure M)
  body: by
  rw [← closure_empty]
  have : Small.{u} (∅ : Set M) := small_subsingleton _
  exact Substructure.small_closure

中文:
实例 small_bot
  签名: : Small.{u} (⊥ : L.子结构 M)
  定义体: by
  rw [← closure_empty]
  have : Small.{u} (∅ : Set M) := small_subsingleton _
  exact Substructure.small_closure

Depends on / 依赖: Substructure, Substructure.small_closure, closure_empty, small_closure, small_subsingleton
-/
instance small_bot : Small.{u} (⊥ : L.Substructure M) := by
  rw [← closure_empty]
  have : Small.{u} (∅ : Set M) := small_subsingleton _
  exact Substructure.small_closure

/--
theorem `iSup_eq_closure` / 定理 `iSup_eq_closure`

English:
theorem iSup_eq_closure
  given: {ι : Sort*} (S : ι -> L.Substructure M)
  proof: by simp_rw [closure_iUnion, closure_eq]

中文:
定理 iSup_eq_closure
  条件: {ι : 类型层*} (S : ι -> L.子结构 M)
  证明: by simp_rw [closure_iUnion, closure_eq]

Depends on / 依赖: closure_eq, closure_iUnion, simp_rw
-/
theorem iSup_eq_closure {ι : Sort*} (S : ι -> L.Substructure M) :
    ⨆ i, S i = closure L (⋃ i, (S i : Set M)) := by simp_rw [closure_iUnion, closure_eq]

-- This proof uses the fact that `Substructure.closure` is finitary.
/--
theorem `mem_iSup_of_directed` / 定理 `mem_iSup_of_directed`

English:
theorem mem_iSup_of_directed
  statement: {ι : Type*} [hι : Nonempty ι] {S : ι -> L.Substructure M}
  proof: by
  refine ⟨?_, fun ⟨i, hi⟩ => le_iSup S i hi⟩
  suffices x in closure L (⋃ i, (S i : Set M)) -> exists i, x in S i by
    simpa only [closure_iUnion, closure_eq (S _)] using this
  refine fun hx => closure_induction hx (fun _ => mem_iUnion.1) (fun f v hC => ?_)
  simp_rw [Set.mem_ofPred] at *
  have ⟨i, hi⟩ := hS.finite_le (fun i => Classical.choose (hC i))
  refine ⟨i, (S i).fun_mem f v (fun j => hi j (Classical.choose_spec (hC j)))⟩

中文:
定理 mem_iSup_of_directed
  结论: {ι : 类型} [hι : 非空 ι] {S : ι -> L.子结构 M}
  证明: by
  refine ⟨?_, fun ⟨i, hi⟩ => le_iSup S i hi⟩
  suffices x in closure L (⋃ i, (S i : Set M)) -> exists i, x in S i by
    simpa only [closure_iUnion, closure_eq (S _)] using this
  refine fun hx => closure_induction hx (fun _ => mem_iUnion.1) (fun f v hC => ?_)
  simp_rw [Set.mem_ofPred] at *
  have ⟨i, hi⟩ := hS.finite_le (fun i => Classical.choose (hC i))
  refine ⟨i, (S i).fun_mem f v (fun j => hi j (Classical.choose_spec (hC j)))⟩

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, Set.mem_ofPred, choose_spec, closure, closure_eq, closure_iUnion, closure_induction, finite_le, fun_mem, hS.finite_le, le_iSup, mem_iUnion, mem_ofPred, simp_rw
-/
theorem mem_iSup_of_directed {ι : Type*} [hι : Nonempty ι] {S : ι -> L.Substructure M}
    (hS : Directed (· <= ·) S) {x : M} :
    x in ⨆ i, S i ↔ exists i, x in S i := by
  refine ⟨?_, fun ⟨i, hi⟩ => le_iSup S i hi⟩
  suffices x in closure L (⋃ i, (S i : Set M)) -> exists i, x in S i by
    simpa only [closure_iUnion, closure_eq (S _)] using this
  refine fun hx => closure_induction hx (fun _ => mem_iUnion.1) (fun f v hC => ?_)
  simp_rw [Set.mem_ofPred] at *
  have ⟨i, hi⟩ := hS.finite_le (fun i => Classical.choose (hC i))
  refine ⟨i, (S i).fun_mem f v (fun j => hi j (Classical.choose_spec (hC j)))⟩

-- This proof uses the fact that `Substructure.closure` is finitary.
/--
theorem `mem_sSup_of_directedOn` / 定理 `mem_sSup_of_directedOn`

English:
theorem mem_sSup_of_directedOn
  statement: {S : Set (L.Substructure M)} (Sne : S.Nonempty)
  proof: by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, Subtype.exists, exists_prop]

中文:
定理 mem_sSup_of_directedOn
  结论: {S : 集合 (L.子结构 M)} (Sne : S.非空)
  证明: by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, Subtype.exists, exists_prop]

Depends on / 依赖: Nonempty, Sne.to_subtype, Subtype, Subtype.exists, directed_val, exists_prop, hS.directed_val, mem_iSup_of_directed, sSup_eq_iSup, to_subtype
-/
theorem mem_sSup_of_directedOn {S : Set (L.Substructure M)} (Sne : S.Nonempty)
    (hS : DirectedOn (· <= ·) S) {x : M} :
    x in sSup S ↔ exists s in S, x in s := by
  have : Nonempty S := Sne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, Subtype.exists, exists_prop]

variable (L) (M)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: L.Constants] : IsEmpty (⊥
  body: by
  refine (isEmpty_subtype _).2 (fun x => ?_)
  have h : (∅ : Set M) in (closure L).closed := by
    rw [mem_closed_iff]
    intro n f
    cases n
    · exact isEmptyElim f
    · intro x hx
      simp only [mem_empty_iff_false, forall_const] at hx
  rw [← closure_empty]; rw [← SetLike.mem_coe]; rw [h]
  exact Set.notMem_empty _

中文:
实例 [是空
  签名: L.Constants] : 是空 (⊥
  定义体: by
  refine (isEmpty_subtype _).2 (fun x => ?_)
  have h : (∅ : Set M) in (closure L).closed := by
    rw [mem_closed_iff]
    intro n f
    cases n
    · exact isEmptyElim f
    · intro x hx
      simp only [mem_empty_iff_false, forall_const] at hx
  rw [← closure_empty]; rw [← SetLike.mem_coe]; rw [h]
  exact Set.notMem_empty _

Depends on / 依赖: Set.notMem_empty, SetLike, SetLike.mem_coe, closed, closure, closure_empty, forall_const, isEmptyElim, isEmpty_subtype, mem_closed_iff, mem_coe, mem_empty_iff_false, notMem_empty
-/
instance [IsEmpty L.Constants] : IsEmpty (⊥ : L.Substructure M) := by
  refine (isEmpty_subtype _).2 (fun x => ?_)
  have h : (∅ : Set M) in (closure L).closed := by
    rw [mem_closed_iff]
    intro n f
    cases n
    · exact isEmptyElim f
    · intro x hx
      simp only [mem_empty_iff_false, forall_const] at hx
  rw [← closure_empty]; rw [← SetLike.mem_coe]; rw [h]
  exact Set.notMem_empty _

variable {L} {M}

/-!
### `comap` and `map`
-/


/-- The preimage of a substructure along a homomorphism is a substructure. -/
@[simps]
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (φ : M ->[L] N) (S : L.Substructure N)
  body: φ ⁻¹' S
  fun_mem {n} f x hx := by
    rw [mem_preimage]; rw [φ.map_fun]
    exact S.fun_mem f (φ ∘ x) hx

@[simp]

中文:
定义 comap
  签名: (φ : M ->[L] N) (S : L.子结构 N)
  定义体: φ ⁻¹' S
  fun_mem {n} f x hx := by
    rw [mem_preimage]; rw [φ.map_fun]
    exact S.fun_mem f (φ ∘ x) hx

@[simp]
-/
def comap (φ : M ->[L] N) (S : L.Substructure N) : L.Substructure M where
  carrier := φ ⁻¹' S
  fun_mem {n} f x hx := by
    rw [mem_preimage]; rw [φ.map_fun]
    exact S.fun_mem f (φ ∘ x) hx

@[simp]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: {S : L.Substructure N} {f : M ->[L] N} {x : M}
  statement: x in S.comap f ↔ f x in S
  proof: Iff.rfl

中文:
定理 mem_comap
  条件: {S : L.子结构 N} {f : M ->[L] N} {x : M}
  结论: x in S.comap f ↔ f x in S
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_comap {S : L.Substructure N} {f : M ->[L] N} {x : M} : x in S.comap f ↔ f x in S :=
  Iff.rfl

/--
theorem `comap_comap` / 定理 `comap_comap`

English:
theorem comap_comap
  given: (S : L.Substructure P) (g : N ->[L] P) (f : M ->[L] N)
  proof: rfl

@[simp]

中文:
定理 comap_comap
  条件: (S : L.子结构 P) (g : N ->[L] P) (f : M ->[L] N)
  证明: rfl

@[simp]
-/
theorem comap_comap (S : L.Substructure P) (g : N ->[L] P) (f : M ->[L] N) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  rfl

@[simp]
/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  given: (S : L.Substructure P)
  statement: S.comap (Hom.id _ _) = S
  proof: ext (by simp)

中文:
定理 comap_id
  条件: (S : L.子结构 P)
  结论: S.comap (态射.id _ _) = S
  证明: ext (by simp)
-/
theorem comap_id (S : L.Substructure P) : S.comap (Hom.id _ _) = S :=
  ext (by simp)

/-- The image of a substructure along a homomorphism is a substructure. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (φ : M ->[L] N) (S : L.Substructure M)
  body: φ '' S
  fun_mem {n} f x hx :=
    (mem_image _ _ _).1
      ⟨funMap f fun i => Classical.choose (hx i),
        S.fun_mem f _ fun i => (Classical.choose_spec (hx i)).1, by
        simp only [Hom.map_fun, SetLike.mem_coe]
        exact congr rfl (funext fun i => (Classical.choose_spec (hx i)).2)⟩

@[simp]

中文:
定义 map
  签名: (φ : M ->[L] N) (S : L.子结构 M)
  定义体: φ '' S
  fun_mem {n} f x hx :=
    (mem_image _ _ _).1
      ⟨funMap f fun i => Classical.choose (hx i),
        S.fun_mem f _ fun i => (Classical.choose_spec (hx i)).1, by
        simp only [Hom.map_fun, SetLike.mem_coe]
        exact congr rfl (funext fun i => (Classical.choose_spec (hx i)).2)⟩

@[simp]
-/
def map (φ : M ->[L] N) (S : L.Substructure M) : L.Substructure N where
  carrier := φ '' S
  fun_mem {n} f x hx :=
    (mem_image _ _ _).1
      ⟨funMap f fun i => Classical.choose (hx i),
        S.fun_mem f _ fun i => (Classical.choose_spec (hx i)).1, by
        simp only [Hom.map_fun, SetLike.mem_coe]
        exact congr rfl (funext fun i => (Classical.choose_spec (hx i)).2)⟩

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {f : M ->[L] N} {S : L.Substructure M} {y : N}
  proof: Iff.rfl

中文:
定理 mem_map
  条件: {f : M ->[L] N} {S : L.子结构 M} {y : N}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_map {f : M ->[L] N} {S : L.Substructure M} {y : N} :
    y in S.map f ↔ exists x in S, f x = y :=
  Iff.rfl

/--
theorem `mem_map_of_mem` / 定理 `mem_map_of_mem`

English:
theorem mem_map_of_mem
  given: (f : M ->[L] N) {S : L.Substructure M} {x : M} (hx : x in S)
  statement: f x in S.map f
  proof: mem_image_of_mem f hx

中文:
定理 mem_map_of_mem
  条件: (f : M ->[L] N) {S : L.子结构 M} {x : M} (hx : x in S)
  结论: f x in S.map f
  证明: mem_image_of_mem f hx

Depends on / 依赖: mem_image_of_mem
-/
theorem mem_map_of_mem (f : M ->[L] N) {S : L.Substructure M} {x : M} (hx : x in S) : f x in S.map f :=
  mem_image_of_mem f hx

/--
theorem `apply_coe_mem_map` / 定理 `apply_coe_mem_map`

English:
theorem apply_coe_mem_map
  given: (f : M ->[L] N) (S : L.Substructure M) (x : S)
  statement: f x in S.map f
  proof: mem_map_of_mem f x.prop

中文:
定理 apply_coe_mem_map
  条件: (f : M ->[L] N) (S : L.子结构 M) (x : S)
  结论: f x in S.map f
  证明: mem_map_of_mem f x.prop

Depends on / 依赖: mem_map_of_mem, x.prop
-/
theorem apply_coe_mem_map (f : M ->[L] N) (S : L.Substructure M) (x : S) : f x in S.map f :=
  mem_map_of_mem f x.prop

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (g : N ->[L] P) (f : M ->[L] N)
  statement: (S.map f).map g = S.map (g.comp f)
  proof: SetLike.coe_injective image_image _ _ _

中文:
定理 map_map
  条件: (g : N ->[L] P) (f : M ->[L] N)
  结论: (S.map f).map g = S.map (g.comp f)
  证明: SetLike.coe_injective image_image _ _ _

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, image_image
-/
theorem map_map (g : N ->[L] P) (f : M ->[L] N) : (S.map f).map g = S.map (g.comp f) :=
SetLike.coe_injective image_image _ _ _

/--
theorem `map_le_iff_le_comap` / 定理 `map_le_iff_le_comap`

English:
theorem map_le_iff_le_comap
  given: {f : M ->[L] N} {S : L.Substructure M} {T : L.Substructure N}
  proof: image_subset_iff

中文:
定理 map_le_iff_le_comap
  条件: {f : M ->[L] N} {S : L.子结构 M} {T : L.子结构 N}
  证明: image_subset_iff

Depends on / 依赖: image_subset_iff
-/
theorem map_le_iff_le_comap {f : M ->[L] N} {S : L.Substructure M} {T : L.Substructure N} :
    S.map f <= T ↔ S <= T.comap f :=
  image_subset_iff

/--
theorem `gc_map_comap` / 定理 `gc_map_comap`

English:
theorem gc_map_comap
  given: (f : M ->[L] N)
  statement: GaloisConnection (map f) (comap f)
  proof: fun _ _ =>
  map_le_iff_le_comap

中文:
定理 gc_map_comap
  条件: (f : M ->[L] N)
  结论: GaloisConnection (map f) (comap f)
  证明: fun _ _ =>
  map_le_iff_le_comap
-/
theorem gc_map_comap (f : M ->[L] N) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap

/--
theorem `map_le_of_le_comap` / 定理 `map_le_of_le_comap`

English:
theorem map_le_of_le_comap
  given: {T : L.Substructure N} {f : M ->[L] N}
  statement: S <= T.comap f -> S.map f <= T
  proof: (gc_map_comap f).l_le

中文:
定理 map_le_of_le_comap
  条件: {T : L.子结构 N} {f : M ->[L] N}
  结论: S <= T.comap f -> S.map f <= T
  证明: (gc_map_comap f).l_le

Depends on / 依赖: gc_map_comap, l_le
-/
theorem map_le_of_le_comap {T : L.Substructure N} {f : M ->[L] N} : S <= T.comap f -> S.map f <= T :=
  (gc_map_comap f).l_le

/--
theorem `le_comap_of_map_le` / 定理 `le_comap_of_map_le`

English:
theorem le_comap_of_map_le
  given: {T : L.Substructure N} {f : M ->[L] N}
  statement: S.map f <= T -> S <= T.comap f
  proof: (gc_map_comap f).le_u

中文:
定理 le_comap_of_map_le
  条件: {T : L.子结构 N} {f : M ->[L] N}
  结论: S.map f <= T -> S <= T.comap f
  证明: (gc_map_comap f).le_u

Depends on / 依赖: gc_map_comap, le_u
-/
theorem le_comap_of_map_le {T : L.Substructure N} {f : M ->[L] N} : S.map f <= T -> S <= T.comap f :=
  (gc_map_comap f).le_u

/--
theorem `le_comap_map` / 定理 `le_comap_map`

English:
theorem le_comap_map
  given: {f : M ->[L] N}
  statement: S <= (S.map f).comap f
  proof: (gc_map_comap f).le_u_l _

中文:
定理 le_comap_map
  条件: {f : M ->[L] N}
  结论: S <= (S.map f).comap f
  证明: (gc_map_comap f).le_u_l _

Depends on / 依赖: gc_map_comap, le_u_l
-/
theorem le_comap_map {f : M ->[L] N} : S <= (S.map f).comap f :=
  (gc_map_comap f).le_u_l _

/--
theorem `map_comap_le` / 定理 `map_comap_le`

English:
theorem map_comap_le
  given: {S : L.Substructure N} {f : M ->[L] N}
  statement: (S.comap f).map f <= S
  proof: (gc_map_comap f).l_u_le _

中文:
定理 map_comap_le
  条件: {S : L.子结构 N} {f : M ->[L] N}
  结论: (S.comap f).map f <= S
  证明: (gc_map_comap f).l_u_le _

Depends on / 依赖: gc_map_comap, l_u_le
-/
theorem map_comap_le {S : L.Substructure N} {f : M ->[L] N} : (S.comap f).map f <= S :=
  (gc_map_comap f).l_u_le _

/--
theorem `monotone_map` / 定理 `monotone_map`

English:
theorem monotone_map
  given: {f : M ->[L] N}
  statement: Monotone (map f)
  proof: (gc_map_comap f).monotone_l

中文:
定理 monotone_map
  条件: {f : M ->[L] N}
  结论: 递增 (map f)
  证明: (gc_map_comap f).monotone_l

Depends on / 依赖: gc_map_comap, monotone_l
-/
theorem monotone_map {f : M ->[L] N} : Monotone (map f) :=
  (gc_map_comap f).monotone_l

/--
theorem `monotone_comap` / 定理 `monotone_comap`

English:
theorem monotone_comap
  given: {f : M ->[L] N}
  statement: Monotone (comap f)
  proof: (gc_map_comap f).monotone_u

@[simp]

中文:
定理 monotone_comap
  条件: {f : M ->[L] N}
  结论: 递增 (comap f)
  证明: (gc_map_comap f).monotone_u

@[simp]

Depends on / 依赖: gc_map_comap, monotone_u
-/
theorem monotone_comap {f : M ->[L] N} : Monotone (comap f) :=
  (gc_map_comap f).monotone_u

@[simp]
/--
theorem `map_comap_map` / 定理 `map_comap_map`

English:
theorem map_comap_map
  given: {f : M ->[L] N}
  statement: ((S.map f).comap f).map f = S.map f
  proof: (gc_map_comap f).l_u_l_eq_l _

@[simp]

中文:
定理 map_comap_map
  条件: {f : M ->[L] N}
  结论: ((S.map f).comap f).map f = S.map f
  证明: (gc_map_comap f).l_u_l_eq_l _

@[simp]

Depends on / 依赖: gc_map_comap, l_u_l_eq_l
-/
theorem map_comap_map {f : M ->[L] N} : ((S.map f).comap f).map f = S.map f :=
  (gc_map_comap f).l_u_l_eq_l _

@[simp]
/--
theorem `comap_map_comap` / 定理 `comap_map_comap`

English:
theorem comap_map_comap
  given: {S : L.Substructure N} {f : M ->[L] N}
  proof: (gc_map_comap f).u_l_u_eq_u _

中文:
定理 comap_map_comap
  条件: {S : L.子结构 N} {f : M ->[L] N}
  证明: (gc_map_comap f).u_l_u_eq_u _

Depends on / 依赖: gc_map_comap, u_l_u_eq_u
-/
theorem comap_map_comap {S : L.Substructure N} {f : M ->[L] N} :
    ((S.comap f).map f).comap f = S.comap f :=
  (gc_map_comap f).u_l_u_eq_u _

/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  given: (S T : L.Substructure M) (f : M ->[L] N)
  statement: (S ⊔ T).map f = S.map f ⊔ T.map f
  proof: (gc_map_comap f).l_sup

中文:
定理 map_sup
  条件: (S T : L.子结构 M) (f : M ->[L] N)
  结论: (S ⊔ T).map f = S.map f ⊔ T.map f
  证明: (gc_map_comap f).l_sup

Depends on / 依赖: gc_map_comap, l_sup
-/
theorem map_sup (S T : L.Substructure M) (f : M ->[L] N) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
  (gc_map_comap f).l_sup

/--
theorem `map_iSup` / 定理 `map_iSup`

English:
theorem map_iSup
  given: {ι : Sort*} (f : M ->[L] N) (s : ι -> L.Substructure M)
  proof: (gc_map_comap f).l_iSup

中文:
定理 map_iSup
  条件: {ι : 类型层*} (f : M ->[L] N) (s : ι -> L.子结构 M)
  证明: (gc_map_comap f).l_iSup

Depends on / 依赖: gc_map_comap, l_iSup
-/
theorem map_iSup {ι : Sort*} (f : M ->[L] N) (s : ι -> L.Substructure M) :
    (⨆ i, s i).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup

/--
theorem `comap_inf` / 定理 `comap_inf`

English:
theorem comap_inf
  given: (S T : L.Substructure N) (f : M ->[L] N)
  proof: (gc_map_comap f).u_inf

中文:
定理 comap_inf
  条件: (S T : L.子结构 N) (f : M ->[L] N)
  证明: (gc_map_comap f).u_inf

Depends on / 依赖: gc_map_comap, u_inf
-/
theorem comap_inf (S T : L.Substructure N) (f : M ->[L] N) :
    (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
  (gc_map_comap f).u_inf

/--
theorem `comap_iInf` / 定理 `comap_iInf`

English:
theorem comap_iInf
  given: {ι : Sort*} (f : M ->[L] N) (s : ι -> L.Substructure N)
  proof: (gc_map_comap f).u_iInf

@[simp]

中文:
定理 comap_iInf
  条件: {ι : 类型层*} (f : M ->[L] N) (s : ι -> L.子结构 N)
  证明: (gc_map_comap f).u_iInf

@[simp]

Depends on / 依赖: gc_map_comap, u_iInf
-/
theorem comap_iInf {ι : Sort*} (f : M ->[L] N) (s : ι -> L.Substructure N) :
    (⨅ i, s i).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[simp]
/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  given: (f : M ->[L] N)
  statement: (⊥ : L.Substructure M).map f = ⊥
  proof: (gc_map_comap f).l_bot

@[simp]

中文:
定理 map_bot
  条件: (f : M ->[L] N)
  结论: (⊥ : L.子结构 M).map f = ⊥
  证明: (gc_map_comap f).l_bot

@[simp]

Depends on / 依赖: gc_map_comap, l_bot
-/
theorem map_bot (f : M ->[L] N) : (⊥ : L.Substructure M).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
/--
theorem `comap_top` / 定理 `comap_top`

English:
theorem comap_top
  given: (f : M ->[L] N)
  statement: (⊤ : L.Substructure N).comap f = ⊤
  proof: (gc_map_comap f).u_top

@[simp]

中文:
定理 comap_top
  条件: (f : M ->[L] N)
  结论: (⊤ : L.子结构 N).comap f = ⊤
  证明: (gc_map_comap f).u_top

@[simp]

Depends on / 依赖: gc_map_comap, u_top
-/
theorem comap_top (f : M ->[L] N) : (⊤ : L.Substructure N).comap f = ⊤ :=
  (gc_map_comap f).u_top

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (S : L.Substructure M)
  statement: S.map (Hom.id L M) = S
  proof: SetLike.coe_injective Set.image_id _

中文:
定理 map_id
  条件: (S : L.子结构 M)
  结论: S.map (态射.id L M) = S
  证明: SetLike.coe_injective Set.image_id _

Depends on / 依赖: Set.image_id, SetLike, SetLike.coe_injective, coe_injective, image_id
-/
theorem map_id (S : L.Substructure M) : S.map (Hom.id L M) = S :=
SetLike.coe_injective Set.image_id _

/--
theorem `map_closure` / 定理 `map_closure`

English:
theorem map_closure
  given: (f : M ->[L] N) (s : Set M)
  statement: (closure L s).map f = closure L (f '' s)
  proof: Eq.symm
closure_eq_of_le (Set.image_mono subset_closure)
map_le_iff_le_comap.2 closure_le.2 fun x hx => subset_closure ⟨x, hx, rfl⟩

@[simp]

中文:
定理 map_closure
  条件: (f : M ->[L] N) (s : 集合 M)
  结论: (closure L s).map f = closure L (f '' s)
  证明: Eq.symm
closure_eq_of_le (Set.image_mono subset_closure)
map_le_iff_le_comap.2 closure_le.2 fun x hx => subset_closure ⟨x, hx, rfl⟩

@[simp]

Depends on / 依赖: Eq.symm, Set.image_mono, closure_eq_of_le, closure_le, image_mono, map_le_iff_le_comap, subset_closure
-/
theorem map_closure (f : M ->[L] N) (s : Set M) : (closure L s).map f = closure L (f '' s) :=
Eq.symm
closure_eq_of_le (Set.image_mono subset_closure)
map_le_iff_le_comap.2 closure_le.2 fun x hx => subset_closure ⟨x, hx, rfl⟩

@[simp]
/--
theorem `closure_image` / 定理 `closure_image`

English:
theorem closure_image
  given: (f : M ->[L] N)
  statement: closure L (f '' s) = map f (closure L s)
  proof: (map_closure f s).symm

中文:
定理 closure_image
  条件: (f : M ->[L] N)
  结论: closure L (f '' s) = map f (closure L s)
  证明: (map_closure f s).symm

Depends on / 依赖: map_closure
-/
theorem closure_image (f : M ->[L] N) : closure L (f '' s) = map f (closure L s) :=
  (map_closure f s).symm

section GaloisCoinsertion

variable {ι : Type*} {f : M ->[L] N}

/--
Definition of `gciMapComap` / `gciMapComap` 的定义

English:
definition gciMapComap
  signature: (hf : Function.Injective f)
  body: (gc_map_comap f).toGaloisCoinsertion fun S x => by simp [mem_comap, mem_map, hf.eq_iff]

中文:
定义 gciMapComap
  签名: (hf : 函数.单射 f)
  定义体: (gc_map_comap f).toGaloisCoinsertion fun S x => by simp [mem_comap, mem_map, hf.eq_iff]

Depends on / 依赖: eq_iff, gc_map_comap, hf.eq_iff, mem_comap, mem_map, toGaloisCoinsertion
-/
def gciMapComap (hf : Function.Injective f) : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by simp [mem_comap, mem_map, hf.eq_iff]

variable (hf : Function.Injective f)
include hf

/--
theorem `comap_map_eq_of_injective` / 定理 `comap_map_eq_of_injective`

English:
theorem comap_map_eq_of_injective
  given: (S : L.Substructure M)
  statement: (S.map f).comap f = S
  proof: (gciMapComap hf).u_l_eq _

中文:
定理 comap_map_eq_of_injective
  条件: (S : L.子结构 M)
  结论: (S.map f).comap f = S
  证明: (gciMapComap hf).u_l_eq _

Depends on / 依赖: gciMapComap, u_l_eq
-/
theorem comap_map_eq_of_injective (S : L.Substructure M) : (S.map f).comap f = S :=
  (gciMapComap hf).u_l_eq _

/--
theorem `comap_surjective_of_injective` / 定理 `comap_surjective_of_injective`

English:
theorem comap_surjective_of_injective
  statement: Function.Surjective (comap f)
  proof: (gciMapComap hf).u_surjective

中文:
定理 comap_surjective_of_injective
  结论: 函数.满射 (comap f)
  证明: (gciMapComap hf).u_surjective

Depends on / 依赖: gciMapComap, u_surjective
-/
theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gciMapComap hf).u_surjective

/--
theorem `map_injective_of_injective` / 定理 `map_injective_of_injective`

English:
theorem map_injective_of_injective
  statement: Function.Injective (map f)
  proof: (gciMapComap hf).l_injective

中文:
定理 map_injective_of_injective
  结论: 函数.单射 (map f)
  证明: (gciMapComap hf).l_injective

Depends on / 依赖: gciMapComap, l_injective
-/
theorem map_injective_of_injective : Function.Injective (map f) :=
  (gciMapComap hf).l_injective

/--
theorem `comap_inf_map_of_injective` / 定理 `comap_inf_map_of_injective`

English:
theorem comap_inf_map_of_injective
  given: (S T : L.Substructure M)
  statement: (S.map f ⊓ T.map f).comap f = S ⊓ T
  proof: (gciMapComap hf).u_inf_l _ _

中文:
定理 comap_inf_map_of_injective
  条件: (S T : L.子结构 M)
  结论: (S.map f ⊓ T.map f).comap f = S ⊓ T
  证明: (gciMapComap hf).u_inf_l _ _

Depends on / 依赖: gciMapComap, u_inf_l
-/
theorem comap_inf_map_of_injective (S T : L.Substructure M) : (S.map f ⊓ T.map f).comap f = S ⊓ T :=
  (gciMapComap hf).u_inf_l _ _

/--
theorem `comap_iInf_map_of_injective` / 定理 `comap_iInf_map_of_injective`

English:
theorem comap_iInf_map_of_injective
  given: (S : ι -> L.Substructure M)
  proof: (gciMapComap hf).u_iInf_l _

中文:
定理 comap_iInf_map_of_injective
  条件: (S : ι -> L.子结构 M)
  证明: (gciMapComap hf).u_iInf_l _

Depends on / 依赖: gciMapComap, u_iInf_l
-/
theorem comap_iInf_map_of_injective (S : ι -> L.Substructure M) :
    (⨅ i, (S i).map f).comap f = ⨅ i, S i :=
  (gciMapComap hf).u_iInf_l _

/--
theorem `comap_sup_map_of_injective` / 定理 `comap_sup_map_of_injective`

English:
theorem comap_sup_map_of_injective
  given: (S T : L.Substructure M)
  statement: (S.map f ⊔ T.map f).comap f = S ⊔ T
  proof: (gciMapComap hf).u_sup_l _ _

中文:
定理 comap_sup_map_of_injective
  条件: (S T : L.子结构 M)
  结论: (S.map f ⊔ T.map f).comap f = S ⊔ T
  证明: (gciMapComap hf).u_sup_l _ _

Depends on / 依赖: gciMapComap, u_sup_l
-/
theorem comap_sup_map_of_injective (S T : L.Substructure M) : (S.map f ⊔ T.map f).comap f = S ⊔ T :=
  (gciMapComap hf).u_sup_l _ _

/--
theorem `comap_iSup_map_of_injective` / 定理 `comap_iSup_map_of_injective`

English:
theorem comap_iSup_map_of_injective
  given: (S : ι -> L.Substructure M)
  proof: (gciMapComap hf).u_iSup_l _

中文:
定理 comap_iSup_map_of_injective
  条件: (S : ι -> L.子结构 M)
  证明: (gciMapComap hf).u_iSup_l _

Depends on / 依赖: gciMapComap, u_iSup_l
-/
theorem comap_iSup_map_of_injective (S : ι -> L.Substructure M) :
    (⨆ i, (S i).map f).comap f = ⨆ i, S i :=
  (gciMapComap hf).u_iSup_l _

/--
theorem `map_le_map_iff_of_injective` / 定理 `map_le_map_iff_of_injective`

English:
theorem map_le_map_iff_of_injective
  given: {S T : L.Substructure M}
  statement: S.map f <= T.map f ↔ S <= T
  proof: (gciMapComap hf).l_le_l_iff

中文:
定理 map_le_map_iff_of_injective
  条件: {S T : L.子结构 M}
  结论: S.map f <= T.map f ↔ S <= T
  证明: (gciMapComap hf).l_le_l_iff

Depends on / 依赖: gciMapComap, l_le_l_iff
-/
theorem map_le_map_iff_of_injective {S T : L.Substructure M} : S.map f <= T.map f ↔ S <= T :=
  (gciMapComap hf).l_le_l_iff

/--
theorem `map_strictMono_of_injective` / 定理 `map_strictMono_of_injective`

English:
theorem map_strictMono_of_injective
  statement: StrictMono (map f)
  proof: (gciMapComap hf).strictMono_l

中文:
定理 map_strictMono_of_injective
  结论: 严格递增 (map f)
  证明: (gciMapComap hf).strictMono_l

Depends on / 依赖: gciMapComap, strictMono_l
-/
theorem map_strictMono_of_injective : StrictMono (map f) :=
  (gciMapComap hf).strictMono_l

end GaloisCoinsertion

section GaloisInsertion

variable {ι : Type*} {f : M ->[L] N} (hf : Function.Surjective f)
include hf

/--
Definition of `giMapComap` / `giMapComap` 的定义

English:
definition giMapComap
  signature: : GaloisInsertion (map f) (comap f)
  body: (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2 ⟨y, by simp [hy, h]⟩

中文:
定义 giMapComap
  签名: : Galois嵌入 (map f) (comap f)
  定义体: (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2 ⟨y, by simp [hy, h]⟩

Depends on / 依赖: gc_map_comap, mem_map, toGaloisInsertion
-/
def giMapComap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2 ⟨y, by simp [hy, h]⟩

/--
theorem `map_comap_eq_of_surjective` / 定理 `map_comap_eq_of_surjective`

English:
theorem map_comap_eq_of_surjective
  given: (S : L.Substructure N)
  statement: (S.comap f).map f = S
  proof: (giMapComap hf).l_u_eq _

中文:
定理 map_comap_eq_of_surjective
  条件: (S : L.子结构 N)
  结论: (S.comap f).map f = S
  证明: (giMapComap hf).l_u_eq _

Depends on / 依赖: giMapComap, l_u_eq
-/
theorem map_comap_eq_of_surjective (S : L.Substructure N) : (S.comap f).map f = S :=
  (giMapComap hf).l_u_eq _

/--
theorem `map_surjective_of_surjective` / 定理 `map_surjective_of_surjective`

English:
theorem map_surjective_of_surjective
  statement: Function.Surjective (map f)
  proof: (giMapComap hf).l_surjective

中文:
定理 map_surjective_of_surjective
  结论: 函数.满射 (map f)
  证明: (giMapComap hf).l_surjective

Depends on / 依赖: giMapComap, l_surjective
-/
theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (giMapComap hf).l_surjective

/--
theorem `comap_injective_of_surjective` / 定理 `comap_injective_of_surjective`

English:
theorem comap_injective_of_surjective
  statement: Function.Injective (comap f)
  proof: (giMapComap hf).u_injective

中文:
定理 comap_injective_of_surjective
  结论: 函数.单射 (comap f)
  证明: (giMapComap hf).u_injective

Depends on / 依赖: giMapComap, u_injective
-/
theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (giMapComap hf).u_injective

/--
theorem `map_inf_comap_of_surjective` / 定理 `map_inf_comap_of_surjective`

English:
theorem map_inf_comap_of_surjective
  given: (S T : L.Substructure N)
  proof: (giMapComap hf).l_inf_u _ _

中文:
定理 map_inf_comap_of_surjective
  条件: (S T : L.子结构 N)
  证明: (giMapComap hf).l_inf_u _ _

Depends on / 依赖: giMapComap, l_inf_u
-/
theorem map_inf_comap_of_surjective (S T : L.Substructure N) :
    (S.comap f ⊓ T.comap f).map f = S ⊓ T :=
  (giMapComap hf).l_inf_u _ _

/--
theorem `map_iInf_comap_of_surjective` / 定理 `map_iInf_comap_of_surjective`

English:
theorem map_iInf_comap_of_surjective
  given: (S : ι -> L.Substructure N)
  proof: (giMapComap hf).l_iInf_u _

中文:
定理 map_iInf_comap_of_surjective
  条件: (S : ι -> L.子结构 N)
  证明: (giMapComap hf).l_iInf_u _

Depends on / 依赖: giMapComap, l_iInf_u
-/
theorem map_iInf_comap_of_surjective (S : ι -> L.Substructure N) :
    (⨅ i, (S i).comap f).map f = ⨅ i, S i :=
  (giMapComap hf).l_iInf_u _

/--
theorem `map_sup_comap_of_surjective` / 定理 `map_sup_comap_of_surjective`

English:
theorem map_sup_comap_of_surjective
  given: (S T : L.Substructure N)
  proof: (giMapComap hf).l_sup_u _ _

中文:
定理 map_sup_comap_of_surjective
  条件: (S T : L.子结构 N)
  证明: (giMapComap hf).l_sup_u _ _

Depends on / 依赖: giMapComap, l_sup_u
-/
theorem map_sup_comap_of_surjective (S T : L.Substructure N) :
    (S.comap f ⊔ T.comap f).map f = S ⊔ T :=
  (giMapComap hf).l_sup_u _ _

/--
theorem `map_iSup_comap_of_surjective` / 定理 `map_iSup_comap_of_surjective`

English:
theorem map_iSup_comap_of_surjective
  given: (S : ι -> L.Substructure N)
  proof: (giMapComap hf).l_iSup_u _

中文:
定理 map_iSup_comap_of_surjective
  条件: (S : ι -> L.子结构 N)
  证明: (giMapComap hf).l_iSup_u _

Depends on / 依赖: giMapComap, l_iSup_u
-/
theorem map_iSup_comap_of_surjective (S : ι -> L.Substructure N) :
    (⨆ i, (S i).comap f).map f = ⨆ i, S i :=
  (giMapComap hf).l_iSup_u _

/--
theorem `comap_le_comap_iff_of_surjective` / 定理 `comap_le_comap_iff_of_surjective`

English:
theorem comap_le_comap_iff_of_surjective
  given: {S T : L.Substructure N}
  statement: S.comap f <= T.comap f ↔ S <= T
  proof: (giMapComap hf).u_le_u_iff

中文:
定理 comap_le_comap_iff_of_surjective
  条件: {S T : L.子结构 N}
  结论: S.comap f <= T.comap f ↔ S <= T
  证明: (giMapComap hf).u_le_u_iff

Depends on / 依赖: giMapComap, u_le_u_iff
-/
theorem comap_le_comap_iff_of_surjective {S T : L.Substructure N} : S.comap f <= T.comap f ↔ S <= T :=
  (giMapComap hf).u_le_u_iff

/--
theorem `comap_strictMono_of_surjective` / 定理 `comap_strictMono_of_surjective`

English:
theorem comap_strictMono_of_surjective
  statement: StrictMono (comap f)
  proof: (giMapComap hf).strictMono_u

中文:
定理 comap_strictMono_of_surjective
  结论: 严格递增 (comap f)
  证明: (giMapComap hf).strictMono_u

Depends on / 依赖: giMapComap, strictMono_u
-/
theorem comap_strictMono_of_surjective : StrictMono (comap f) :=
  (giMapComap hf).strictMono_u

end GaloisInsertion

/--
Instance `inducedStructure` / 实例 `inducedStructure`

English:
instance inducedStructure
  signature: {S : L.Substructure M}
  body: ⟨funMap f fun i => x i, S.fun_mem f (fun i => x i) fun i => (x i).2⟩
  RelMap {_} r x := RelMap r fun i => (x i : M)

中文:
实例 inducedStructure
  签名: {S : L.子结构 M}
  定义体: ⟨funMap f fun i => x i, S.fun_mem f (fun i => x i) fun i => (x i).2⟩
  RelMap {_} r x := RelMap r fun i => (x i : M)

Depends on / 依赖: S.fun_mem, funMap, fun_mem
-/
instance inducedStructure {S : L.Substructure M} : L.Structure S where
  funMap {_} f x := ⟨funMap f fun i => x i, S.fun_mem f (fun i => x i) fun i => (x i).2⟩
  RelMap {_} r x := RelMap r fun i => (x i : M)

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: (S : L.Substructure M)
  body: (↑)
  inj' := Subtype.coe_injective

@[simp]

中文:
定义 subtype
  签名: (S : L.子结构 M)
  定义体: (↑)
  inj' := Subtype.coe_injective

@[simp]
-/
def subtype (S : L.Substructure M) : S ↪[L] M where
  toFun := (↑)
  inj' := Subtype.coe_injective

@[simp]
/--
theorem `subtype_apply` / 定理 `subtype_apply`

English:
theorem subtype_apply
  given: {S : L.Substructure M} {x : S}
  statement: subtype S x = x
  proof: rfl

中文:
定理 subtype_apply
  条件: {S : L.子结构 M} {x : S}
  结论: subtype S x = x
  证明: rfl
-/
theorem subtype_apply {S : L.Substructure M} {x : S} : subtype S x = x :=
  rfl

/--
theorem `subtype_injective` / 定理 `subtype_injective`

English:
theorem subtype_injective
  given: (S : L.Substructure M)
  statement: Function.Injective (subtype S)
  proof: Subtype.coe_injective

@[simp]

中文:
定理 subtype_injective
  条件: (S : L.子结构 M)
  结论: 函数.单射 (subtype S)
  证明: Subtype.coe_injective

@[simp]

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
theorem subtype_injective (S : L.Substructure M) : Function.Injective (subtype S) :=
  Subtype.coe_injective

@[simp]
/--
theorem `coe_subtype` / 定理 `coe_subtype`

English:
theorem coe_subtype
  statement: ⇑S.subtype = ((↑) : S -> M)
  proof: rfl

中文:
定理 coe_subtype
  结论: ⇑S.subtype = ((↑) : S -> M)
  证明: rfl
-/
theorem coe_subtype : ⇑S.subtype = ((↑) : S -> M) :=
  rfl

/--
Definition of `topEquiv` / `topEquiv` 的定义

English:
definition topEquiv
  signature: : (⊤ : L.Substructure M) ≃[L] M where
  body: subtype ⊤
  invFun m := ⟨m, mem_top m⟩
  left_inv m := by simp

@[simp]

中文:
定义 topEquiv
  签名: : (⊤ : L.子结构 M) ≃[L] M where
  定义体: subtype ⊤
  invFun m := ⟨m, mem_top m⟩
  left_inv m := by simp

@[simp]

Depends on / 依赖: subtype
-/
def topEquiv : (⊤ : L.Substructure M) ≃[L] M where
  toFun := subtype ⊤
  invFun m := ⟨m, mem_top m⟩
  left_inv m := by simp

@[simp]
/--
theorem `coe_topEquiv` / 定理 `coe_topEquiv`

English:
theorem coe_topEquiv
  proof: rfl

@[simp]

中文:
定理 coe_topEquiv
  证明: rfl

@[simp]
-/
theorem coe_topEquiv :
    ⇑(topEquiv : (⊤ : L.Substructure M) ≃[L] M) = ((↑) : (⊤ : L.Substructure M) -> M) :=
  rfl

@[simp]
/--
theorem `realize_boundedFormula_top` / 定理 `realize_boundedFormula_top`

English:
theorem realize_boundedFormula_top
  statement: {α : Type*} {n : Nat} {φ : L.BoundedFormula α n}
  proof: by
  rw [← StrongHomClass.realize_boundedFormula Substructure.topEquiv φ]
  simp

@[simp]

中文:
定理 realize_boundedFormula_top
  结论: {α : 类型} {n : 自然数} {φ : L.BoundedFormula α n}
  证明: by
  rw [← StrongHomClass.realize_boundedFormula Substructure.topEquiv φ]
  simp

@[simp]

Depends on / 依赖: StrongHomClass, StrongHomClass.realize_boundedFormula, Substructure, Substructure.topEquiv, realize_boundedFormula, topEquiv
-/
theorem realize_boundedFormula_top {α : Type*} {n : Nat} {φ : L.BoundedFormula α n}
    {v : α -> (⊤ : L.Substructure M)} {xs : Fin n -> (⊤ : L.Substructure M)} :
    φ.Realize v xs ↔ φ.Realize (((↑) : _ -> M) ∘ v) ((↑) ∘ xs) := by
  rw [← StrongHomClass.realize_boundedFormula Substructure.topEquiv φ]
  simp

@[simp]
/--
theorem `realize_formula_top` / 定理 `realize_formula_top`

English:
theorem realize_formula_top
  given: {α : Type*} {φ : L.Formula α} {v : α -> (⊤ : L.Substructure M)}
  proof: by
  rw [← StrongHomClass.realize_formula Substructure.topEquiv φ]
  simp

中文:
定理 realize_formula_top
  条件: {α : 类型} {φ : L.公式 α} {v : α -> (⊤ : L.子结构 M)}
  证明: by
  rw [← StrongHomClass.realize_formula Substructure.topEquiv φ]
  simp

Depends on / 依赖: StrongHomClass, StrongHomClass.realize_formula, Substructure, Substructure.topEquiv, realize_formula, topEquiv
-/
theorem realize_formula_top {α : Type*} {φ : L.Formula α} {v : α -> (⊤ : L.Substructure M)} :
    φ.Realize v ↔ φ.Realize (((↑) : (⊤ : L.Substructure M) -> M) ∘ v) := by
  rw [← StrongHomClass.realize_formula Substructure.topEquiv φ]
  simp

/-- A dependent version of `Substructure.closure_induction`. -/
@[elab_as_elim]
/--
theorem `closure_induction'` / 定理 `closure_induction'`

English:
theorem closure_induction'
  statement: (s : Set M) {p : forall x, x in closure L s -> Prop}
  proof: by
  refine Exists.elim ?_ fun (hx : x in closure L s) (hc : p x hx) => hc
  exact closure_induction hx (fun x hx => ⟨subset_closure hx, Hs x hx⟩) @Hfun

中文:
定理 closure_induction'
  结论: (s : 集合 M) {p : 对任意 x, x in closure L s -> 命题}
  证明: by
  refine Exists.elim ?_ fun (hx : x in closure L s) (hc : p x hx) => hc
  exact closure_induction hx (fun x hx => ⟨subset_closure hx, Hs x hx⟩) @Hfun

Depends on / 依赖: Exists, Exists.elim, closure, closure_induction, subset_closure
-/
theorem closure_induction' (s : Set M) {p : forall x, x in closure L s -> Prop}
    (Hs : forall (x) (h : x in s), p x (subset_closure h))
    (Hfun : forall {n : Nat} (f : L.Functions n), ClosedUnder f { x | exists hx, p x hx }) {x}
    (hx : x in closure L s) : p x hx := by
  refine Exists.elim ?_ fun (hx : x in closure L s) (hc : p x hx) => hc
  exact closure_induction hx (fun x hx => ⟨subset_closure hx, Hs x hx⟩) @Hfun

end Substructure

open Substructure

namespace LHom

variable {L' : Language} [L'.Structure M]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `substructureReduct` / `substructureReduct` 的定义

English:
definition substructureReduct
  signature: (φ : L ->ᴸ L') [φ.IsExpansionOn M]
  body: { carrier := S
      fun_mem := fun {n} f x hx => by
        have h := S.fun_mem (φ.onFunction f) x hx
        simp only [LHom.map_onFunction, Substructure.mem_carrier] at h
        exact h }
  inj' S T h := by
    simp only [SetLike.coe_set_eq, Substructure.mk.injEq] at h
    exact h
  map_rel_iff' {_ _} := Iff.rfl

中文:
定义 substructureReduct
  签名: (φ : L ->ᴸ L') [φ.是ExpansionOn M]
  定义体: { carrier := S
      fun_mem := fun {n} f x hx => by
        have h := S.fun_mem (φ.onFunction f) x hx
        simp only [LHom.map_onFunction, Substructure.mem_carrier] at h
        exact h }
  inj' S T h := by
    simp only [SetLike.coe_set_eq, Substructure.mk.injEq] at h
    exact h
  map_rel_iff' {_ _} := Iff.rfl

Depends on / 依赖: Iff.rfl, LHom.map_onFunction, S.fun_mem, SetLike, SetLike.coe_set_eq, Substructure, Substructure.mem_carrier, Substructure.mk.injEq, carrier, coe_set_eq, fun_mem, map_onFunction, map_rel_iff, mem_carrier, onFunction
-/
def substructureReduct (φ : L ->ᴸ L') [φ.IsExpansionOn M] :
    L'.Substructure M ↪o L.Substructure M where
  toFun S :=
    { carrier := S
      fun_mem := fun {n} f x hx => by
        have h := S.fun_mem (φ.onFunction f) x hx
        simp only [LHom.map_onFunction, Substructure.mem_carrier] at h
        exact h }
  inj' S T h := by
    simp only [SetLike.coe_set_eq, Substructure.mk.injEq] at h
    exact h
  map_rel_iff' {_ _} := Iff.rfl

variable (φ : L ->ᴸ L') [φ.IsExpansionOn M]

@[simp]
/--
theorem `mem_substructureReduct` / 定理 `mem_substructureReduct`

English:
theorem mem_substructureReduct
  given: {x : M} {S : L'.Substructure M}
  proof: Iff.rfl

@[simp]

中文:
定理 mem_substructureReduct
  条件: {x : M} {S : L'.子结构 M}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_substructureReduct {x : M} {S : L'.Substructure M} :
    x in φ.substructureReduct S ↔ x in S :=
  Iff.rfl

@[simp]
/--
theorem `coe_substructureReduct` / 定理 `coe_substructureReduct`

English:
theorem coe_substructureReduct
  given: {S : L'.Substructure M}
  statement: (φ.substructureReduct S : Set M) = ↑S
  proof: rfl

中文:
定理 coe_substructureReduct
  条件: {S : L'.子结构 M}
  结论: (φ.substructureReduct S : 集合 M) = ↑S
  证明: rfl
-/
theorem coe_substructureReduct {S : L'.Substructure M} : (φ.substructureReduct S : Set M) = ↑S :=
  rfl

end LHom

namespace Substructure

/--
Definition of `withConstants` / `withConstants` 的定义

English:
definition withConstants
  signature: (S : L.Substructure M) {A : Set M} (h : A subseteq S)
  body: S
  fun_mem {n} f := by
    obtain f | f := f
    · exact S.fun_mem f
    · cases n
      · exact fun _ _ => h f.2
      · exact isEmptyElim f

中文:
定义 withConstants
  签名: (S : L.子结构 M) {A : 集合 M} (h : A subseteq S)
  定义体: S
  fun_mem {n} f := by
    obtain f | f := f
    · exact S.fun_mem f
    · cases n
      · exact fun _ _ => h f.2
      · exact isEmptyElim f
-/
def withConstants (S : L.Substructure M) {A : Set M} (h : A subseteq S) : L[[A]].Substructure M where
  carrier := S
  fun_mem {n} f := by
    obtain f | f := f
    · exact S.fun_mem f
    · cases n
      · exact fun _ _ => h f.2
      · exact isEmptyElim f

variable {A : Set M} {s : Set M} (h : A subseteq S)

@[simp]
/--
theorem `mem_withConstants` / 定理 `mem_withConstants`

English:
theorem mem_withConstants
  given: {x : M}
  statement: x in S.withConstants h ↔ x in S
  proof: Iff.rfl

@[simp]

中文:
定理 mem_withConstants
  条件: {x : M}
  结论: x in S.withConstants h ↔ x in S
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_withConstants {x : M} : x in S.withConstants h ↔ x in S :=
  Iff.rfl

@[simp]
/--
theorem `coe_withConstants` / 定理 `coe_withConstants`

English:
theorem coe_withConstants
  statement: (S.withConstants h : Set M) = ↑S
  proof: rfl

@[simp]

中文:
定理 coe_withConstants
  结论: (S.withConstants h : 集合 M) = ↑S
  证明: rfl

@[simp]
-/
theorem coe_withConstants : (S.withConstants h : Set M) = ↑S :=
  rfl

@[simp]
/--
theorem `reduct_withConstants` / 定理 `reduct_withConstants`

English:
theorem reduct_withConstants
  proof: by
  ext
  simp

中文:
定理 reduct_withConstants
  证明: by
  ext
  simp
-/
theorem reduct_withConstants :
    (L.lhomWithConstants A).substructureReduct (S.withConstants h) = S := by
  ext
  simp

/--
theorem `subset_closure_withConstants` / 定理 `subset_closure_withConstants`

English:
theorem subset_closure_withConstants
  statement: A subseteq closure L[[A]] s
  proof: by
  intro a ha
  simp only [SetLike.mem_coe]
  let a' : L[[A]].Constants := Sum.inr ⟨a, ha⟩
  exact constants_mem a'

中文:
定理 subset_closure_withConstants
  结论: A subseteq closure L[[A]] s
  证明: by
  intro a ha
  simp only [SetLike.mem_coe]
  let a' : L[[A]].Constants := Sum.inr ⟨a, ha⟩
  exact constants_mem a'

Depends on / 依赖: Constants, SetLike, SetLike.mem_coe, Sum.inr, constants_mem, mem_coe
-/
theorem subset_closure_withConstants : A subseteq closure L[[A]] s := by
  intro a ha
  simp only [SetLike.mem_coe]
  let a' : L[[A]].Constants := Sum.inr ⟨a, ha⟩
  exact constants_mem a'

/--
theorem `closure_withConstants_eq` / 定理 `closure_withConstants_eq`

English:
theorem closure_withConstants_eq
  proof: by
  refine closure_eq_of_le ((A.subset_union_right).trans subset_closure) ?_
  rw [← (L.lhomWithConstants A).substructureReduct.le_iff_le]
  simp only [subset_closure, reduct_withConstants, closure_le, LHom.coe_substructureReduct,
    Set.union_subset_iff, and_true]
  exact subset_closure_withConstants

中文:
定理 closure_withConstants_eq
  证明: by
  refine closure_eq_of_le ((A.subset_union_right).trans subset_closure) ?_
  rw [← (L.lhomWithConstants A).substructureReduct.le_iff_le]
  simp only [subset_closure, reduct_withConstants, closure_le, LHom.coe_substructureReduct,
    Set.union_subset_iff, and_true]
  exact subset_closure_withConstants

Depends on / 依赖: A.subset_union_right, L.lhomWithConstants, LHom.coe_substructureReduct, Set.union_subset_iff, and_true, closure_eq_of_le, closure_le, coe_substructureReduct, le_iff_le, lhomWithConstants, reduct_withConstants, subset_closure, subset_closure_withConstants, subset_union_right, substructureReduct, substructureReduct.le_iff_le, union_subset_iff
-/
theorem closure_withConstants_eq :
    closure L[[A]] s =
      (closure L (A union s)).withConstants ((A.subset_union_left).trans subset_closure) := by
  refine closure_eq_of_le ((A.subset_union_right).trans subset_closure) ?_
  rw [← (L.lhomWithConstants A).substructureReduct.le_iff_le]
  simp only [subset_closure, reduct_withConstants, closure_le, LHom.coe_substructureReduct,
    Set.union_subset_iff, and_true]
  exact subset_closure_withConstants

end Substructure

namespace Hom

/-- The restriction of a first-order hom to a substructure `s ⊆ M` gives a hom `s → N`. -/
@[simps!]
/--
Definition of `domRestrict` / `domRestrict` 的定义

English:
definition domRestrict
  signature: (f : M ->[L] N) (p : L.Substructure M)
  body: f.comp p.subtype.toHom

中文:
定义 domRestrict
  签名: (f : M ->[L] N) (p : L.子结构 M)
  定义体: f.comp p.subtype.toHom

Depends on / 依赖: f.comp, p.subtype.toHom, subtype
-/
def domRestrict (f : M ->[L] N) (p : L.Substructure M) : p ->[L] N :=
  f.comp p.subtype.toHom

/-- A first-order hom `f : M → N` whose values lie in a substructure `p ⊆ N` can be restricted to a
hom `M → p`. -/
@[simps]
/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (p : L.Substructure N) (f : M ->[L] N) (h : forall c, f c in p)
  body: ⟨f c, h c⟩
  map_fun' {n} f x := by aesop
  map_rel' {_} R x h := f.map_rel R x h

@[simp]

中文:
定义 codRestrict
  签名: (p : L.子结构 N) (f : M ->[L] N) (h : 对任意 c, f c in p)
  定义体: ⟨f c, h c⟩
  map_fun' {n} f x := by aesop
  map_rel' {_} R x h := f.map_rel R x h

@[simp]
-/
def codRestrict (p : L.Substructure N) (f : M ->[L] N) (h : forall c, f c in p) : M ->[L] p where
  toFun c := ⟨f c, h c⟩
  map_fun' {n} f x := by aesop
  map_rel' {_} R x h := f.map_rel R x h

@[simp]
/--
theorem `comp_codRestrict` / 定理 `comp_codRestrict`

English:
theorem comp_codRestrict
  given: (f : M ->[L] N) (g : N ->[L] P) (p : L.Substructure P) (h : forall b, g b in p)
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_codRestrict
  条件: (f : M ->[L] N) (g : N ->[L] P) (p : L.子结构 P) (h : 对任意 b, g b in p)
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_codRestrict (f : M ->[L] N) (g : N ->[L] P) (p : L.Substructure P) (h : forall b, g b in p) :
    ((codRestrict p g h).comp f : M ->[L] p) = codRestrict p (g.comp f) fun _ => h _ :=
  ext fun _ => rfl

@[simp]
/--
theorem `subtype_comp_codRestrict` / 定理 `subtype_comp_codRestrict`

English:
theorem subtype_comp_codRestrict
  given: (f : M ->[L] N) (p : L.Substructure N) (h : forall b, f b in p)
  proof: ext fun _ => rfl

@[simp]

中文:
定理 subtype_comp_codRestrict
  条件: (f : M ->[L] N) (p : L.子结构 N) (h : 对任意 b, f b in p)
  证明: ext fun _ => rfl

@[simp]
-/
theorem subtype_comp_codRestrict (f : M ->[L] N) (p : L.Substructure N) (h : forall b, f b in p) :
    p.subtype.toHom.comp (codRestrict p f h) = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `domRestrict_comp_codRestrict` / 定理 `domRestrict_comp_codRestrict`

English:
theorem domRestrict_comp_codRestrict
  statement: (g : N ->[L] P) (f : M ->[L] N) (p : L.Substructure N)
  proof: rfl

中文:
定理 domRestrict_comp_codRestrict
  结论: (g : N ->[L] P) (f : M ->[L] N) (p : L.子结构 N)
  证明: rfl
-/
theorem domRestrict_comp_codRestrict (g : N ->[L] P) (f : M ->[L] N) (p : L.Substructure N)
    (h : forall b, f b in p) :
    (g.domRestrict p).comp (f.codRestrict p h) = g.comp f :=
  rfl

/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: (f : M ->[L] N)
  body: (map f ⊤).copy (Set.range f) Set.image_univ.symm

中文:
定义 range
  签名: (f : M ->[L] N)
  定义体: (map f ⊤).copy (Set.range f) Set.image_univ.symm

Depends on / 依赖: Set.image_univ.symm, Set.range, image_univ
-/
def range (f : M ->[L] N) : L.Substructure N :=
  (map f ⊤).copy (Set.range f) Set.image_univ.symm

/--
theorem `range_coe` / 定理 `range_coe`

English:
theorem range_coe
  given: (f : M ->[L] N)
  statement: (range f : Set N) = Set.range f
  proof: rfl

@[simp]

中文:
定理 range_coe
  条件: (f : M ->[L] N)
  结论: (range f : 集合 N) = 集合.range f
  证明: rfl

@[simp]
-/
theorem range_coe (f : M ->[L] N) : (range f : Set N) = Set.range f :=
  rfl

@[simp]
/--
theorem `mem_range` / 定理 `mem_range`

English:
theorem mem_range
  given: {f : M ->[L] N} {x}
  statement: x in range f ↔ exists y, f y = x
  proof: Iff.rfl

中文:
定理 mem_range
  条件: {f : M ->[L] N} {x}
  结论: x in range f ↔ 存在 y, f y = x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_range {f : M ->[L] N} {x} : x in range f ↔ exists y, f y = x :=
  Iff.rfl

/--
theorem `range_eq_map` / 定理 `range_eq_map`

English:
theorem range_eq_map
  given: (f : M ->[L] N)
  statement: f.range = map f ⊤
  proof: by
  ext
  simp

中文:
定理 range_eq_map
  条件: (f : M ->[L] N)
  结论: f.range = map f ⊤
  证明: by
  ext
  simp
-/
theorem range_eq_map (f : M ->[L] N) : f.range = map f ⊤ := by
  ext
  simp

/--
theorem `mem_range_self` / 定理 `mem_range_self`

English:
theorem mem_range_self
  given: (f : M ->[L] N) (x : M)
  statement: f x in f.range
  proof: ⟨x, rfl⟩

@[simp]

中文:
定理 mem_range_self
  条件: (f : M ->[L] N) (x : M)
  结论: f x in f.range
  证明: ⟨x, rfl⟩

@[simp]
-/
theorem mem_range_self (f : M ->[L] N) (x : M) : f x in f.range :=
  ⟨x, rfl⟩

@[simp]
/--
theorem `range_id` / 定理 `range_id`

English:
theorem range_id
  statement: range (id L M) = ⊤
  proof: SetLike.coe_injective Set.range_id

中文:
定理 range_id
  结论: range (id L M) = ⊤
  证明: SetLike.coe_injective Set.range_id

Depends on / 依赖: Set.range_id, SetLike, SetLike.coe_injective, coe_injective, range_id
-/
theorem range_id : range (id L M) = ⊤ :=
  SetLike.coe_injective Set.range_id

/--
theorem `range_comp` / 定理 `range_comp`

English:
theorem range_comp
  given: (f : M ->[L] N) (g : N ->[L] P)
  statement: range (g.comp f : M ->[L] P) = map g (range f)
  proof: SetLike.coe_injective (Set.range_comp g f)

中文:
定理 range_comp
  条件: (f : M ->[L] N) (g : N ->[L] P)
  结论: range (g.comp f : M ->[L] P) = map g (range f)
  证明: SetLike.coe_injective (Set.range_comp g f)

Depends on / 依赖: Set.range_comp, SetLike, SetLike.coe_injective, coe_injective, range_comp
-/
theorem range_comp (f : M ->[L] N) (g : N ->[L] P) : range (g.comp f : M ->[L] P) = map g (range f) :=
  SetLike.coe_injective (Set.range_comp g f)

/--
theorem `range_comp_le_range` / 定理 `range_comp_le_range`

English:
theorem range_comp_le_range
  given: (f : M ->[L] N) (g : N ->[L] P)
  statement: range (g.comp f : M ->[L] P) <= range g
  proof: SetLike.coe_mono (Set.range_comp_subset_range f g)

中文:
定理 range_comp_le_range
  条件: (f : M ->[L] N) (g : N ->[L] P)
  结论: range (g.comp f : M ->[L] P) <= range g
  证明: SetLike.coe_mono (Set.range_comp_subset_range f g)

Depends on / 依赖: Set.range_comp_subset_range, SetLike, SetLike.coe_mono, coe_mono, range_comp_subset_range
-/
theorem range_comp_le_range (f : M ->[L] N) (g : N ->[L] P) : range (g.comp f : M ->[L] P) <= range g :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)

/--
theorem `range_eq_top` / 定理 `range_eq_top`

English:
theorem range_eq_top
  given: {f : M ->[L] N}
  statement: range f = ⊤ ↔ Function.Surjective f
  proof: by
  rw [SetLike.ext'_iff]; rw [range_coe]; rw [coe_top]; rw [Set.range_eq_univ]

中文:
定理 range_eq_top
  条件: {f : M ->[L] N}
  结论: range f = ⊤ ↔ 函数.满射 f
  证明: by
  rw [SetLike.ext'_iff]; rw [range_coe]; rw [coe_top]; rw [Set.range_eq_univ]

Depends on / 依赖: Set.range_eq_univ, SetLike, SetLike.ext, _iff, coe_top, range_coe, range_eq_univ
-/
theorem range_eq_top {f : M ->[L] N} : range f = ⊤ ↔ Function.Surjective f := by
  rw [SetLike.ext'_iff]; rw [range_coe]; rw [coe_top]; rw [Set.range_eq_univ]

/--
theorem `range_le_iff_comap` / 定理 `range_le_iff_comap`

English:
theorem range_le_iff_comap
  given: {f : M ->[L] N} {p : L.Substructure N}
  statement: range f <= p ↔ comap f p = ⊤
  proof: by
  rw [range_eq_map]; rw [map_le_iff_le_comap]; rw [eq_top_iff]

中文:
定理 range_le_iff_comap
  条件: {f : M ->[L] N} {p : L.子结构 N}
  结论: range f <= p ↔ comap f p = ⊤
  证明: by
  rw [range_eq_map]; rw [map_le_iff_le_comap]; rw [eq_top_iff]

Depends on / 依赖: eq_top_iff, map_le_iff_le_comap, range_eq_map
-/
theorem range_le_iff_comap {f : M ->[L] N} {p : L.Substructure N} : range f <= p ↔ comap f p = ⊤ := by
  rw [range_eq_map]; rw [map_le_iff_le_comap]; rw [eq_top_iff]

/--
theorem `map_le_range` / 定理 `map_le_range`

English:
theorem map_le_range
  given: {f : M ->[L] N} {p : L.Substructure M}
  statement: map f p <= range f
  proof: SetLike.coe_mono (Set.image_subset_range f p)

中文:
定理 map_le_range
  条件: {f : M ->[L] N} {p : L.子结构 M}
  结论: map f p <= range f
  证明: SetLike.coe_mono (Set.image_subset_range f p)

Depends on / 依赖: Set.image_subset_range, SetLike, SetLike.coe_mono, coe_mono, image_subset_range
-/
theorem map_le_range {f : M ->[L] N} {p : L.Substructure M} : map f p <= range f :=
  SetLike.coe_mono (Set.image_subset_range f p)

/--
Definition of `eqLocus` / `eqLocus` 的定义

English:
definition eqLocus
  signature: (f g : M ->[L] N)
  body: { x : M | f x = g x }
  fun_mem {n} fn x hx := by
    have h : f ∘ x = g ∘ x := by
      ext
      repeat' rw [Function.comp_apply]
      apply hx
    simp [h]

@[simp]

中文:
定义 eqLocus
  签名: (f g : M ->[L] N)
  定义体: { x : M | f x = g x }
  fun_mem {n} fn x hx := by
    have h : f ∘ x = g ∘ x := by
      ext
      repeat' rw [Function.comp_apply]
      apply hx
    simp [h]

@[simp]
-/
def eqLocus (f g : M ->[L] N) : Substructure L M where
  carrier := { x : M | f x = g x }
  fun_mem {n} fn x hx := by
    have h : f ∘ x = g ∘ x := by
      ext
      repeat' rw [Function.comp_apply]
      apply hx
    simp [h]

@[simp]
/--
theorem `mem_eqLocus` / 定理 `mem_eqLocus`

English:
theorem mem_eqLocus
  given: {f g : M ->[L] N} {x : M}
  statement: x in f.eqLocus g ↔ f x = g x
  proof: Iff.rfl

中文:
定理 mem_eqLocus
  条件: {f g : M ->[L] N} {x : M}
  结论: x in f.eqLocus g ↔ f x = g x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_eqLocus {f g : M ->[L] N} {x : M} : x in f.eqLocus g ↔ f x = g x := Iff.rfl

/--
theorem `eqOn_closure` / 定理 `eqOn_closure`

English:
theorem eqOn_closure
  given: {f g : M ->[L] N} {s : Set M} (h : Set.EqOn f g s)
  proof: show closure L s <= f.eqLocus g from closure_le.2 h

中文:
定理 eqOn_closure
  条件: {f g : M ->[L] N} {s : 集合 M} (h : 集合.EqOn f g s)
  证明: show closure L s <= f.eqLocus g from closure_le.2 h

Depends on / 依赖: closure, closure_le, eqLocus, f.eqLocus
-/
theorem eqOn_closure {f g : M ->[L] N} {s : Set M} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure L s) :=
  show closure L s <= f.eqLocus g from closure_le.2 h

/--
theorem `eq_of_eqOn_top` / 定理 `eq_of_eqOn_top`

English:
theorem eq_of_eqOn_top
  given: {f g : M ->[L] N} (h : Set.EqOn f g (⊤ : Substructure L M))
  statement: f = g
  proof: ext fun _ => h trivial

中文:
定理 eq_of_eqOn_top
  条件: {f g : M ->[L] N} (h : 集合.EqOn f g (⊤ : 子结构 L M))
  结论: f = g
  证明: ext fun _ => h trivial
-/
theorem eq_of_eqOn_top {f g : M ->[L] N} (h : Set.EqOn f g (⊤ : Substructure L M)) : f = g :=
  ext fun _ => h trivial

variable {s : Set M}

/--
theorem `eq_of_eqOn_dense` / 定理 `eq_of_eqOn_dense`

English:
theorem eq_of_eqOn_dense
  given: (hs : closure L s = ⊤) {f g : M ->[L] N} (h : s.EqOn f g)
  statement: f = g
  proof: eq_of_eqOn_top hs ▸ eqOn_closure h

中文:
定理 eq_of_eqOn_dense
  条件: (hs : closure L s = ⊤) {f g : M ->[L] N} (h : s.EqOn f g)
  结论: f = g
  证明: eq_of_eqOn_top hs ▸ eqOn_closure h

Depends on / 依赖: eqOn_closure, eq_of_eqOn_top
-/
theorem eq_of_eqOn_dense (hs : closure L s = ⊤) {f g : M ->[L] N} (h : s.EqOn f g) : f = g :=
eq_of_eqOn_top hs ▸ eqOn_closure h

end Hom

namespace Embedding

/--
Definition of `domRestrict` / `domRestrict` 的定义

English:
definition domRestrict
  signature: (f : M ↪[L] N) (p : L.Substructure M)
  body: f.comp p.subtype

@[simp]

中文:
定义 domRestrict
  签名: (f : M ↪[L] N) (p : L.子结构 M)
  定义体: f.comp p.subtype

@[simp]

Depends on / 依赖: f.comp, p.subtype, subtype
-/
def domRestrict (f : M ↪[L] N) (p : L.Substructure M) : p ↪[L] N :=
  f.comp p.subtype

@[simp]
/--
theorem `domRestrict_apply` / 定理 `domRestrict_apply`

English:
theorem domRestrict_apply
  given: (f : M ↪[L] N) (p : L.Substructure M) (x : p)
  statement: f.domRestrict p x = f x
  proof: rfl

中文:
定理 domRestrict_apply
  条件: (f : M ↪[L] N) (p : L.子结构 M) (x : p)
  结论: f.domRestrict p x = f x
  证明: rfl
-/
theorem domRestrict_apply (f : M ↪[L] N) (p : L.Substructure M) (x : p) : f.domRestrict p x = f x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (p : L.Substructure N) (f : M ↪[L] N) (h : forall c, f c in p)
  body: f.toHom.codRestrict p h
  inj' _ _ ab := f.injective (Subtype.mk_eq_mk.1 ab)
  map_fun' {_} F x := (f.toHom.codRestrict p h).map_fun' F x
  map_rel' {n} r x := by
    rw [← p.subtype.map_rel]
    change RelMap r (Hom.comp p.subtype.toHom (f.toHom.codRestrict p h) ∘ x) ↔ _
    rw [Hom.subtype_comp_codRestrict]; rw [← f.map_rel]
    rfl

@[simp]

中文:
定义 codRestrict
  签名: (p : L.子结构 N) (f : M ↪[L] N) (h : 对任意 c, f c in p)
  定义体: f.toHom.codRestrict p h
  inj' _ _ ab := f.injective (Subtype.mk_eq_mk.1 ab)
  map_fun' {_} F x := (f.toHom.codRestrict p h).map_fun' F x
  map_rel' {n} r x := by
    rw [← p.subtype.map_rel]
    change RelMap r (Hom.comp p.subtype.toHom (f.toHom.codRestrict p h) ∘ x) ↔ _
    rw [Hom.subtype_comp_codRestrict]; rw [← f.map_rel]
    rfl

@[simp]

Depends on / 依赖: codRestrict, f.toHom.codRestrict
-/
def codRestrict (p : L.Substructure N) (f : M ↪[L] N) (h : forall c, f c in p) : M ↪[L] p where
  toFun := f.toHom.codRestrict p h
  inj' _ _ ab := f.injective (Subtype.mk_eq_mk.1 ab)
  map_fun' {_} F x := (f.toHom.codRestrict p h).map_fun' F x
  map_rel' {n} r x := by
    rw [← p.subtype.map_rel]
    change RelMap r (Hom.comp p.subtype.toHom (f.toHom.codRestrict p h) ∘ x) ↔ _
    rw [Hom.subtype_comp_codRestrict]; rw [← f.map_rel]
    rfl

@[simp]
/--
theorem `codRestrict_apply` / 定理 `codRestrict_apply`

English:
theorem codRestrict_apply
  given: (p : L.Substructure N) (f : M ↪[L] N) {h} (x : M)
  proof: rfl

@[simp]

中文:
定理 codRestrict_apply
  条件: (p : L.子结构 N) (f : M ↪[L] N) {h} (x : M)
  证明: rfl

@[simp]
-/
theorem codRestrict_apply (p : L.Substructure N) (f : M ↪[L] N) {h} (x : M) :
    (codRestrict p f h x : N) = f x :=
  rfl

@[simp]
/--
theorem `codRestrict_apply'` / 定理 `codRestrict_apply'`

English:
theorem codRestrict_apply'
  given: (p : L.Substructure N) (f : M ↪[L] N) {h} (x : M)
  proof: rfl

@[simp]

中文:
定理 codRestrict_apply'
  条件: (p : L.子结构 N) (f : M ↪[L] N) {h} (x : M)
  证明: rfl

@[simp]
-/
theorem codRestrict_apply' (p : L.Substructure N) (f : M ↪[L] N) {h} (x : M) :
    codRestrict p f h x = ⟨f x, h x⟩ :=
  rfl

@[simp]
/--
theorem `comp_codRestrict` / 定理 `comp_codRestrict`

English:
theorem comp_codRestrict
  given: (f : M ↪[L] N) (g : N ↪[L] P) (p : L.Substructure P) (h : forall b, g b in p)
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_codRestrict
  条件: (f : M ↪[L] N) (g : N ↪[L] P) (p : L.子结构 P) (h : 对任意 b, g b in p)
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_codRestrict (f : M ↪[L] N) (g : N ↪[L] P) (p : L.Substructure P) (h : forall b, g b in p) :
    ((codRestrict p g h).comp f : M ↪[L] p) = codRestrict p (g.comp f) fun _ => h _ :=
  ext fun _ => rfl

@[simp]
/--
theorem `subtype_comp_codRestrict` / 定理 `subtype_comp_codRestrict`

English:
theorem subtype_comp_codRestrict
  given: (f : M ↪[L] N) (p : L.Substructure N) (h : forall b, f b in p)
  proof: ext fun _ => rfl

中文:
定理 subtype_comp_codRestrict
  条件: (f : M ↪[L] N) (p : L.子结构 N) (h : 对任意 b, f b in p)
  证明: ext fun _ => rfl
-/
theorem subtype_comp_codRestrict (f : M ↪[L] N) (p : L.Substructure N) (h : forall b, f b in p) :
    p.subtype.comp (codRestrict p f h) = f :=
  ext fun _ => rfl

/--
Definition of `substructureEquivMap` / `substructureEquivMap` 的定义

English:
definition substructureEquivMap
  signature: (f : M ↪[L] N) (s : L.Substructure M)
  body: codRestrict (s.map f.toHom) (f.domRestrict s) fun ⟨m, hm⟩ => ⟨m, hm, rfl⟩
  invFun n := ⟨Classical.choose n.2, (Classical.choose_spec n.2).1⟩
  left_inv := fun ⟨m, hm⟩ =>
    Subtype.mk_eq_mk.2
      (f.injective
        (Classical.choose_spec
            (codRestrict (s.map f.toHom) (f.domRestrict s) (fun ⟨m, hm⟩ => ⟨m, hm, rfl⟩)
                ⟨m, hm⟩).2).2)
  right_inv := fun ⟨_, hn⟩ => Subtype.mk_eq_mk.2 (Classical.choose_spec hn).2
  map_fun' {n} f x := by simp
  map_rel' {n} R x := by simp

@[simp]

中文:
定义 substructureEquivMap
  签名: (f : M ↪[L] N) (s : L.子结构 M)
  定义体: codRestrict (s.map f.toHom) (f.domRestrict s) fun ⟨m, hm⟩ => ⟨m, hm, rfl⟩
  invFun n := ⟨Classical.choose n.2, (Classical.choose_spec n.2).1⟩
  left_inv := fun ⟨m, hm⟩ =>
    Subtype.mk_eq_mk.2
      (f.injective
        (Classical.choose_spec
            (codRestrict (s.map f.toHom) (f.domRestrict s) (fun ⟨m, hm⟩ => ⟨m, hm, rfl⟩)
                ⟨m, hm⟩).2).2)
  right_inv := fun ⟨_, hn⟩ => Subtype.mk_eq_mk.2 (Classical.choose_spec hn).2
  map_fun' {n} f x := by simp
  map_rel' {n} R x := by simp

@[simp]

Depends on / 依赖: codRestrict, domRestrict, f.domRestrict, f.toHom, s.map
-/
noncomputable def substructureEquivMap (f : M ↪[L] N) (s : L.Substructure M) :
    s ≃[L] s.map f.toHom where
  toFun := codRestrict (s.map f.toHom) (f.domRestrict s) fun ⟨m, hm⟩ => ⟨m, hm, rfl⟩
  invFun n := ⟨Classical.choose n.2, (Classical.choose_spec n.2).1⟩
  left_inv := fun ⟨m, hm⟩ =>
    Subtype.mk_eq_mk.2
      (f.injective
        (Classical.choose_spec
            (codRestrict (s.map f.toHom) (f.domRestrict s) (fun ⟨m, hm⟩ => ⟨m, hm, rfl⟩)
                ⟨m, hm⟩).2).2)
  right_inv := fun ⟨_, hn⟩ => Subtype.mk_eq_mk.2 (Classical.choose_spec hn).2
  map_fun' {n} f x := by simp
  map_rel' {n} R x := by simp

@[simp]
/--
theorem `substructureEquivMap_apply` / 定理 `substructureEquivMap_apply`

English:
theorem substructureEquivMap_apply
  given: (f : M ↪[L] N) (p : L.Substructure M) (x : p)
  proof: rfl

@[simp]

中文:
定理 substructureEquivMap_apply
  条件: (f : M ↪[L] N) (p : L.子结构 M) (x : p)
  证明: rfl

@[simp]
-/
theorem substructureEquivMap_apply (f : M ↪[L] N) (p : L.Substructure M) (x : p) :
    (f.substructureEquivMap p x : N) = f x :=
  rfl

@[simp]
/--
theorem `subtype_substructureEquivMap` / 定理 `subtype_substructureEquivMap`

English:
theorem subtype_substructureEquivMap
  given: (f : M ↪[L] N) (s : L.Substructure M)
  proof: by
  ext; rfl

中文:
定理 subtype_substructureEquivMap
  条件: (f : M ↪[L] N) (s : L.子结构 M)
  证明: by
  ext; rfl
-/
theorem subtype_substructureEquivMap (f : M ↪[L] N) (s : L.Substructure M) :
    (subtype _).comp (f.substructureEquivMap s).toEmbedding = f.comp (subtype _) := by
  ext; rfl

/--
Definition of `equivRange` / `equivRange` 的定义

English:
definition equivRange
  signature: (f : M ↪[L] N)
  body: codRestrict f.toHom.range f f.toHom.mem_range_self
  invFun n := Classical.choose n.2
  left_inv m :=
    f.injective (Classical.choose_spec (codRestrict f.toHom.range f f.toHom.mem_range_self m).2)
  right_inv := fun ⟨_, hn⟩ => Subtype.mk_eq_mk.2 (Classical.choose_spec hn)
  map_fun' {n} f x := by simp
  map_rel' {n} R x := by simp

@[simp]

中文:
定义 equivRange
  签名: (f : M ↪[L] N)
  定义体: codRestrict f.toHom.range f f.toHom.mem_range_self
  invFun n := Classical.choose n.2
  left_inv m :=
    f.injective (Classical.choose_spec (codRestrict f.toHom.range f f.toHom.mem_range_self m).2)
  right_inv := fun ⟨_, hn⟩ => Subtype.mk_eq_mk.2 (Classical.choose_spec hn)
  map_fun' {n} f x := by simp
  map_rel' {n} R x := by simp

@[simp]
-/
@[simps toEquiv_apply] noncomputable def equivRange (f : M ↪[L] N) : M ≃[L] f.toHom.range where
  toFun := codRestrict f.toHom.range f f.toHom.mem_range_self
  invFun n := Classical.choose n.2
  left_inv m :=
    f.injective (Classical.choose_spec (codRestrict f.toHom.range f f.toHom.mem_range_self m).2)
  right_inv := fun ⟨_, hn⟩ => Subtype.mk_eq_mk.2 (Classical.choose_spec hn)
  map_fun' {n} f x := by simp
  map_rel' {n} R x := by simp

@[simp]
/--
theorem `equivRange_apply` / 定理 `equivRange_apply`

English:
theorem equivRange_apply
  given: (f : M ↪[L] N) (x : M)
  statement: (f.equivRange x : N) = f x
  proof: rfl

@[simp]

中文:
定理 equivRange_apply
  条件: (f : M ↪[L] N) (x : M)
  结论: (f.equivRange x : N) = f x
  证明: rfl

@[simp]
-/
theorem equivRange_apply (f : M ↪[L] N) (x : M) : (f.equivRange x : N) = f x :=
  rfl

@[simp]
/--
theorem `subtype_equivRange` / 定理 `subtype_equivRange`

English:
theorem subtype_equivRange
  given: (f : M ↪[L] N)
  statement: (subtype _).comp f.equivRange.toEmbedding = f
  proof: by
  ext; rfl

中文:
定理 subtype_equivRange
  条件: (f : M ↪[L] N)
  结论: (subtype _).comp f.equivRange.toEmbedding = f
  证明: by
  ext; rfl
-/
theorem subtype_equivRange (f : M ↪[L] N) : (subtype _).comp f.equivRange.toEmbedding = f := by
  ext; rfl

end Embedding

namespace Equiv

/--
theorem `toHom_range` / 定理 `toHom_range`

English:
theorem toHom_range
  given: (f : M ≃[L] N)
  statement: f.toHom.range = ⊤
  proof: by
  ext n
  simp only [Hom.mem_range, coe_toHom, Substructure.mem_top, iff_true]
  exact ⟨f.symm n, apply_symm_apply _ _⟩

中文:
定理 toHom_range
  条件: (f : M ≃[L] N)
  结论: f.toHom.range = ⊤
  证明: by
  ext n
  simp only [Hom.mem_range, coe_toHom, Substructure.mem_top, iff_true]
  exact ⟨f.symm n, apply_symm_apply _ _⟩

Depends on / 依赖: Hom.mem_range, Substructure, Substructure.mem_top, apply_symm_apply, coe_toHom, f.symm, iff_true, mem_range, mem_top
-/
theorem toHom_range (f : M ≃[L] N) : f.toHom.range = ⊤ := by
  ext n
  simp only [Hom.mem_range, coe_toHom, Substructure.mem_top, iff_true]
  exact ⟨f.symm n, apply_symm_apply _ _⟩

end Equiv

namespace Substructure

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: {S T : L.Substructure M} (h : S <= T)
  body: S.subtype.codRestrict _ fun x => h x.2

@[simp]

中文:
定义 inclusion
  签名: {S T : L.子结构 M} (h : S <= T)
  定义体: S.subtype.codRestrict _ fun x => h x.2

@[simp]

Depends on / 依赖: S.subtype.codRestrict, codRestrict, subtype
-/
def inclusion {S T : L.Substructure M} (h : S <= T) : S ↪[L] T :=
  S.subtype.codRestrict _ fun x => h x.2

@[simp]
/--
theorem `inclusion_self` / 定理 `inclusion_self`

English:
theorem inclusion_self
  given: (S : L.Substructure M)
  statement: inclusion (le_refl S) = Embedding.refl L S
  proof: rfl

@[simp]

中文:
定理 inclusion_self
  条件: (S : L.子结构 M)
  结论: inclusion (le_refl S) = 嵌入.refl L S
  证明: rfl

@[simp]
-/
theorem inclusion_self (S : L.Substructure M) : inclusion (le_refl S) = Embedding.refl L S := rfl

@[simp]
/--
theorem `coe_inclusion` / 定理 `coe_inclusion`

English:
theorem coe_inclusion
  given: {S T : L.Substructure M} (h : S <= T)
  proof: rfl

中文:
定理 coe_inclusion
  条件: {S T : L.子结构 M} (h : S <= T)
  证明: rfl
-/
theorem coe_inclusion {S T : L.Substructure M} (h : S <= T) :
    (inclusion h : S -> T) = Set.inclusion h :=
  rfl

/--
theorem `range_subtype` / 定理 `range_subtype`

English:
theorem range_subtype
  given: (S : L.Substructure M)
  statement: S.subtype.toHom.range = S
  proof: by
  ext x
  simp only [Hom.mem_range, Embedding.coe_toHom, coe_subtype]
  refine ⟨?_, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  rintro ⟨⟨y, hy⟩, rfl⟩
  exact hy

@[simp]

中文:
定理 range_subtype
  条件: (S : L.子结构 M)
  结论: S.subtype.toHom.range = S
  证明: by
  ext x
  simp only [Hom.mem_range, Embedding.coe_toHom, coe_subtype]
  refine ⟨?_, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  rintro ⟨⟨y, hy⟩, rfl⟩
  exact hy

@[simp]

Depends on / 依赖: Embedding, Embedding.coe_toHom, Hom.mem_range, coe_subtype, coe_toHom, mem_range
-/
theorem range_subtype (S : L.Substructure M) : S.subtype.toHom.range = S := by
  ext x
  simp only [Hom.mem_range, Embedding.coe_toHom, coe_subtype]
  refine ⟨?_, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  rintro ⟨⟨y, hy⟩, rfl⟩
  exact hy

@[simp]
/--
lemma `subtype_comp_inclusion` / 引理 `subtype_comp_inclusion`

English:
lemma subtype_comp_inclusion
  given: {S T : L.Substructure M} (h : S <= T)
  proof: rfl

中文:
引理 subtype_comp_inclusion
  条件: {S T : L.子结构 M} (h : S <= T)
  证明: rfl
-/
lemma subtype_comp_inclusion {S T : L.Substructure M} (h : S <= T) :
    T.subtype.comp (inclusion h) = S.subtype := rfl

end Substructure

end Language

end FirstOrder
