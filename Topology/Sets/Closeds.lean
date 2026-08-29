/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.Clopen

/-!
# Closed sets

We define a few types of closed sets in a topological space.

## Main Definitions

For a topological space `α`,
* `TopologicalSpace.Closeds α`: The type of closed sets.
* `TopologicalSpace.Clopens α`: The type of clopen sets.
-/

@[expose] public section


open Order OrderDual Set Topology


variable {ι α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

namespace TopologicalSpace

/-! ### Closed sets -/


/--
Definition of `Closeds` / `Closeds` 的定义

English:
structure Closeds
  parameters: (α : Type*) [TopologicalSpace α]
  axioms and operations (2):
    - carrier : Set α
    - isClosed' : IsClosed carrier

中文:
结构 Closeds
  参数: (α : 类型) [拓扑空间 α]
  公理与运算 (2 个):
    - carrier : 集合 α
    - isClosed' : 是闭集 carrier
-/
structure Closeds (α : Type*) [TopologicalSpace α] where
  /-- the carrier set, i.e. the points in this set -/
  carrier : Set α
  isClosed' : IsClosed carrier

namespace Closeds

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (Closeds α) α
  body: Closeds.carrier
  coe_injective s t h := by cases s; cases t; congr

中文:
实例 :
  签名: 集合状 (Closeds α) α
  定义体: Closeds.carrier
  coe_injective s t h := by cases s; cases t; congr

Depends on / 依赖: Closeds, Closeds.carrier, carrier
-/
instance : SetLike (Closeds α) α where
  coe := Closeds.carrier
  coe_injective s t h := by cases s; cases t; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Closeds α)
  body: fast_instance% .ofSetLike (Closeds α) α

中文:
实例 :
  签名: 偏序 (Closeds α)
  定义体: fast_instance% .ofSetLike (Closeds α) α

Depends on / 依赖: Closeds, fast_instance, ofSetLike
-/
instance : PartialOrder (Closeds α) := fast_instance% .ofSetLike (Closeds α) α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanLift (Set α) (Closeds α) (↑) IsClosed
  body: ⟨⟨s, hs⟩, rfl⟩

中文:
实例 :
  签名: CanLift (集合 α) (Closeds α) (↑) 是闭集
  定义体: ⟨⟨s, hs⟩, rfl⟩
-/
instance : CanLift (Set α) (Closeds α) (↑) IsClosed where
  prf s hs := ⟨⟨s, hs⟩, rfl⟩

/--
theorem `isClosed` / 定理 `isClosed`

English:
theorem isClosed
  given: (s : Closeds α)
  statement: IsClosed (s : Set α)
  proof: s.isClosed'

中文:
定理 isClosed
  条件: (s : Closeds α)
  结论: 是闭集 (s : 集合 α)
  证明: s.isClosed'

Depends on / 依赖: isClosed, s.isClosed
-/
theorem isClosed (s : Closeds α) : IsClosed (s : Set α) :=
  s.isClosed'

/--
Definition of `Simps.coe` / `Simps.coe` 的定义

English:
definition Simps.coe
  signature: (s : Closeds α)
  body: s

initialize_simps_projections Closeds (carrier -> coe, as_prefix coe)

@[simp]

中文:
定义 Simps.coe
  签名: (s : Closeds α)
  定义体: s

initialize_simps_projections Closeds (carrier -> coe, as_prefix coe)

@[simp]
-/
def Simps.coe (s : Closeds α) : Set α := s

initialize_simps_projections Closeds (carrier -> coe, as_prefix coe)

@[simp]
/--
lemma `carrier_eq_coe` / 引理 `carrier_eq_coe`

English:
lemma carrier_eq_coe
  given: (s : Closeds α)
  statement: s.carrier = (s : Set α)
  proof: rfl

@[ext]

中文:
引理 carrier_eq_coe
  条件: (s : Closeds α)
  结论: s.carrier = (s : 集合 α)
  证明: rfl

@[ext]
-/
lemma carrier_eq_coe (s : Closeds α) : s.carrier = (s : Set α) := rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {s t : Closeds α} (h : (s : Set α) = t)
  statement: s = t
  proof: SetLike.ext' h

@[simp]

中文:
定理 ext
  条件: {s t : Closeds α} (h : (s : 集合 α) = t)
  结论: s = t
  证明: SetLike.ext' h

@[simp]
-/
protected theorem ext {s t : Closeds α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (s : Set α) (h)
  statement: (mk s h : Set α) = s
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (s : 集合 α) (h)
  结论: (mk s h : 集合 α) = s
  证明: rfl

@[simp]
-/
theorem coe_mk (s : Set α) (h) : (mk s h : Set α) = s :=
  rfl

@[simp]
/--
lemma `mem_mk` / 引理 `mem_mk`

English:
lemma mem_mk
  given: {s : Set α} {hs : IsClosed s} {x : α}
  statement: x in (⟨s, hs⟩ : Closeds α) ↔ x in s
  proof: .rfl

中文:
引理 mem_mk
  条件: {s : 集合 α} {hs : 是闭集 s} {x : α}
  结论: x in (⟨s, hs⟩ : Closeds α) ↔ x in s
  证明: .rfl
-/
lemma mem_mk {s : Set α} {hs : IsClosed s} {x : α} : x in (⟨s, hs⟩ : Closeds α) ↔ x in s :=
  .rfl

/-- The closure of a set, as an element of `TopologicalSpace.Closeds`. -/
@[simps]
/--
Definition of `closure` / `closure` 的定义

English:
definition closure
  signature: (s : Set α)
  body: ⟨closure s, isClosed_closure⟩

@[simp]

中文:
定义 closure
  签名: (s : 集合 α)
  定义体: ⟨closure s, isClosed_closure⟩

@[simp]
-/
protected def closure (s : Set α) : Closeds α :=
  ⟨closure s, isClosed_closure⟩

@[simp]
/--
theorem `mem_closure` / 定理 `mem_closure`

English:
theorem mem_closure
  given: {s : Set α} {x : α}
  statement: x in Closeds.closure s ↔ x in closure s
  proof: .rfl

中文:
定理 mem_closure
  条件: {s : 集合 α} {x : α}
  结论: x in Closeds.closure s ↔ x in closure s
  证明: .rfl
-/
theorem mem_closure {s : Set α} {x : α} : x in Closeds.closure s ↔ x in closure s := .rfl

/--
theorem `gc` / 定理 `gc`

English:
theorem gc
  statement: GaloisConnection Closeds.closure ((↑) : Closeds α -> Set α)
  proof: fun _ U =>
  ⟨subset_closure.trans, fun h => closure_minimal h U.isClosed⟩

@[simp]

中文:
定理 gc
  结论: GaloisConnection Closeds.closure ((↑) : Closeds α -> 集合 α)
  证明: fun _ U =>
  ⟨subset_closure.trans, fun h => closure_minimal h U.isClosed⟩

@[simp]
-/
theorem gc : GaloisConnection Closeds.closure ((↑) : Closeds α -> Set α) := fun _ U =>
  ⟨subset_closure.trans, fun h => closure_minimal h U.isClosed⟩

@[simp]
/--
lemma `closure_le` / 引理 `closure_le`

English:
lemma closure_le
  given: {s : Set α} {t : Closeds α}
  statement: .closure s <= t ↔ s subseteq t
  proof: t.isClosed.closure_subset_iff

中文:
引理 closure_le
  条件: {s : 集合 α} {t : Closeds α}
  结论: .closure s <= t ↔ s subseteq t
  证明: t.isClosed.closure_subset_iff

Depends on / 依赖: closure_subset_iff, isClosed, t.isClosed.closure_subset_iff
-/
lemma closure_le {s : Set α} {t : Closeds α} : .closure s <= t ↔ s subseteq t :=
  t.isClosed.closure_subset_iff

/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion (@Closeds.closure α _) (↑) where
  body: ⟨s, closure_eq_iff_isClosed.1 hs.antisymm subset_closure⟩
  gc := gc
  le_l_u _ := subset_closure
choice_eq _s hs := SetLike.coe_injective subset_closure.antisymm hs

中文:
定义 gi
  签名: : Galois嵌入 (@Closeds.closure α _) (↑) where
  定义体: ⟨s, closure_eq_iff_isClosed.1 hs.antisymm subset_closure⟩
  gc := gc
  le_l_u _ := subset_closure
choice_eq _s hs := SetLike.coe_injective subset_closure.antisymm hs

Depends on / 依赖: antisymm, closure_eq_iff_isClosed, hs.antisymm, subset_closure
-/
def gi : GaloisInsertion (@Closeds.closure α _) (↑) where
choice s hs := ⟨s, closure_eq_iff_isClosed.1 hs.antisymm subset_closure⟩
  gc := gc
  le_l_u _ := subset_closure
choice_eq _s hs := SetLike.coe_injective subset_closure.antisymm hs

/--
Instance `instCompleteLattice` / 实例 `instCompleteLattice`

English:
instance instCompleteLattice
  signature: : CompleteLattice (Closeds α)
  body: fast_instance% CompleteLattice.copy
    (GaloisInsertion.liftCompleteLattice gi)
    -- le
    _ rfl
    -- top
    ⟨univ, isClosed_univ⟩ rfl
    -- bot
    ⟨∅, isClosed_empty⟩ (SetLike.coe_injective closure_empty.symm)
    -- sup
    (fun s t => ⟨s union t, s.2.union t.2⟩)
    (funext fun s => fune

中文:
实例 instCompleteLattice
  签名: : 完备格 (Closeds α)
  定义体: fast_instance% CompleteLattice.copy
    (GaloisInsertion.liftCompleteLattice gi)
    -- le
    _ rfl
    -- top
    ⟨univ, isClosed_univ⟩ rfl
    -- bot
    ⟨∅, isClosed_empty⟩ (SetLike.coe_injective closure_empty.symm)
    -- sup
    (fun s t => ⟨s union t, s.2.union t.2⟩)
    (funext fun s => fune

Depends on / 依赖: CompleteLattice, CompleteLattice.copy, GaloisInsertion, GaloisInsertion.liftCompleteLattice, fast_instance, liftCompleteLattice
-/
instance instCompleteLattice : CompleteLattice (Closeds α) :=
  fast_instance% CompleteLattice.copy
    (GaloisInsertion.liftCompleteLattice gi)
    -- le
    _ rfl
    -- top
    ⟨univ, isClosed_univ⟩ rfl
    -- bot
    ⟨∅, isClosed_empty⟩ (SetLike.coe_injective closure_empty.symm)
    -- sup
    (fun s t => ⟨s union t, s.2.union t.2⟩)
    (funext fun s => funext fun t => SetLike.coe_injective (s.2.union t.2).closure_eq.symm)
    -- inf
    (fun s t => ⟨s inter t, s.2.inter t.2⟩) rfl
    -- sSup
    _ rfl
    -- sInf
    (fun S => ⟨⋂ s in S, ↑s, isClosed_biInter fun s _ => s.2⟩)
    (funext fun _ => SetLike.coe_injective sInf_image.symm)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Closeds α)
  body: ⟨⊥⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 可居 (Closeds α)
  定义体: ⟨⊥⟩

@[simp, norm_cast]
-/
instance : Inhabited (Closeds α) :=
  ⟨⊥⟩

@[simp, norm_cast]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  given: (s t : Closeds α)
  statement: (↑(s ⊔ t) : Set α) = ↑s union ↑t
  proof: by
  rfl

@[simp, norm_cast]

中文:
定理 coe_sup
  条件: (s t : Closeds α)
  结论: (↑(s ⊔ t) : 集合 α) = ↑s union ↑t
  证明: by
  rfl

@[simp, norm_cast]
-/
theorem coe_sup (s t : Closeds α) : (↑(s ⊔ t) : Set α) = ↑s union ↑t := by
  rfl

@[simp, norm_cast]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (s t : Closeds α)
  statement: (↑(s ⊓ t) : Set α) = ↑s inter ↑t
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_inf
  条件: (s t : Closeds α)
  结论: (↑(s ⊓ t) : 集合 α) = ↑s inter ↑t
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_inf (s t : Closeds α) : (↑(s ⊓ t) : Set α) = ↑s inter ↑t :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: (↑(⊤ : Closeds α) : Set α) = univ
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_top
  结论: (↑(⊤ : Closeds α) : 集合 α) = univ
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_top : (↑(⊤ : Closeds α) : Set α) = univ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_eq_univ` / 定理 `coe_eq_univ`

English:
theorem coe_eq_univ
  given: {s : Closeds α}
  statement: (s : Set α) = univ ↔ s = ⊤
  proof: SetLike.coe_injective.eq_iff' rfl

@[simp, norm_cast]

中文:
定理 coe_eq_univ
  条件: {s : Closeds α}
  结论: (s : 集合 α) = univ ↔ s = ⊤
  证明: SetLike.coe_injective.eq_iff' rfl

@[simp, norm_cast]

Depends on / 依赖: SetLike, SetLike.coe_injective.eq_iff, coe_injective, eq_iff
-/
theorem coe_eq_univ {s : Closeds α} : (s : Set α) = univ ↔ s = ⊤ :=
  SetLike.coe_injective.eq_iff' rfl

@[simp, norm_cast]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: (↑(⊥ : Closeds α) : Set α) = ∅
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_bot
  结论: (↑(⊥ : Closeds α) : 集合 α) = ∅
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_bot : (↑(⊥ : Closeds α) : Set α) = ∅ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_eq_empty` / 定理 `coe_eq_empty`

English:
theorem coe_eq_empty
  given: {s : Closeds α}
  statement: (s : Set α) = ∅ ↔ s = ⊥
  proof: SetLike.coe_injective.eq_iff' rfl

中文:
定理 coe_eq_empty
  条件: {s : Closeds α}
  结论: (s : 集合 α) = ∅ ↔ s = ⊥
  证明: SetLike.coe_injective.eq_iff' rfl

Depends on / 依赖: SetLike, SetLike.coe_injective.eq_iff, coe_injective, eq_iff
-/
theorem coe_eq_empty {s : Closeds α} : (s : Set α) = ∅ ↔ s = ⊥ :=
  SetLike.coe_injective.eq_iff' rfl

/--
theorem `coe_nonempty` / 定理 `coe_nonempty`

English:
theorem coe_nonempty
  given: {s : Closeds α}
  statement: (s : Set α).Nonempty ↔ s != ⊥
  proof: nonempty_iff_ne_empty.trans coe_eq_empty.not

@[simp, norm_cast]

中文:
定理 coe_nonempty
  条件: {s : Closeds α}
  结论: (s : 集合 α).非空 ↔ s != ⊥
  证明: nonempty_iff_ne_empty.trans coe_eq_empty.not

@[simp, norm_cast]

Depends on / 依赖: coe_eq_empty, coe_eq_empty.not, nonempty_iff_ne_empty, nonempty_iff_ne_empty.trans
-/
theorem coe_nonempty {s : Closeds α} : (s : Set α).Nonempty ↔ s != ⊥ :=
  nonempty_iff_ne_empty.trans coe_eq_empty.not

@[simp, norm_cast]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: {S : Set (Closeds α)}
  statement: (↑(sInf S) : Set α) = ⋂ i in S, ↑i
  proof: rfl

@[simp]

中文:
定理 coe_sInf
  条件: {S : 集合 (Closeds α)}
  结论: (↑(sInf S) : 集合 α) = ⋂ i in S, ↑i
  证明: rfl

@[simp]
-/
theorem coe_sInf {S : Set (Closeds α)} : (↑(sInf S) : Set α) = ⋂ i in S, ↑i :=
  rfl

@[simp]
/--
lemma `coe_sSup` / 引理 `coe_sSup`

English:
lemma coe_sSup
  given: {S : Set (Closeds α)}
  statement: ((sSup S : Closeds α) : Set α) =
  proof: by rfl

@[simp, norm_cast]

中文:
引理 coe_sSup
  条件: {S : 集合 (Closeds α)}
  结论: ((sSup S : Closeds α) : 集合 α) =
  证明: by rfl

@[simp, norm_cast]
-/
lemma coe_sSup {S : Set (Closeds α)} : ((sSup S : Closeds α) : Set α) =
    closure (⋃₀ ((↑) '' S)) := by rfl

@[simp, norm_cast]
/--
theorem `coe_finset_sup` / 定理 `coe_finset_sup`

English:
theorem coe_finset_sup
  given: (f : ι -> Closeds α) (s : Finset ι)
  proof: map_finset_sup (⟨⟨(↑), coe_sup⟩, coe_bot⟩ : SupBotHom (Closeds α) (Set α)) _ _

@[simp, norm_cast]

中文:
定理 coe_finset_sup
  条件: (f : ι -> Closeds α) (s : 有限集 ι)
  证明: map_finset_sup (⟨⟨(↑), coe_sup⟩, coe_bot⟩ : SupBotHom (Closeds α) (Set α)) _ _

@[simp, norm_cast]

Depends on / 依赖: Closeds, SupBotHom, coe_bot, coe_sup, map_finset_sup
-/
theorem coe_finset_sup (f : ι -> Closeds α) (s : Finset ι) :
    (↑(s.sup f) : Set α) = s.sup ((↑) ∘ f) :=
  map_finset_sup (⟨⟨(↑), coe_sup⟩, coe_bot⟩ : SupBotHom (Closeds α) (Set α)) _ _

@[simp, norm_cast]
/--
theorem `coe_finset_inf` / 定理 `coe_finset_inf`

English:
theorem coe_finset_inf
  given: (f : ι -> Closeds α) (s : Finset ι)
  proof: map_finset_inf (⟨⟨(↑), coe_inf⟩, coe_top⟩ : InfTopHom (Closeds α) (Set α)) _ _

@[simp]

中文:
定理 coe_finset_inf
  条件: (f : ι -> Closeds α) (s : 有限集 ι)
  证明: map_finset_inf (⟨⟨(↑), coe_inf⟩, coe_top⟩ : InfTopHom (Closeds α) (Set α)) _ _

@[simp]

Depends on / 依赖: Closeds, InfTopHom, coe_inf, coe_top, map_finset_inf
-/
theorem coe_finset_inf (f : ι -> Closeds α) (s : Finset ι) :
    (↑(s.inf f) : Set α) = s.inf ((↑) ∘ f) :=
  map_finset_inf (⟨⟨(↑), coe_inf⟩, coe_top⟩ : InfTopHom (Closeds α) (Set α)) _ _

@[simp]
/--
theorem `mem_sInf` / 定理 `mem_sInf`

English:
theorem mem_sInf
  given: {S : Set (Closeds α)} {x : α}
  statement: x in sInf S ↔ forall s in S, x in s
  proof: mem_iInter₂

@[simp]

中文:
定理 mem_sInf
  条件: {S : 集合 (Closeds α)} {x : α}
  结论: x in sInf S ↔ 对任意 s in S, x in s
  证明: mem_iInter₂

@[simp]
-/
theorem mem_sInf {S : Set (Closeds α)} {x : α} : x in sInf S ↔ forall s in S, x in s := mem_iInter₂

@[simp]
/--
theorem `mem_iInf` / 定理 `mem_iInf`

English:
theorem mem_iInf
  given: {ι} {x : α} {s : ι -> Closeds α}
  statement: x in iInf s ↔ forall i, x in s i
  proof: by simp [iInf]

@[simp, norm_cast]

中文:
定理 mem_iInf
  条件: {ι} {x : α} {s : ι -> Closeds α}
  结论: x in iInf s ↔ 对任意 i, x in s i
  证明: by simp [iInf]

@[simp, norm_cast]
-/
theorem mem_iInf {ι} {x : α} {s : ι -> Closeds α} : x in iInf s ↔ forall i, x in s i := by simp [iInf]

@[simp, norm_cast]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι} (s : ι -> Closeds α)
  statement: ((⨅ i, s i : Closeds α) : Set α) = ⋂ i, s i
  proof: by
  ext; simp

中文:
定理 coe_iInf
  条件: {ι} (s : ι -> Closeds α)
  结论: ((⨅ i, s i : Closeds α) : 集合 α) = ⋂ i, s i
  证明: by
  ext; simp
-/
theorem coe_iInf {ι} (s : ι -> Closeds α) : ((⨅ i, s i : Closeds α) : Set α) = ⋂ i, s i := by
  ext; simp

/--
theorem `iInf_def` / 定理 `iInf_def`

English:
theorem iInf_def
  given: {ι} (s : ι -> Closeds α)
  proof: by ext1; simp

@[simp]

中文:
定理 iInf_def
  条件: {ι} (s : ι -> Closeds α)
  证明: by ext1; simp

@[simp]
-/
theorem iInf_def {ι} (s : ι -> Closeds α) :
    ⨅ i, s i = ⟨⋂ i, s i, isClosed_iInter fun i => (s i).2⟩ := by ext1; simp

@[simp]
/--
theorem `iInf_mk` / 定理 `iInf_mk`

English:
theorem iInf_mk
  given: {ι} (s : ι -> Set α) (h : forall i, IsClosed (s i))
  proof: iInf_def _

中文:
定理 iInf_mk
  条件: {ι} (s : ι -> 集合 α) (h : 对任意 i, 是闭集 (s i))
  证明: iInf_def _

Depends on / 依赖: iInf_def
-/
theorem iInf_mk {ι} (s : ι -> Set α) (h : forall i, IsClosed (s i)) :
    (⨅ i, ⟨s i, h i⟩ : Closeds α) = ⟨⋂ i, s i, isClosed_iInter h⟩ :=
  iInf_def _

/--
Instance `instCoframe` / 实例 `instCoframe`

English:
instance instCoframe
  signature: : Coframe (Closeds α)
  body: fast_instance% .ofMinimalAxioms {
  iInf_sup_le_sup_sInf a s :=
    (SetLike.coe_injective <| by simp only [coe_sup, coe_iInf, coe_sInf, Set.union_iInter₂]).le }

@[simps]

中文:
实例 instCoframe
  签名: : 余frame (Closeds α)
  定义体: fast_instance% .ofMinimalAxioms {
  iInf_sup_le_sup_sInf a s :=
    (SetLike.coe_injective <| by simp only [coe_sup, coe_iInf, coe_sInf, Set.union_iInter₂]).le }

@[simps]

Depends on / 依赖: fast_instance, ofMinimalAxioms
-/
instance instCoframe : Coframe (Closeds α) := fast_instance% .ofMinimalAxioms {
  iInf_sup_le_sup_sInf a s :=
    (SetLike.coe_injective <| by simp only [coe_sup, coe_iInf, coe_sInf, Set.union_iInter₂]).le }

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T1Space
  signature: α] : Singleton α (Closeds α) where
  body: ⟨{x}, isClosed_singleton⟩

@[simp]

中文:
实例 [T1空间
  签名: α] : 单例 α (Closeds α) where
  定义体: ⟨{x}, isClosed_singleton⟩

@[simp]

Depends on / 依赖: isClosed_singleton
-/
instance [T1Space α] : Singleton α (Closeds α) where
  singleton x := ⟨{x}, isClosed_singleton⟩

@[simp]
/--
theorem `mk_singleton` / 定理 `mk_singleton`

English:
theorem mk_singleton
  given: [T1Space α] {x : α}
  proof: rfl

中文:
定理 mk_singleton
  条件: [T1空间 α] {x : α}
  证明: rfl
-/
theorem mk_singleton [T1Space α] {x : α} :
    (⟨{x}, isClosed_singleton⟩ : Closeds α) = {x} :=
  rfl

/--
lemma `mem_singleton` / 引理 `mem_singleton`

English:
lemma mem_singleton
  given: [T1Space α] {a b : α}
  statement: a in ({b} : Closeds α) ↔ a = b
  proof: Iff.rfl

中文:
引理 mem_singleton
  条件: [T1空间 α] {a b : α}
  结论: a in ({b} : Closeds α) ↔ a = b
  证明: Iff.rfl
-/
@[simp] lemma mem_singleton [T1Space α] {a b : α} : a in ({b} : Closeds α) ↔ a = b := Iff.rfl

/--
theorem `singleton_injective` / 定理 `singleton_injective`

English:
theorem singleton_injective
  given: [T1Space α]
  statement: Function.Injective ({·} : α -> Closeds α)
  proof: .of_comp (f := SetLike.coe) Set.singleton_injective

@[simp]

中文:
定理 singleton_injective
  条件: [T1空间 α]
  结论: 函数.单射 ({·} : α -> Closeds α)
  证明: .of_comp (f := SetLike.coe) Set.singleton_injective

@[simp]

Depends on / 依赖: Set.singleton_injective, SetLike, SetLike.coe, of_comp, singleton_injective
-/
theorem singleton_injective [T1Space α] : Function.Injective ({·} : α -> Closeds α) :=
  .of_comp (f := SetLike.coe) Set.singleton_injective

@[simp]
/--
theorem `singleton_inj` / 定理 `singleton_inj`

English:
theorem singleton_inj
  given: [T1Space α] {x y : α}
  statement: ({x} : Closeds α) = {y} ↔ x = y
  proof: singleton_injective.eq_iff

中文:
定理 singleton_inj
  条件: [T1空间 α] {x y : α}
  结论: ({x} : Closeds α) = {y} ↔ x = y
  证明: singleton_injective.eq_iff

Depends on / 依赖: eq_iff, singleton_injective, singleton_injective.eq_iff
-/
theorem singleton_inj [T1Space α] {x y : α} : ({x} : Closeds α) = {y} ↔ x = y :=
  singleton_injective.eq_iff

/-- The preimage of a closed set under a continuous map. -/
@[simps]
/--
Definition of `preimage` / `preimage` 的定义

English:
definition preimage
  signature: (s : Closeds β) {f : α -> β} (hf : Continuous f)
  body: ⟨f ⁻¹' s, s.isClosed.preimage hf⟩

中文:
定义 原像
  签名: (s : Closeds β) {f : α -> β} (hf : 连续 f)
  定义体: ⟨f ⁻¹' s, s.isClosed.preimage hf⟩

Depends on / 依赖: isClosed, preimage, s.isClosed.preimage
-/
def preimage (s : Closeds β) {f : α -> β} (hf : Continuous f) : Closeds α :=
  ⟨f ⁻¹' s, s.isClosed.preimage hf⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SProd (Closeds α) (Closeds β) (Closeds (α × β))
  body: ⟨s ×ˢ t, s.isClosed.prod t.isClosed⟩

@[simp]

中文:
实例 :
  签名: SProd (Closeds α) (Closeds β) (Closeds (α × β))
  定义体: ⟨s ×ˢ t, s.isClosed.prod t.isClosed⟩

@[simp]

Depends on / 依赖: isClosed, s.isClosed.prod, t.isClosed
-/
instance : SProd (Closeds α) (Closeds β) (Closeds (α × β)) where
  sprod s t := ⟨s ×ˢ t, s.isClosed.prod t.isClosed⟩

@[simp]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (s : Closeds α) (t : Closeds β)
  proof: rfl

@[simp]

中文:
定理 coe_prod
  条件: (s : Closeds α) (t : Closeds β)
  证明: rfl

@[simp]
-/
theorem coe_prod (s : Closeds α) (t : Closeds β) :
    (s ×ˢ t : Closeds (α × β)) = (s : Set α) ×ˢ (t : Set β) :=
  rfl

@[simp]
/--
theorem `mem_prod` / 定理 `mem_prod`

English:
theorem mem_prod
  given: {s : Closeds α} {t : Closeds β} {x : α × β}
  statement: x in s ×ˢ t ↔ x.1 in s ∧ x.2 in t
  proof: Iff.rfl

@[simp]

中文:
定理 mem_prod
  条件: {s : Closeds α} {t : Closeds β} {x : α × β}
  结论: x in s ×ˢ t ↔ x.1 in s ∧ x.2 in t
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_prod {s : Closeds α} {t : Closeds β} {x : α × β} : x in s ×ˢ t ↔ x.1 in s ∧ x.2 in t :=
  Iff.rfl

@[simp]
/--
theorem `singleton_prod_singleton` / 定理 `singleton_prod_singleton`

English:
theorem singleton_prod_singleton
  given: [T1Space α] [T1Space β] (x : α) (y : β)
  proof: Closeds.ext Set.singleton_prod_singleton

中文:
定理 singleton_prod_singleton
  条件: [T1空间 α] [T1空间 β] (x : α) (y : β)
  证明: Closeds.ext Set.singleton_prod_singleton

Depends on / 依赖: Closeds, Closeds.ext, Set.singleton_prod_singleton, singleton_prod_singleton
-/
theorem singleton_prod_singleton [T1Space α] [T1Space β] (x : α) (y : β) :
    ({x} ×ˢ {y} : Closeds (α × β)) = {(x, y)} :=
  Closeds.ext Set.singleton_prod_singleton

end Closeds

/-- The complement of a closed set as an open set. -/
@[simps]
/--
Definition of `Closeds.compl` / `Closeds.compl` 的定义

English:
definition Closeds.compl
  signature: (s : Closeds α)
  body: ⟨sᶜ, s.2.isOpen_compl⟩

中文:
定义 Closeds.compl
  签名: (s : Closeds α)
  定义体: ⟨sᶜ, s.2.isOpen_compl⟩

Depends on / 依赖: isOpen_compl
-/
def Closeds.compl (s : Closeds α) : Opens α :=
  ⟨sᶜ, s.2.isOpen_compl⟩

/-- The complement of an open set as a closed set. -/
@[simps]
/--
Definition of `Opens.compl` / `Opens.compl` 的定义

English:
definition Opens.compl
  signature: (s : Opens α)
  body: ⟨sᶜ, s.2.isClosed_compl⟩

nonrec theorem Closeds.compl_compl (s : Closeds α) : s.compl.compl = s :=
  Closeds.ext (compl_compl (s : Set α))

nonrec theorem Opens.compl_compl (s : Opens α) : s.compl.compl = s :=
  Opens.ext (compl_compl (s : Set α))

中文:
定义 Opens.compl
  签名: (s : Opens α)
  定义体: ⟨sᶜ, s.2.isClosed_compl⟩

nonrec theorem Closeds.compl_compl (s : Closeds α) : s.compl.compl = s :=
  Closeds.ext (compl_compl (s : Set α))

nonrec theorem Opens.compl_compl (s : Opens α) : s.compl.compl = s :=
  Opens.ext (compl_compl (s : Set α))

Depends on / 依赖: isClosed_compl
-/
def Opens.compl (s : Opens α) : Closeds α :=
  ⟨sᶜ, s.2.isClosed_compl⟩

nonrec theorem Closeds.compl_compl (s : Closeds α) : s.compl.compl = s :=
  Closeds.ext (compl_compl (s : Set α))

nonrec theorem Opens.compl_compl (s : Opens α) : s.compl.compl = s :=
  Opens.ext (compl_compl (s : Set α))

/--
theorem `Closeds.compl_bijective` / 定理 `Closeds.compl_bijective`

English:
theorem Closeds.compl_bijective
  statement: Function.Bijective (@Closeds.compl α _)
  proof: Function.bijective_iff_has_inverse.mpr ⟨Opens.compl, Closeds.compl_compl, Opens.compl_compl⟩

中文:
定理 Closeds.compl_bijective
  结论: 函数.双射 (@Closeds.compl α _)
  证明: Function.bijective_iff_has_inverse.mpr ⟨Opens.compl, Closeds.compl_compl, Opens.compl_compl⟩

Depends on / 依赖: Closeds, Closeds.compl_compl, Function, Function.bijective_iff_has_inverse.mpr, Opens.compl, Opens.compl_compl, bijective_iff_has_inverse, compl_compl
-/
theorem Closeds.compl_bijective : Function.Bijective (@Closeds.compl α _) :=
  Function.bijective_iff_has_inverse.mpr ⟨Opens.compl, Closeds.compl_compl, Opens.compl_compl⟩

/--
theorem `Opens.compl_bijective` / 定理 `Opens.compl_bijective`

English:
theorem Opens.compl_bijective
  statement: Function.Bijective (@Opens.compl α _)
  proof: Function.bijective_iff_has_inverse.mpr ⟨Closeds.compl, Opens.compl_compl, Closeds.compl_compl⟩

中文:
定理 Opens.compl_bijective
  结论: 函数.双射 (@Opens.compl α _)
  证明: Function.bijective_iff_has_inverse.mpr ⟨Closeds.compl, Opens.compl_compl, Closeds.compl_compl⟩

Depends on / 依赖: Closeds, Closeds.compl, Closeds.compl_compl, Function, Function.bijective_iff_has_inverse.mpr, Opens.compl_compl, bijective_iff_has_inverse, compl_compl
-/
theorem Opens.compl_bijective : Function.Bijective (@Opens.compl α _) :=
  Function.bijective_iff_has_inverse.mpr ⟨Closeds.compl, Opens.compl_compl, Closeds.compl_compl⟩

variable (α)

/-- `TopologicalSpace.Closeds.compl` as an `OrderIso` to the order dual of
`TopologicalSpace.Opens α`. -/
@[simps]
/--
Definition of `Closeds.complOrderIso` / `Closeds.complOrderIso` 的定义

English:
definition Closeds.complOrderIso
  signature: : Closeds α ≃o (Opens α)ᵒᵈ where
  body: OrderDual.toDual ∘ Closeds.compl
  invFun := Opens.compl ∘ OrderDual.ofDual
  left_inv s := by simp [Closeds.compl_compl]
  right_inv s := by simp [Opens.compl_compl]
  map_rel_iff' := (@OrderDual.toDual_le_toDual (Opens α)).trans compl_subset_compl

中文:
定义 Closeds.complOrderIso
  签名: : Closeds α ≃o (Opens α)ᵒᵈ where
  定义体: OrderDual.toDual ∘ Closeds.compl
  invFun := Opens.compl ∘ OrderDual.ofDual
  left_inv s := by simp [Closeds.compl_compl]
  right_inv s := by simp [Opens.compl_compl]
  map_rel_iff' := (@OrderDual.toDual_le_toDual (Opens α)).trans compl_subset_compl

Depends on / 依赖: Closeds, Closeds.compl, OrderDual, OrderDual.toDual, toDual
-/
def Closeds.complOrderIso : Closeds α ≃o (Opens α)ᵒᵈ where
  toFun := OrderDual.toDual ∘ Closeds.compl
  invFun := Opens.compl ∘ OrderDual.ofDual
  left_inv s := by simp [Closeds.compl_compl]
  right_inv s := by simp [Opens.compl_compl]
  map_rel_iff' := (@OrderDual.toDual_le_toDual (Opens α)).trans compl_subset_compl

/-- `TopologicalSpace.Opens.compl` as an `OrderIso` to the order dual of
`TopologicalSpace.Closeds α`. -/
@[simps]
/--
Definition of `Opens.complOrderIso` / `Opens.complOrderIso` 的定义

English:
definition Opens.complOrderIso
  signature: : Opens α ≃o (Closeds α)ᵒᵈ where
  body: OrderDual.toDual ∘ Opens.compl
  invFun := Closeds.compl ∘ OrderDual.ofDual
  left_inv s := by simp [Opens.compl_compl]
  right_inv s := by simp [Closeds.compl_compl]
  map_rel_iff' := (@OrderDual.toDual_le_toDual (Closeds α)).trans compl_subset_compl

中文:
定义 Opens.complOrderIso
  签名: : Opens α ≃o (Closeds α)ᵒᵈ where
  定义体: OrderDual.toDual ∘ Opens.compl
  invFun := Closeds.compl ∘ OrderDual.ofDual
  left_inv s := by simp [Opens.compl_compl]
  right_inv s := by simp [Closeds.compl_compl]
  map_rel_iff' := (@OrderDual.toDual_le_toDual (Closeds α)).trans compl_subset_compl

Depends on / 依赖: Opens.compl, OrderDual, OrderDual.toDual, toDual
-/
def Opens.complOrderIso : Opens α ≃o (Closeds α)ᵒᵈ where
  toFun := OrderDual.toDual ∘ Opens.compl
  invFun := Closeds.compl ∘ OrderDual.ofDual
  left_inv s := by simp [Opens.compl_compl]
  right_inv s := by simp [Closeds.compl_compl]
  map_rel_iff' := (@OrderDual.toDual_le_toDual (Closeds α)).trans compl_subset_compl

variable {α}

/--
lemma `Closeds.coe_eq_singleton_of_isAtom` / 引理 `Closeds.coe_eq_singleton_of_isAtom`

English:
lemma Closeds.coe_eq_singleton_of_isAtom
  given: [T0Space α] {s : Closeds α} (hs : IsAtom s)
  proof: by
  refine minimal_nonempty_closed_eq_singleton s.2 (coe_nonempty.2 hs.1) fun t hts ht ht' => ?_
  lift t to Closeds α using ht'
exact SetLike.coe_injective.eq_iff.2 (hs.le_iff_eq <| coe_nonempty.1 ht).1 hts

中文:
引理 Closeds.coe_eq_singleton_of_isAtom
  条件: [T0空间 α] {s : Closeds α} (hs : IsAtom s)
  证明: by
  refine minimal_nonempty_closed_eq_singleton s.2 (coe_nonempty.2 hs.1) fun t hts ht ht' => ?_
  lift t to Closeds α using ht'
exact SetLike.coe_injective.eq_iff.2 (hs.le_iff_eq <| coe_nonempty.1 ht).1 hts

Depends on / 依赖: Closeds, SetLike, SetLike.coe_injective.eq_iff, coe_injective, coe_nonempty, eq_iff, hs.le_iff_eq, le_iff_eq, minimal_nonempty_closed_eq_singleton
-/
lemma Closeds.coe_eq_singleton_of_isAtom [T0Space α] {s : Closeds α} (hs : IsAtom s) :
    exists a, (s : Set α) = {a} := by
  refine minimal_nonempty_closed_eq_singleton s.2 (coe_nonempty.2 hs.1) fun t hts ht ht' => ?_
  lift t to Closeds α using ht'
exact SetLike.coe_injective.eq_iff.2 (hs.le_iff_eq <| coe_nonempty.1 ht).1 hts

/--
lemma `Closeds.isAtom_coe` / 引理 `Closeds.isAtom_coe`

English:
lemma Closeds.isAtom_coe
  given: [T1Space α] {s : Closeds α}
  proof: Closeds.gi.isAtom_iff' rfl
    (fun t ht => by obtain ⟨x, rfl⟩ := Set.isAtom_iff.1 ht; exact closure_singleton) s

中文:
引理 Closeds.isAtom_coe
  条件: [T1空间 α] {s : Closeds α}
  证明: Closeds.gi.isAtom_iff' rfl
    (fun t ht => by obtain ⟨x, rfl⟩ := Set.isAtom_iff.1 ht; exact closure_singleton) s
-/
@[simp, norm_cast] lemma Closeds.isAtom_coe [T1Space α] {s : Closeds α} :
    IsAtom (s : Set α) ↔ IsAtom s :=
  Closeds.gi.isAtom_iff' rfl
    (fun t ht => by obtain ⟨x, rfl⟩ := Set.isAtom_iff.1 ht; exact closure_singleton) s

/--
theorem `Closeds.isAtom_iff` / 定理 `Closeds.isAtom_iff`

English:
theorem Closeds.isAtom_iff
  given: [T1Space α] {s : Closeds α}
  proof: by
  simp [← Closeds.isAtom_coe, Set.isAtom_iff, SetLike.ext_iff, Set.ext_iff]

中文:
定理 Closeds.isAtom_iff
  条件: [T1空间 α] {s : Closeds α}
  证明: by
  simp [← Closeds.isAtom_coe, Set.isAtom_iff, SetLike.ext_iff, Set.ext_iff]

Depends on / 依赖: Closeds, Closeds.isAtom_coe, Set.ext_iff, Set.isAtom_iff, SetLike, SetLike.ext_iff, ext_iff, isAtom_coe, isAtom_iff
-/
theorem Closeds.isAtom_iff [T1Space α] {s : Closeds α} :
    IsAtom s ↔ exists x, s = {x} := by
  simp [← Closeds.isAtom_coe, Set.isAtom_iff, SetLike.ext_iff, Set.ext_iff]

/--
theorem `Opens.isCoatom_iff` / 定理 `Opens.isCoatom_iff`

English:
theorem Opens.isCoatom_iff
  given: [T1Space α] {s : Opens α}
  proof: by
  rw [← s.compl_compl]; rw [← isAtom_dual_iff_isCoatom]
  change IsAtom (Closeds.complOrderIso α s.compl) ↔ _
  simp only [(Closeds.complOrderIso α).isAtom_iff, Closeds.isAtom_iff,
    Closeds.compl_bijective.injective.eq_iff]

中文:
定理 Opens.isCoatom_iff
  条件: [T1空间 α] {s : Opens α}
  证明: by
  rw [← s.compl_compl]; rw [← isAtom_dual_iff_isCoatom]
  change IsAtom (Closeds.complOrderIso α s.compl) ↔ _
  simp only [(Closeds.complOrderIso α).isAtom_iff, Closeds.isAtom_iff,
    Closeds.compl_bijective.injective.eq_iff]

Depends on / 依赖: Closeds, Closeds.complOrderIso, Closeds.compl_bijective.injective.eq_iff, Closeds.isAtom_iff, IsAtom, complOrderIso, compl_bijective, compl_compl, eq_iff, injective, isAtom_dual_iff_isCoatom, isAtom_iff, s.compl, s.compl_compl
-/
theorem Opens.isCoatom_iff [T1Space α] {s : Opens α} :
    IsCoatom s ↔ exists x, s = ({x} : Closeds α).compl := by
  rw [← s.compl_compl]; rw [← isAtom_dual_iff_isCoatom]
  change IsAtom (Closeds.complOrderIso α s.compl) ↔ _
  simp only [(Closeds.complOrderIso α).isAtom_iff, Closeds.isAtom_iff,
    Closeds.compl_bijective.injective.eq_iff]

/-! ### Clopen sets -/


/--
Definition of `Clopens` / `Clopens` 的定义

English:
structure Clopens
  parameters: (α : Type*) [TopologicalSpace α]
  axioms and operations (2):
    - carrier : Set α
    - isClopen' : IsClopen carrier

中文:
结构 Clopens
  参数: (α : 类型) [拓扑空间 α]
  公理与运算 (2 个):
    - carrier : 集合 α
    - isClopen' : IsClopen carrier
-/
structure Clopens (α : Type*) [TopologicalSpace α] where
  /-- the carrier set, i.e. the points in this set -/
  carrier : Set α
  isClopen' : IsClopen carrier

namespace Clopens

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (Clopens α) α
  body: s.carrier
  coe_injective s t h := by cases s; cases t; congr

中文:
实例 :
  签名: 集合状 (Clopens α) α
  定义体: s.carrier
  coe_injective s t h := by cases s; cases t; congr

Depends on / 依赖: carrier, s.carrier
-/
instance : SetLike (Clopens α) α where
  coe s := s.carrier
  coe_injective s t h := by cases s; cases t; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Clopens α)
  body: fast_instance% .ofSetLike (Clopens α) α

中文:
实例 :
  签名: 偏序 (Clopens α)
  定义体: fast_instance% .ofSetLike (Clopens α) α

Depends on / 依赖: Clopens, fast_instance, ofSetLike
-/
instance : PartialOrder (Clopens α) := fast_instance% .ofSetLike (Clopens α) α

/--
theorem `isClopen` / 定理 `isClopen`

English:
theorem isClopen
  given: (s : Clopens α)
  statement: IsClopen (s : Set α)
  proof: s.isClopen'

中文:
定理 isClopen
  条件: (s : Clopens α)
  结论: IsClopen (s : 集合 α)
  证明: s.isClopen'

Depends on / 依赖: isClopen, s.isClopen
-/
theorem isClopen (s : Clopens α) : IsClopen (s : Set α) :=
  s.isClopen'

/--
lemma `isOpen` / 引理 `isOpen`

English:
lemma isOpen
  given: (s : Clopens α)
  statement: IsOpen (s : Set α)
  proof: s.isClopen.isOpen

中文:
引理 isOpen
  条件: (s : Clopens α)
  结论: 是开集 (s : 集合 α)
  证明: s.isClopen.isOpen

Depends on / 依赖: isClopen, isOpen, s.isClopen.isOpen
-/
lemma isOpen (s : Clopens α) : IsOpen (s : Set α) := s.isClopen.isOpen

/--
lemma `isClosed` / 引理 `isClosed`

English:
lemma isClosed
  given: (s : Clopens α)
  statement: IsClosed (s : Set α)
  proof: s.isClopen.isClosed

中文:
引理 isClosed
  条件: (s : Clopens α)
  结论: 是闭集 (s : 集合 α)
  证明: s.isClopen.isClosed

Depends on / 依赖: isClopen, isClosed, s.isClopen.isClosed
-/
lemma isClosed (s : Clopens α) : IsClosed (s : Set α) := s.isClopen.isClosed

/--
Definition of `Simps.coe` / `Simps.coe` 的定义

English:
definition Simps.coe
  signature: (s : Clopens α)
  body: s

initialize_simps_projections Clopens (carrier -> coe, as_prefix coe)

中文:
定义 Simps.coe
  签名: (s : Clopens α)
  定义体: s

initialize_simps_projections Clopens (carrier -> coe, as_prefix coe)
-/
def Simps.coe (s : Clopens α) : Set α := s

initialize_simps_projections Clopens (carrier -> coe, as_prefix coe)

/--
Definition of `toOpens` / `toOpens` 的定义

English:
definition toOpens
  signature: (s : Clopens α)
  body: ⟨s, s.isOpen⟩

中文:
定义 toOpens
  签名: (s : Clopens α)
  定义体: ⟨s, s.isOpen⟩
-/
@[simps] def toOpens (s : Clopens α) : Opens α := ⟨s, s.isOpen⟩

/--
Definition of `toCloseds` / `toCloseds` 的定义

English:
definition toCloseds
  signature: (s : Clopens α)
  body: ⟨s, s.isClosed⟩

@[ext]

中文:
定义 toCloseds
  签名: (s : Clopens α)
  定义体: ⟨s, s.isClosed⟩

@[ext]
-/
@[simps] def toCloseds (s : Clopens α) : Closeds α := ⟨s, s.isClosed⟩

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {s t : Clopens α} (h : (s : Set α) = t)
  statement: s = t
  proof: SetLike.ext' h

@[simp]

中文:
定理 ext
  条件: {s t : Clopens α} (h : (s : 集合 α) = t)
  结论: s = t
  证明: SetLike.ext' h

@[simp]
-/
protected theorem ext {s t : Clopens α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (s : Set α) (h)
  statement: (mk s h : Set α) = s
  proof: rfl

中文:
定理 coe_mk
  条件: (s : 集合 α) (h)
  结论: (mk s h : 集合 α) = s
  证明: rfl
-/
theorem coe_mk (s : Set α) (h) : (mk s h : Set α) = s :=
  rfl

/--
lemma `mem_mk` / 引理 `mem_mk`

English:
lemma mem_mk
  given: {s : Set α} {x h}
  statement: x in mk s h ↔ x in s
  proof: .rfl

中文:
引理 mem_mk
  条件: {s : 集合 α} {x h}
  结论: x in mk s h ↔ x in s
  证明: .rfl
-/
@[simp] lemma mem_mk {s : Set α} {x h} : x in mk s h ↔ x in s := .rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (Clopens α)
  body: ⟨fun s t => ⟨s union t, s.isClopen.union t.isClopen⟩⟩

中文:
实例 :
  签名: 最大值 (Clopens α)
  定义体: ⟨fun s t => ⟨s union t, s.isClopen.union t.isClopen⟩⟩

Depends on / 依赖: isClopen, s.isClopen.union, t.isClopen
-/
instance : Max (Clopens α) := ⟨fun s t => ⟨s union t, s.isClopen.union t.isClopen⟩⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (Clopens α)
  body: ⟨fun s t => ⟨s inter t, s.isClopen.inter t.isClopen⟩⟩

中文:
实例 :
  签名: 最小值 (Clopens α)
  定义体: ⟨fun s t => ⟨s inter t, s.isClopen.inter t.isClopen⟩⟩

Depends on / 依赖: isClopen, s.isClopen.inter, t.isClopen
-/
instance : Min (Clopens α) := ⟨fun s t => ⟨s inter t, s.isClopen.inter t.isClopen⟩⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (Clopens α)
  body: ⟨⟨⊤, isClopen_univ⟩⟩

中文:
实例 :
  签名: 顶元素 (Clopens α)
  定义体: ⟨⟨⊤, isClopen_univ⟩⟩

Depends on / 依赖: isClopen_univ
-/
instance : Top (Clopens α) := ⟨⟨⊤, isClopen_univ⟩⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (Clopens α)
  body: ⟨⟨⊥, isClopen_empty⟩⟩

中文:
实例 :
  签名: 底元素 (Clopens α)
  定义体: ⟨⟨⊥, isClopen_empty⟩⟩

Depends on / 依赖: isClopen_empty
-/
instance : Bot (Clopens α) := ⟨⟨⊥, isClopen_empty⟩⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SDiff (Clopens α)
  body: ⟨fun s t => ⟨s \ t, s.isClopen.diff t.isClopen⟩⟩

中文:
实例 :
  签名: 对称差 (Clopens α)
  定义体: ⟨fun s t => ⟨s \ t, s.isClopen.diff t.isClopen⟩⟩

Depends on / 依赖: isClopen, s.isClopen.diff, t.isClopen
-/
instance : SDiff (Clopens α) := ⟨fun s t => ⟨s \ t, s.isClopen.diff t.isClopen⟩⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HImp (Clopens α)
  body: ⟨s ⇨ t, s.isClopen.himp t.isClopen⟩

中文:
实例 :
  签名: HImp (Clopens α)
  定义体: ⟨s ⇨ t, s.isClopen.himp t.isClopen⟩

Depends on / 依赖: isClopen, s.isClopen.himp, t.isClopen
-/
instance : HImp (Clopens α) where himp s t := ⟨s ⇨ t, s.isClopen.himp t.isClopen⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Compl (Clopens α)
  body: ⟨fun s => ⟨sᶜ, s.isClopen.compl⟩⟩

中文:
实例 :
  签名: 补集 (Clopens α)
  定义体: ⟨fun s => ⟨sᶜ, s.isClopen.compl⟩⟩

Depends on / 依赖: isClopen, s.isClopen.compl
-/
instance : Compl (Clopens α) := ⟨fun s => ⟨sᶜ, s.isClopen.compl⟩⟩

/--
lemma `coe_sup` / 引理 `coe_sup`

English:
lemma coe_sup
  given: (s t : Clopens α)
  statement: ↑(s ⊔ t) = (s union t : Set α)
  proof: rfl

中文:
引理 coe_sup
  条件: (s t : Clopens α)
  结论: ↑(s ⊔ t) = (s union t : 集合 α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_sup (s t : Clopens α) : ↑(s ⊔ t) = (s union t : Set α) := rfl
/--
lemma `coe_inf` / 引理 `coe_inf`

English:
lemma coe_inf
  given: (s t : Clopens α)
  statement: ↑(s ⊓ t) = (s inter t : Set α)
  proof: rfl

中文:
引理 coe_inf
  条件: (s t : Clopens α)
  结论: ↑(s ⊓ t) = (s inter t : 集合 α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_inf (s t : Clopens α) : ↑(s ⊓ t) = (s inter t : Set α) := rfl
/--
lemma `coe_top` / 引理 `coe_top`

English:
lemma coe_top
  statement: (↑(⊤ : Clopens α) : Set α) = univ
  proof: rfl

中文:
引理 coe_top
  结论: (↑(⊤ : Clopens α) : 集合 α) = univ
  证明: rfl
-/
@[simp, norm_cast] lemma coe_top : (↑(⊤ : Clopens α) : Set α) = univ := rfl
/--
lemma `coe_bot` / 引理 `coe_bot`

English:
lemma coe_bot
  statement: (↑(⊥ : Clopens α) : Set α) = ∅
  proof: rfl

中文:
引理 coe_bot
  结论: (↑(⊥ : Clopens α) : 集合 α) = ∅
  证明: rfl
-/
@[simp, norm_cast] lemma coe_bot : (↑(⊥ : Clopens α) : Set α) = ∅ := rfl
/--
lemma `coe_sdiff` / 引理 `coe_sdiff`

English:
lemma coe_sdiff
  given: (s t : Clopens α)
  statement: ↑(s \ t) = (s \ t : Set α)
  proof: rfl

中文:
引理 coe_sdiff
  条件: (s t : Clopens α)
  结论: ↑(s \ t) = (s \ t : 集合 α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_sdiff (s t : Clopens α) : ↑(s \ t) = (s \ t : Set α) := rfl
/--
lemma `coe_himp` / 引理 `coe_himp`

English:
lemma coe_himp
  given: (s t : Clopens α)
  statement: ↑(s ⇨ t) = (s ⇨ t : Set α)
  proof: rfl

中文:
引理 coe_himp
  条件: (s t : Clopens α)
  结论: ↑(s ⇨ t) = (s ⇨ t : 集合 α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_himp (s t : Clopens α) : ↑(s ⇨ t) = (s ⇨ t : Set α) := rfl
/--
lemma `coe_compl` / 引理 `coe_compl`

English:
lemma coe_compl
  given: (s : Clopens α)
  statement: (↑sᶜ : Set α) = (↑s)ᶜ
  proof: rfl

中文:
引理 coe_compl
  条件: (s : Clopens α)
  结论: (↑sᶜ : 集合 α) = (↑s)ᶜ
  证明: rfl
-/
@[simp, norm_cast] lemma coe_compl (s : Clopens α) : (↑sᶜ : Set α) = (↑s)ᶜ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BooleanAlgebra (Clopens α)
  body: fast_instance%
  SetLike.coe_injective.booleanAlgebra _ .rfl .rfl coe_sup coe_inf coe_top coe_bot coe_compl
    coe_sdiff coe_himp

中文:
实例 :
  签名: 布尔代数 (Clopens α)
  定义体: fast_instance%
  SetLike.coe_injective.booleanAlgebra _ .rfl .rfl coe_sup coe_inf coe_top coe_bot coe_compl
    coe_sdiff coe_himp

Depends on / 依赖: fast_instance
-/
instance : BooleanAlgebra (Clopens α) := fast_instance%
  SetLike.coe_injective.booleanAlgebra _ .rfl .rfl coe_sup coe_inf coe_top coe_bot coe_compl
    coe_sdiff coe_himp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Clopens α)
  body: ⟨⊥⟩

中文:
实例 :
  签名: 可居 (Clopens α)
  定义体: ⟨⊥⟩
-/
instance : Inhabited (Clopens α) := ⟨⊥⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SProd (Clopens α) (Clopens β) (Clopens (α × β))
  body: ⟨s ×ˢ t, s.2.prod t.2⟩

@[simp]

中文:
实例 :
  签名: SProd (Clopens α) (Clopens β) (Clopens (α × β))
  定义体: ⟨s ×ˢ t, s.2.prod t.2⟩

@[simp]
-/
instance : SProd (Clopens α) (Clopens β) (Clopens (α × β)) where
  sprod s t := ⟨s ×ˢ t, s.2.prod t.2⟩

@[simp]
/--
lemma `mem_prod` / 引理 `mem_prod`

English:
lemma mem_prod
  given: {s : Clopens α} {t : Clopens β} {x : α × β}
  proof: .rfl

@[simp]

中文:
引理 mem_prod
  条件: {s : Clopens α} {t : Clopens β} {x : α × β}
  证明: .rfl

@[simp]
-/
protected lemma mem_prod {s : Clopens α} {t : Clopens β} {x : α × β} :
    x in s ×ˢ t ↔ x.1 in s ∧ x.2 in t := .rfl

@[simp]
/--
lemma `coe_finset_sup` / 引理 `coe_finset_sup`

English:
lemma coe_finset_sup
  given: (s : Finset ι) (U : ι -> Clopens α)
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ _ IH => simp [IH]

@[simp, norm_cast]

中文:
引理 coe_finset_sup
  条件: (s : 有限集 ι) (U : ι -> Clopens α)
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ _ IH => simp [IH]

@[simp, norm_cast]

Depends on / 依赖: Finset, Finset.induction_on, classical, induction_on, insert
-/
lemma coe_finset_sup (s : Finset ι) (U : ι -> Clopens α) :
    (↑(s.sup U) : Set α) = ⋃ i in s, U i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ _ IH => simp [IH]

@[simp, norm_cast]
/--
lemma `coe_disjoint` / 引理 `coe_disjoint`

English:
lemma coe_disjoint
  given: {s t : Clopens α}
  statement: Disjoint (s : Set α) t ↔ Disjoint s t
  proof: by
  simp [disjoint_iff, ← SetLike.coe_set_eq]

中文:
引理 coe_disjoint
  条件: {s t : Clopens α}
  结论: Disjoint (s : 集合 α) t ↔ Disjoint s t
  证明: by
  simp [disjoint_iff, ← SetLike.coe_set_eq]

Depends on / 依赖: SetLike, SetLike.coe_set_eq, coe_set_eq, disjoint_iff
-/
lemma coe_disjoint {s t : Clopens α} : Disjoint (s : Set α) t ↔ Disjoint s t := by
  simp [disjoint_iff, ← SetLike.coe_set_eq]

end Clopens

/-! ### Irreducible closed sets -/

/--
Definition of `IrreducibleCloseds` / `IrreducibleCloseds` 的定义

English:
structure IrreducibleCloseds
  parameters: (α : Type*) [TopologicalSpace α]
  axioms and operations (3):
    - carrier : Set α
    - isIrreducible' : IsIrreducible carrier
    - isClosed' : IsClosed carrier

中文:
结构 IrreducibleCloseds
  参数: (α : 类型) [拓扑空间 α]
  公理与运算 (3 个):
    - carrier : 集合 α
    - isIrreducible' : 是不可约 carrier
    - isClosed' : 是闭集 carrier
-/
structure IrreducibleCloseds (α : Type*) [TopologicalSpace α] where
  /-- the carrier set, i.e. the points in this set -/
  carrier : Set α
  isIrreducible' : IsIrreducible carrier
  isClosed' : IsClosed carrier

namespace IrreducibleCloseds

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (IrreducibleCloseds α) α
  body: IrreducibleCloseds.carrier
  coe_injective s t h := by cases s; cases t; congr

中文:
实例 :
  签名: 集合状 (IrreducibleCloseds α) α
  定义体: IrreducibleCloseds.carrier
  coe_injective s t h := by cases s; cases t; congr

Depends on / 依赖: IrreducibleCloseds, IrreducibleCloseds.carrier, carrier
-/
instance : SetLike (IrreducibleCloseds α) α where
  coe := IrreducibleCloseds.carrier
  coe_injective s t h := by cases s; cases t; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (IrreducibleCloseds α)
  body: fast_instance% .ofSetLike (IrreducibleCloseds α) α

中文:
实例 :
  签名: 偏序 (IrreducibleCloseds α)
  定义体: fast_instance% .ofSetLike (IrreducibleCloseds α) α

Depends on / 依赖: IrreducibleCloseds, fast_instance, ofSetLike
-/
instance : PartialOrder (IrreducibleCloseds α) := fast_instance% .ofSetLike (IrreducibleCloseds α) α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanLift (Set α) (IrreducibleCloseds α) (↑) (fun s => IsIrreducible s ∧ IsClosed s)
  body: ⟨⟨s, hs.1, hs.2⟩, rfl⟩

中文:
实例 :
  签名: CanLift (集合 α) (IrreducibleCloseds α) (↑) (fun s => 是不可约 s ∧ 是闭集 s)
  定义体: ⟨⟨s, hs.1, hs.2⟩, rfl⟩
-/
instance : CanLift (Set α) (IrreducibleCloseds α) (↑) (fun s => IsIrreducible s ∧ IsClosed s) where
  prf s hs := ⟨⟨s, hs.1, hs.2⟩, rfl⟩

/--
theorem `isIrreducible` / 定理 `isIrreducible`

English:
theorem isIrreducible
  given: (s : IrreducibleCloseds α)
  statement: IsIrreducible (s : Set α)
  proof: s.isIrreducible'

中文:
定理 isIrreducible
  条件: (s : IrreducibleCloseds α)
  结论: 是不可约 (s : 集合 α)
  证明: s.isIrreducible'

Depends on / 依赖: isIrreducible, s.isIrreducible
-/
theorem isIrreducible (s : IrreducibleCloseds α) : IsIrreducible (s : Set α) := s.isIrreducible'

/--
theorem `isClosed` / 定理 `isClosed`

English:
theorem isClosed
  given: (s : IrreducibleCloseds α)
  statement: IsClosed (s : Set α)
  proof: s.isClosed'

中文:
定理 isClosed
  条件: (s : IrreducibleCloseds α)
  结论: 是闭集 (s : 集合 α)
  证明: s.isClosed'

Depends on / 依赖: isClosed, s.isClosed
-/
theorem isClosed (s : IrreducibleCloseds α) : IsClosed (s : Set α) := s.isClosed'

/--
Definition of `Simps.coe` / `Simps.coe` 的定义

English:
definition Simps.coe
  signature: (s : IrreducibleCloseds α)
  body: s

initialize_simps_projections IrreducibleCloseds (carrier -> coe, as_prefix coe)

@[ext]

中文:
定义 Simps.coe
  签名: (s : IrreducibleCloseds α)
  定义体: s

initialize_simps_projections IrreducibleCloseds (carrier -> coe, as_prefix coe)

@[ext]
-/
def Simps.coe (s : IrreducibleCloseds α) : Set α := s

initialize_simps_projections IrreducibleCloseds (carrier -> coe, as_prefix coe)

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {s t : IrreducibleCloseds α} (h : (s : Set α) = t)
  statement: s = t
  proof: SetLike.ext' h

@[simp]

中文:
定理 ext
  条件: {s t : IrreducibleCloseds α} (h : (s : 集合 α) = t)
  结论: s = t
  证明: SetLike.ext' h

@[simp]
-/
protected theorem ext {s t : IrreducibleCloseds α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (s : Set α) (h : IsIrreducible s) (h' : IsClosed s)
  statement: (mk s h h' : Set α) = s
  proof: rfl

@[simps]

中文:
定理 coe_mk
  条件: (s : 集合 α) (h : 是不可约 s) (h' : 是闭集 s)
  结论: (mk s h h' : 集合 α) = s
  证明: rfl

@[simps]
-/
theorem coe_mk (s : Set α) (h : IsIrreducible s) (h' : IsClosed s) : (mk s h h' : Set α) = s :=
  rfl

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T1Space
  signature: α] : Singleton α (IrreducibleCloseds α) where
  body: ⟨{x}, isIrreducible_singleton, isClosed_singleton⟩

@[simp]

中文:
实例 [T1空间
  签名: α] : 单例 α (IrreducibleCloseds α) where
  定义体: ⟨{x}, isIrreducible_singleton, isClosed_singleton⟩

@[simp]

Depends on / 依赖: isClosed_singleton, isIrreducible_singleton
-/
instance [T1Space α] : Singleton α (IrreducibleCloseds α) where
  singleton x := ⟨{x}, isIrreducible_singleton, isClosed_singleton⟩

@[simp]
/--
theorem `mk_singleton` / 定理 `mk_singleton`

English:
theorem mk_singleton
  given: [T1Space α] {x : α}
  proof: rfl

中文:
定理 mk_singleton
  条件: [T1空间 α] {x : α}
  证明: rfl
-/
theorem mk_singleton [T1Space α] {x : α} :
    (⟨{x}, isIrreducible_singleton, isClosed_singleton⟩ : IrreducibleCloseds α) = {x} :=
  rfl

/--
lemma `mem_singleton` / 引理 `mem_singleton`

English:
lemma mem_singleton
  given: [T1Space α] {a b : α}
  statement: a in ({b} : IrreducibleCloseds α) ↔ a = b
  proof: Iff.rfl

中文:
引理 mem_singleton
  条件: [T1空间 α] {a b : α}
  结论: a in ({b} : IrreducibleCloseds α) ↔ a = b
  证明: Iff.rfl
-/
@[simp] lemma mem_singleton [T1Space α] {a b : α} : a in ({b} : IrreducibleCloseds α) ↔ a = b :=
  Iff.rfl

/--
theorem `singleton_injective` / 定理 `singleton_injective`

English:
theorem singleton_injective
  given: [T1Space α]
  statement: Function.Injective ({·} : α -> IrreducibleCloseds α)
  proof: .of_comp (f := SetLike.coe) Set.singleton_injective

@[simp]

中文:
定理 singleton_injective
  条件: [T1空间 α]
  结论: 函数.单射 ({·} : α -> IrreducibleCloseds α)
  证明: .of_comp (f := SetLike.coe) Set.singleton_injective

@[simp]

Depends on / 依赖: Set.singleton_injective, SetLike, SetLike.coe, of_comp, singleton_injective
-/
theorem singleton_injective [T1Space α] : Function.Injective ({·} : α -> IrreducibleCloseds α) :=
  .of_comp (f := SetLike.coe) Set.singleton_injective

@[simp]
/--
theorem `singleton_inj` / 定理 `singleton_inj`

English:
theorem singleton_inj
  given: [T1Space α] {x y : α}
  statement: ({x} : IrreducibleCloseds α) = {y} ↔ x = y
  proof: singleton_injective.eq_iff

中文:
定理 singleton_inj
  条件: [T1空间 α] {x y : α}
  结论: ({x} : IrreducibleCloseds α) = {y} ↔ x = y
  证明: singleton_injective.eq_iff

Depends on / 依赖: eq_iff, singleton_injective, singleton_injective.eq_iff
-/
theorem singleton_inj [T1Space α] {x y : α} : ({x} : IrreducibleCloseds α) = {y} ↔ x = y :=
  singleton_injective.eq_iff

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
The equivalence between `IrreducibleCloseds α` and `{x : Set α // IsIrreducible x ∧ IsClosed x }`.
-/
@[simps apply symm_apply]
/--
Definition of `equivSubtype` / `equivSubtype` 的定义

English:
definition equivSubtype
  signature: : IrreducibleCloseds α ≃ { x : Set α // IsIrreducible x ∧ IsClosed x } where
  body: ⟨a.1, a.2, a.3⟩
  invFun a := ⟨a.1, a.2.1, a.2.2⟩

中文:
定义 equivSubtype
  签名: : IrreducibleCloseds α ≃ { x : 集合 α // 是不可约 x ∧ 是闭集 x } where
  定义体: ⟨a.1, a.2, a.3⟩
  invFun a := ⟨a.1, a.2.1, a.2.2⟩
-/
def equivSubtype : IrreducibleCloseds α ≃ { x : Set α // IsIrreducible x ∧ IsClosed x } where
  toFun a := ⟨a.1, a.2, a.3⟩
  invFun a := ⟨a.1, a.2.1, a.2.2⟩

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
The equivalence between `IrreducibleCloseds α` and `{x : Set α // IsClosed x ∧ IsIrreducible x }`.
-/
@[simps apply symm_apply]
/--
Definition of `equivSubtype'` / `equivSubtype'` 的定义

English:
definition equivSubtype'
  signature: : IrreducibleCloseds α ≃ { x : Set α // IsClosed x ∧ IsIrreducible x } where
  body: ⟨a.1, a.3, a.2⟩
  invFun a := ⟨a.1, a.2.2, a.2.1⟩

中文:
定义 equivSubtype'
  签名: : IrreducibleCloseds α ≃ { x : 集合 α // 是闭集 x ∧ 是不可约 x } where
  定义体: ⟨a.1, a.3, a.2⟩
  invFun a := ⟨a.1, a.2.2, a.2.1⟩
-/
def equivSubtype' : IrreducibleCloseds α ≃ { x : Set α // IsClosed x ∧ IsIrreducible x } where
  toFun a := ⟨a.1, a.3, a.2⟩
  invFun a := ⟨a.1, a.2.2, a.2.1⟩

variable (α) in
/--
Definition of `orderIsoSubtype` / `orderIsoSubtype` 的定义

English:
definition orderIsoSubtype
  signature: : IrreducibleCloseds α ≃o { x : Set α // IsIrreducible x ∧ IsClosed x }
  body: equivSubtype.toOrderIso (fun _ _ h => h) (fun _ _ h => h)

中文:
定义 orderIsoSubtype
  签名: : IrreducibleCloseds α ≃o { x : 集合 α // 是不可约 x ∧ 是闭集 x }
  定义体: equivSubtype.toOrderIso (fun _ _ h => h) (fun _ _ h => h)

Depends on / 依赖: equivSubtype, equivSubtype.toOrderIso, toOrderIso
-/
def orderIsoSubtype : IrreducibleCloseds α ≃o { x : Set α // IsIrreducible x ∧ IsClosed x } :=
  equivSubtype.toOrderIso (fun _ _ h => h) (fun _ _ h => h)

variable (α) in
/--
Definition of `orderIsoSubtype'` / `orderIsoSubtype'` 的定义

English:
definition orderIsoSubtype'
  signature: : IrreducibleCloseds α ≃o { x : Set α // IsClosed x ∧ IsIrreducible x }
  body: equivSubtype'.toOrderIso (fun _ _ h => h) (fun _ _ h => h)

中文:
定义 orderIsoSubtype'
  签名: : IrreducibleCloseds α ≃o { x : 集合 α // 是闭集 x ∧ 是不可约 x }
  定义体: equivSubtype'.toOrderIso (fun _ _ h => h) (fun _ _ h => h)

Depends on / 依赖: equivSubtype, toOrderIso
-/
def orderIsoSubtype' : IrreducibleCloseds α ≃o { x : Set α // IsClosed x ∧ IsIrreducible x } :=
  equivSubtype'.toOrderIso (fun _ _ h => h) (fun _ _ h => h)

/-! ### Partial order structure on irreducible closed sets and maps thereof.-/

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : β -> α) (hf : Continuous f)
  body: closure (f '' c)
.closure isIrreducible' := c.isIrreducible.image f hf.continuousOn
  isClosed' := isClosed_closure

@[simp]

中文:
定义 map
  签名: (f : β -> α) (hf : 连续 f)
  定义体: closure (f '' c)
.closure isIrreducible' := c.isIrreducible.image f hf.continuousOn
  isClosed' := isClosed_closure

@[simp]

Depends on / 依赖: closure
-/
def map (f : β -> α) (hf : Continuous f)
    (c : IrreducibleCloseds β) : IrreducibleCloseds α where
  carrier := closure (f '' c)
.closure isIrreducible' := c.isIrreducible.image f hf.continuousOn
  isClosed' := isClosed_closure

@[simp]
/--
lemma `coe_map` / 引理 `coe_map`

English:
lemma coe_map
  given: (f : β -> α) (hf : Continuous f) (s : IrreducibleCloseds β)
  proof: rfl

中文:
引理 coe_map
  条件: (f : β -> α) (hf : 连续 f) (s : IrreducibleCloseds β)
  证明: rfl
-/
lemma coe_map (f : β -> α) (hf : Continuous f) (s : IrreducibleCloseds β) :
    (map f hf s : Set α) = closure (f '' s) :=
  rfl

/--
lemma `map_mono` / 引理 `map_mono`

English:
lemma map_mono
  given: {f : β -> α} (hf : Continuous f)
  statement: Monotone (map f hf)
  proof: fun _ _ h_le => closure_mono Set.image_mono h_le

中文:
引理 map_mono
  条件: {f : β -> α} (hf : 连续 f)
  结论: 递增 (map f hf)
  证明: fun _ _ h_le => closure_mono Set.image_mono h_le

Depends on / 依赖: Set.image_mono, closure_mono, h_le, image_mono
-/
lemma map_mono {f : β -> α} (hf : Continuous f) : Monotone (map f hf) :=
fun _ _ h_le => closure_mono Set.image_mono h_le

/--
lemma `map_injective_of_isInducing` / 引理 `map_injective_of_isInducing`

English:
lemma map_injective_of_isInducing
  given: {f : β -> α} (hf : IsInducing f)
  proof: by
  intro A B h_images_eq
  apply SetLike.coe_injective
  replace h_images_eq : closure (f '' A) = closure (f '' B) := congr($h_images_eq)
  rw [← A.isClosed.closure_eq]; rw [hf.closure_eq_preimage_closure_image]; rw [h_images_eq]; rw [← hf.closure_eq_preimage_closure_image]; rw [B.isClosed.closure

中文:
引理 map_injective_of_isInducing
  条件: {f : β -> α} (hf : 是Inducing f)
  证明: by
  intro A B h_images_eq
  apply SetLike.coe_injective
  replace h_images_eq : closure (f '' A) = closure (f '' B) := congr($h_images_eq)
  rw [← A.isClosed.closure_eq]; rw [hf.closure_eq_preimage_closure_image]; rw [h_images_eq]; rw [← hf.closure_eq_preimage_closure_image]; rw [B.isClosed.closure

Depends on / 依赖: A.isClosed.closure_eq, B.isClosed.closure_eq, SetLike, SetLike.coe_injective, closure, closure_eq, closure_eq_preimage_closure_image, coe_injective, h_images_eq, hf.closure_eq_preimage_closure_image, isClosed, replace
-/
lemma map_injective_of_isInducing {f : β -> α} (hf : IsInducing f) :
    Function.Injective (map f hf.continuous) := by
  intro A B h_images_eq
  apply SetLike.coe_injective
  replace h_images_eq : closure (f '' A) = closure (f '' B) := congr($h_images_eq)
  rw [← A.isClosed.closure_eq]; rw [hf.closure_eq_preimage_closure_image]; rw [h_images_eq]; rw [← hf.closure_eq_preimage_closure_image]; rw [B.isClosed.closure_eq]

/--
lemma `map_strictMono_of_isInducing` / 引理 `map_strictMono_of_isInducing`

English:
lemma map_strictMono_of_isInducing
  given: {f : β -> α} (hf : IsInducing f)
  proof: Monotone.strictMono_of_injective (map_mono hf.continuous) (map_injective_of_isInducing hf)

中文:
引理 map_strictMono_of_isInducing
  条件: {f : β -> α} (hf : 是Inducing f)
  证明: Monotone.strictMono_of_injective (map_mono hf.continuous) (map_injective_of_isInducing hf)

Depends on / 依赖: Monotone, Monotone.strictMono_of_injective, continuous, hf.continuous, map_injective_of_isInducing, map_mono, strictMono_of_injective
-/
lemma map_strictMono_of_isInducing {f : β -> α} (hf : IsInducing f) :
    StrictMono (map f hf.continuous) :=
  Monotone.strictMono_of_injective (map_mono hf.continuous) (map_injective_of_isInducing hf)

set_option backward.isDefEq.respectTransparency false in
/--
Given `f : U → X` a continuous open embedding, the irreducible closeds of `U` are order isomorphic
to the irreducible closeds of `X` nontrivially intersecting the range of `f`.
-/
noncomputable
/--
Definition of `orderIsoOfIsOpenEmbedding` / `orderIsoOfIsOpenEmbedding` 的定义

English:
definition orderIsoOfIsOpenEmbedding
  signature: (f : β -> α) (h : IsOpenEmbedding f)
  body: ⟨map f h.continuous T, nonempty_preimage_closure_image h.continuous T T.2.nonempty⟩
  invFun V :=
    { carrier := f ⁻¹' V
      isIrreducible' := ⟨V.2, V.1.2.isPreirreducible.preimage h⟩
      isClosed' := V.1.3.preimage h.continuous }
  left_inv V := by
    ext
    simp [h.isOpenMap.preimage_closu

中文:
定义 orderIsoOfIsOpenEmbedding
  签名: (f : β -> α) (h : 是开嵌入 f)
  定义体: ⟨map f h.continuous T, nonempty_preimage_closure_image h.continuous T T.2.nonempty⟩
  invFun V :=
    { carrier := f ⁻¹' V
      isIrreducible' := ⟨V.2, V.1.2.isPreirreducible.preimage h⟩
      isClosed' := V.1.3.preimage h.continuous }
  left_inv V := by
    ext
    simp [h.isOpenMap.preimage_closu

Depends on / 依赖: continuous, h.continuous, nonempty, nonempty_preimage_closure_image
-/
def orderIsoOfIsOpenEmbedding (f : β -> α) (h : IsOpenEmbedding f) :
    IrreducibleCloseds β ≃o {V : IrreducibleCloseds α | (f ⁻¹' V).Nonempty} where
  toFun T := ⟨map f h.continuous T, nonempty_preimage_closure_image h.continuous T T.2.nonempty⟩
  invFun V :=
    { carrier := f ⁻¹' V
      isIrreducible' := ⟨V.2, V.1.2.isPreirreducible.preimage h⟩
      isClosed' := V.1.3.preimage h.continuous }
  left_inv V := by
    ext
    simp [h.isOpenMap.preimage_closure_image h.injective h.continuous _ V.isClosed]
  right_inv V := by
    ext
    simp [closure_image_preimage_of_isPreirreducible f h.isOpenMap V V.2 V.1.2.2 V.1.3]
  map_rel_iff' {a b} := by
    refine ⟨fun hle => ?_, fun hle => map_mono h.continuous hle⟩
    simpa [← h.isEmbedding.closure_eq_preimage_closure_image, a.isClosed.closure_eq,
      b.isClosed.closure_eq] using Set.preimage_mono (f := f) hle

end IrreducibleCloseds

end TopologicalSpace
