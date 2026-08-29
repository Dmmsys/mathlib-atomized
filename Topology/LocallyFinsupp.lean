/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Support
public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Data.Int.Cast.Pi
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Tactic.Peel

/-!
# Type of functions with locally finite support

This file defines functions with locally finite support, provides supporting API. For suitable
targets, it establishes functions with locally finite support as an instance of a lattice ordered
commutative group.

Throughout the present file, `X` denotes a topologically space and `U` a subset of `X`.
-/

@[expose] public section

open Filter Function Set Topology

variable
  {X : Type*} [TopologicalSpace X] {U : Set X}
  {Y : Type*}

/-!
## Definition, coercion to functions and basic extensionality lemmas

A function with locally finite support within `U` is a function `X → Y` whose support is locally
finite within `U` and entirely contained in `U`. For T1-spaces, the theorem
`supportDiscreteWithin_iff_locallyFiniteWithin` shows that the first condition is equivalent to the
condition that the support `f` is discrete within `U`.
-/

variable (U Y) in
/--
Definition of `Function.locallyFinsuppWithin` / `Function.locallyFinsuppWithin` 的定义

English:
structure Function.locallyFinsuppWithin
  parameters: [Zero Y]
  axioms and operations (3):
    - toFun : X -> Y
    - supportWithinDomain' : toFun.support subseteq U
    - supportLocallyFiniteWithinDomain' : forall z in U, exists t in 𝓝 z, Set.Finite (t inter toFun.support)

中文:
结构 Function.locallyFinsuppWithin
  参数: [Zero Y]
  公理与运算 (3 个):
    - toFun : X -> Y
    - supportWithinDomain' : toFun.support subseteq U
    - supportLocallyFiniteWithinDomain' : 对任意 z in U, 存在 t in 𝓝 z, Set.Finite (t inter toFun.support)
-/
structure Function.locallyFinsuppWithin [Zero Y] where
  /-- A function `X → Y` -/
  toFun : X -> Y
  /-- A proof that the support of `toFun` is contained in `U` -/
  supportWithinDomain' : toFun.support subseteq U
  /-- A proof that the support is locally finite within `U` -/
  supportLocallyFiniteWithinDomain' : forall z in U, exists t in 𝓝 z, Set.Finite (t inter toFun.support)

variable (X Y) in
/--
Definition of `Function.locallyFinsupp` / `Function.locallyFinsupp` 的定义

English:
abbreviation Function.locallyFinsupp
  signature: [Zero Y]
  body: locallyFinsuppWithin (Set.univ : Set X) Y

中文:
缩写 Function.locallyFinsupp
  签名: [Zero Y]
  定义体: locallyFinsuppWithin (Set.univ : Set X) Y

Depends on / 依赖: Set.univ, locallyFinsuppWithin
-/
abbrev Function.locallyFinsupp [Zero Y] := locallyFinsuppWithin (Set.univ : Set X) Y

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: Y] : Zero (locallyFinsuppWithin U Y) where
  body: { toFun := fun _ => 0
      supportWithinDomain' := by simp
      supportLocallyFiniteWithinDomain' z hz := by
        simp_rw [support_fun_zero, inter_empty, finite_empty, and_true]
        use Set.univ, univ_mem }

中文:
实例 [Zero
  签名: Y] : Zero (locallyFinsuppWithin U Y) where
  定义体: { toFun := fun _ => 0
      supportWithinDomain' := by simp
      supportLocallyFiniteWithinDomain' z hz := by
        simp_rw [support_fun_zero, inter_empty, finite_empty, and_true]
        use Set.univ, univ_mem }

Depends on / 依赖: Set.univ, and_true, finite_empty, inter_empty, simp_rw, supportLocallyFiniteWithinDomain, supportWithinDomain, support_fun_zero, univ_mem
-/
instance [Zero Y] : Zero (locallyFinsuppWithin U Y) where
  zero :=
    { toFun := fun _ => 0
      supportWithinDomain' := by simp
      supportLocallyFiniteWithinDomain' z hz := by
        simp_rw [support_fun_zero, inter_empty, finite_empty, and_true]
        use Set.univ, univ_mem }

/--
theorem `supportDiscreteWithin_iff_locallyFiniteWithin` / 定理 `supportDiscreteWithin_iff_locallyFiniteWithin`

English:
theorem supportDiscreteWithin_iff_locallyFiniteWithin
  statement: [T1Space X] [Zero Y] {f : X -> Y}
  proof: by
  have : f.support = (U \ {x | f x = (0 : X -> Y) x}) := by
    ext x
    simp only [mem_support, ne_eq, Pi.zero_apply, Set.mem_sdiff, mem_ofPred_eq, iff_and_self]
    exact (h ·)
  rw [EventuallyEq]; rw [Filter.Eventually]; rw [codiscreteWithin_iff_locallyFiniteComplementWithin]; rw [this]

中文:
定理 supportDiscreteWithin_iff_locallyFiniteWithin
  结论: [T1Space X] [Zero Y] {f : X -> Y}
  证明: by
  have : f.support = (U \ {x | f x = (0 : X -> Y) x}) := by
    ext x
    simp only [mem_support, ne_eq, Pi.zero_apply, Set.mem_sdiff, mem_ofPred_eq, iff_and_self]
    exact (h ·)
  rw [EventuallyEq]; rw [Filter.Eventually]; rw [codiscreteWithin_iff_locallyFiniteComplementWithin]; rw [this]

Depends on / 依赖: Eventually, EventuallyEq, Filter, Filter.Eventually, Pi.zero_apply, Set.mem_sdiff, codiscreteWithin_iff_locallyFiniteComplementWithin, f.support, iff_and_self, mem_ofPred_eq, mem_sdiff, mem_support, ne_eq, support, zero_apply
-/
theorem supportDiscreteWithin_iff_locallyFiniteWithin [T1Space X] [Zero Y] {f : X -> Y}
    (h : f.support subseteq U) :
    f =ᶠ[codiscreteWithin U] 0 ↔ forall z in U, exists t in 𝓝 z, Set.Finite (t inter f.support) := by
  have : f.support = (U \ {x | f x = (0 : X -> Y) x}) := by
    ext x
    simp only [mem_support, ne_eq, Pi.zero_apply, Set.mem_sdiff, mem_ofPred_eq, iff_and_self]
    exact (h ·)
  rw [EventuallyEq]; rw [Filter.Eventually]; rw [codiscreteWithin_iff_locallyFiniteComplementWithin]; rw [this]

/--
Definition of `LocallyFiniteSupport` / `LocallyFiniteSupport` 的定义

English:
definition LocallyFiniteSupport
  signature: [Zero Y] (f : X -> Y)
  body: forall z : X, exists t in 𝓝 z, Set.Finite (t inter f.support)

中文:
定义 LocallyFiniteSupport
  签名: [Zero Y] (f : X -> Y)
  定义体: forall z : X, exists t in 𝓝 z, Set.Finite (t inter f.support)

Depends on / 依赖: Finite, Set.Finite, f.support, support
-/
def LocallyFiniteSupport [Zero Y] (f : X -> Y) : Prop :=
  forall z : X, exists t in 𝓝 z, Set.Finite (t inter f.support)

/--
lemma `LocallyFiniteSupport.iff_locallyFinite_support` / 引理 `LocallyFiniteSupport.iff_locallyFinite_support`

English:
lemma LocallyFiniteSupport.iff_locallyFinite_support
  given: [Zero Y] (f : X -> Y)
  proof: by
  dsimp only [LocallyFinite]
  peel with z t ht
  have aux1 : t inter f.support = {i : f.support | ↑i in t} := by aesop
  have aux2 : InjOn Subtype.val {i : f.support | ↑i in t} := by aesop
  simp only [singleton_inter_nonempty, aux1, finite_image_iff aux2]

中文:
引理 LocallyFiniteSupport.iff_locallyFinite_support
  条件: [Zero Y] (f : X -> Y)
  证明: by
  dsimp only [LocallyFinite]
  peel with z t ht
  have aux1 : t inter f.support = {i : f.support | ↑i in t} := by aesop
  have aux2 : InjOn Subtype.val {i : f.support | ↑i in t} := by aesop
  simp only [singleton_inter_nonempty, aux1, finite_image_iff aux2]

Depends on / 依赖: LocallyFinite, Subtype, Subtype.val, f.support, finite_image_iff, singleton_inter_nonempty, support
-/
lemma LocallyFiniteSupport.iff_locallyFinite_support [Zero Y] (f : X -> Y) :
    LocallyFinite (fun s : f.support => ({s.val} : Set X)) ↔ LocallyFiniteSupport f := by
  dsimp only [LocallyFinite]
  peel with z t ht
  have aux1 : t inter f.support = {i : f.support | ↑i in t} := by aesop
  have aux2 : InjOn Subtype.val {i : f.support | ↑i in t} := by aesop
  simp only [singleton_inter_nonempty, aux1, finite_image_iff aux2]

/--
lemma `LocallyFiniteSupport.locallyFinite_support` / 引理 `LocallyFiniteSupport.locallyFinite_support`

English:
lemma LocallyFiniteSupport.locallyFinite_support
  given: [Zero Y] (f : X -> Y) (h : LocallyFiniteSupport f)
  proof: (LocallyFiniteSupport.iff_locallyFinite_support f).mpr h

中文:
引理 LocallyFiniteSupport.locallyFinite_support
  条件: [Zero Y] (f : X -> Y) (h : LocallyFiniteSupport f)
  证明: (LocallyFiniteSupport.iff_locallyFinite_support f).mpr h

Depends on / 依赖: LocallyFiniteSupport, LocallyFiniteSupport.iff_locallyFinite_support, iff_locallyFinite_support
-/
lemma LocallyFiniteSupport.locallyFinite_support [Zero Y] (f : X -> Y) (h : LocallyFiniteSupport f) :
    LocallyFinite (fun s : f.support => ({s.val} : Set X)) :=
  (LocallyFiniteSupport.iff_locallyFinite_support f).mpr h

/--
lemma `LocallyFiniteSupport.finite_inter_support_of_isCompact` / 引理 `LocallyFiniteSupport.finite_inter_support_of_isCompact`

English:
lemma LocallyFiniteSupport.finite_inter_support_of_isCompact
  statement: {W : Set X}
  proof: by
  have := LocallyFinite.finite_nonempty_inter_compact
    (LocallyFiniteSupport.locallyFinite_support f h) hW
  have lem {α : Type u_1} (s t : Set α) : {i : s | ({↑i} inter t).Nonempty} = (t inter s) := by aesop
  rw [← lem f.support W]
  exact Finite.image Subtype.val this

中文:
引理 LocallyFiniteSupport.finite_inter_support_of_isCompact
  结论: {W : Set X}
  证明: by
  have := LocallyFinite.finite_nonempty_inter_compact
    (LocallyFiniteSupport.locallyFinite_support f h) hW
  have lem {α : Type u_1} (s t : Set α) : {i : s | ({↑i} inter t).Nonempty} = (t inter s) := by aesop
  rw [← lem f.support W]
  exact Finite.image Subtype.val this

Depends on / 依赖: Finite, Finite.image, LocallyFinite, LocallyFinite.finite_nonempty_inter_compact, LocallyFiniteSupport, LocallyFiniteSupport.locallyFinite_support, Nonempty, Subtype, Subtype.val, f.support, finite_nonempty_inter_compact, locallyFinite_support, support
-/
lemma LocallyFiniteSupport.finite_inter_support_of_isCompact {W : Set X}
   [Zero Y] {f : X -> Y} (h : LocallyFiniteSupport f)
   (hW : IsCompact W) : (W inter f.support).Finite := by
  have := LocallyFinite.finite_nonempty_inter_compact
    (LocallyFiniteSupport.locallyFinite_support f h) hW
  have lem {α : Type u_1} (s t : Set α) : {i : s | ({↑i} inter t).Nonempty} = (t inter s) := by aesop
  rw [← lem f.support W]
  exact Finite.image Subtype.val this

/--
lemma `Function.locallyFinsupp.locallyFiniteSupport` / 引理 `Function.locallyFinsupp.locallyFiniteSupport`

English:
lemma Function.locallyFinsupp.locallyFiniteSupport
  given: [Zero Y] (f : locallyFinsupp X Y)
  proof: (f.supportLocallyFiniteWithinDomain' · (by trivial))

中文:
引理 Function.locallyFinsupp.locallyFiniteSupport
  条件: [Zero Y] (f : locallyFinsupp X Y)
  证明: (f.supportLocallyFiniteWithinDomain' · (by trivial))

Depends on / 依赖: f.supportLocallyFiniteWithinDomain, supportLocallyFiniteWithinDomain
-/
lemma Function.locallyFinsupp.locallyFiniteSupport [Zero Y] (f : locallyFinsupp X Y) :
    LocallyFiniteSupport f.toFun :=
  (f.supportLocallyFiniteWithinDomain' · (by trivial))

namespace Function.locallyFinsuppWithin

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: Y] : FunLike (locallyFinsuppWithin U Y) X Y where
  body: D.toFun
  coe_injective := fun ⟨_, _, _⟩ ⟨_, _, _⟩ => by simp

@[simp]

中文:
实例 [Zero
  签名: Y] : FunLike (locallyFinsuppWithin U Y) X Y where
  定义体: D.toFun
  coe_injective := fun ⟨_, _, _⟩ ⟨_, _, _⟩ => by simp

@[simp]

Depends on / 依赖: D.toFun
-/
instance [Zero Y] : FunLike (locallyFinsuppWithin U Y) X Y where
  coe D := D.toFun
  coe_injective := fun ⟨_, _, _⟩ ⟨_, _, _⟩ => by simp

@[simp]
/--
lemma `toFun_eq_coe` / 引理 `toFun_eq_coe`

English:
lemma toFun_eq_coe
  given: [Zero Y] (c : locallyFinsuppWithin U Y)
  statement: c.toFun = ⇑c
  proof: rfl

@[simp]

中文:
引理 toFun_eq_coe
  条件: [Zero Y] (c : locallyFinsuppWithin U Y)
  结论: c.toFun = ⇑c
  证明: rfl

@[simp]
-/
lemma toFun_eq_coe [Zero Y] (c : locallyFinsuppWithin U Y) : c.toFun = ⇑c := rfl

@[simp]
/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  statement: [Zero Y] (f : X -> Y) (h : f.support subseteq U)
  proof: rfl

中文:
引理 coe_mk
  结论: [Zero Y] (f : X -> Y) (h : f.support subseteq U)
  证明: rfl
-/
lemma coe_mk [Zero Y] (f : X -> Y) (h : f.support subseteq U)
    (h' : forall z in U, exists t in 𝓝 z, Set.Finite (t inter f.support)) :
    ⇑(Function.locallyFinsuppWithin.mk f h h') = f := rfl

/--
Definition of `support` / `support` 的定义

English:
abbreviation support
  signature: [Zero Y] (D : locallyFinsuppWithin U Y)
  body: Function.support D

中文:
缩写 support
  签名: [Zero Y] (D : locallyFinsuppWithin U Y)
  定义体: Function.support D

Depends on / 依赖: Function, Function.support, support
-/
abbrev support [Zero Y] (D : locallyFinsuppWithin U Y) := Function.support D

/--
lemma `supportWithinDomain` / 引理 `supportWithinDomain`

English:
lemma supportWithinDomain
  given: [Zero Y] (D : locallyFinsuppWithin U Y)
  proof: D.supportWithinDomain'

中文:
引理 supportWithinDomain
  条件: [Zero Y] (D : locallyFinsuppWithin U Y)
  证明: D.supportWithinDomain'

Depends on / 依赖: D.supportWithinDomain, supportWithinDomain
-/
lemma supportWithinDomain [Zero Y] (D : locallyFinsuppWithin U Y) :
    D.support subseteq U := D.supportWithinDomain'

/--
lemma `supportLocallyFiniteWithinDomain` / 引理 `supportLocallyFiniteWithinDomain`

English:
lemma supportLocallyFiniteWithinDomain
  given: [Zero Y] (D : locallyFinsuppWithin U Y)
  proof: D.supportLocallyFiniteWithinDomain'

@[ext]

中文:
引理 supportLocallyFiniteWithinDomain
  条件: [Zero Y] (D : locallyFinsuppWithin U Y)
  证明: D.supportLocallyFiniteWithinDomain'

@[ext]

Depends on / 依赖: D.supportLocallyFiniteWithinDomain, supportLocallyFiniteWithinDomain
-/
lemma supportLocallyFiniteWithinDomain [Zero Y] (D : locallyFinsuppWithin U Y) :
    forall z in U, exists t in 𝓝 z, Set.Finite (t inter D.support) := D.supportLocallyFiniteWithinDomain'

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} (h : forall a, D₁ a = D₂ a)
  proof: DFunLike.ext _ _ h

中文:
引理 ext
  条件: [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} (h : 对任意 a, D₁ a = D₂ a)
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
lemma ext [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} (h : forall a, D₁ a = D₂ a) :
    D₁ = D₂ := DFunLike.ext _ _ h

/--
lemma `coe_injective` / 引理 `coe_injective`

English:
lemma coe_injective
  given: [Zero Y]
  proof: DFunLike.coe_injective

中文:
引理 coe_injective
  条件: [Zero Y]
  证明: DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
lemma coe_injective [Zero Y] :
    Injective (· : locallyFinsuppWithin U Y -> X -> Y) := DFunLike.coe_injective

/-!
## Singleton Indicators as Functions with Locally Finite Support
-/

/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: [DecidableEq X] [Zero Y] (x : X) (y : Y)
  body: Pi.single x y
  supportWithinDomain' z hz := by tauto
  supportLocallyFiniteWithinDomain' _ _ :=
    ⟨Set.univ, univ_mem, by simpa using (finite_singleton x).subset Pi.support_single_subset⟩

中文:
定义 single
  签名: [DecidableEq X] [Zero Y] (x : X) (y : Y)
  定义体: Pi.single x y
  supportWithinDomain' z hz := by tauto
  supportLocallyFiniteWithinDomain' _ _ :=
    ⟨Set.univ, univ_mem, by simpa using (finite_singleton x).subset Pi.support_single_subset⟩

Depends on / 依赖: Pi.single, single
-/
noncomputable def single [DecidableEq X] [Zero Y] (x : X) (y : Y) : locallyFinsupp X Y where
  toFun := Pi.single x y
  supportWithinDomain' z hz := by tauto
  supportLocallyFiniteWithinDomain' _ _ :=
    ⟨Set.univ, univ_mem, by simpa using (finite_singleton x).subset Pi.support_single_subset⟩

/--
lemma `single_apply` / 引理 `single_apply`

English:
lemma single_apply
  given: [DecidableEq X] [Zero Y] {x₁ x₂ : X} {y : Y}
  proof: by
  simp_rw [DFunLike.coe, single, Pi.single_apply]

中文:
引理 single_apply
  条件: [DecidableEq X] [Zero Y] {x₁ x₂ : X} {y : Y}
  证明: by
  simp_rw [DFunLike.coe, single, Pi.single_apply]
-/
@[simp] lemma single_apply [DecidableEq X] [Zero Y] {x₁ x₂ : X} {y : Y} :
    single x₁ y x₂ = if x₂ = x₁ then y else 0 := by
  simp_rw [DFunLike.coe, single, Pi.single_apply]

/--
lemma `single_zero` / 引理 `single_zero`

English:
lemma single_zero
  given: [DecidableEq X] [Zero Y] {x : X}
  proof: by aesop

中文:
引理 single_zero
  条件: [DecidableEq X] [Zero Y] {x : X}
  证明: by aesop
-/
@[simp] lemma single_zero [DecidableEq X] [Zero Y] {x : X} :
    single x (0 : Y) = 0 := by aesop

/--
lemma `coe_single` / 引理 `coe_single`

English:
lemma coe_single
  given: [DecidableEq X] [Zero Y] {x : X} {y : Y}
  proof: by
  ext
  simp [Pi.single_apply]

中文:
引理 coe_single
  条件: [DecidableEq X] [Zero Y] {x : X} {y : Y}
  证明: by
  ext
  simp [Pi.single_apply]
-/
@[simp] lemma coe_single [DecidableEq X] [Zero Y] {x : X} {y : Y} :
    (single x y : X -> Y) = Pi.single x y := by
  ext
  simp [Pi.single_apply]

/-!
## Elementary properties of the support
-/

/--
Simplifier lemma: Functions with locally finite support within `U` evaluate to zero outside of `U`.
-/
@[simp]
/--
lemma `apply_eq_zero_of_notMem` / 引理 `apply_eq_zero_of_notMem`

English:
lemma apply_eq_zero_of_notMem
  statement: [Zero Y] {z : X} (D : locallyFinsuppWithin U Y)
  proof: notMem_support.mp fun a => hz (D.supportWithinDomain a)

中文:
引理 apply_eq_zero_of_notMem
  结论: [Zero Y] {z : X} (D : locallyFinsuppWithin U Y)
  证明: notMem_support.mp fun a => hz (D.supportWithinDomain a)

Depends on / 依赖: D.supportWithinDomain, notMem_support, notMem_support.mp, supportWithinDomain
-/
lemma apply_eq_zero_of_notMem [Zero Y] {z : X} (D : locallyFinsuppWithin U Y)
    (hz : z ∉ U) :
    D z = 0 := notMem_support.mp fun a => hz (D.supportWithinDomain a)

/--
theorem `eq_zero_codiscreteWithin` / 定理 `eq_zero_codiscreteWithin`

English:
theorem eq_zero_codiscreteWithin
  given: [Zero Y] [T1Space X] (D : locallyFinsuppWithin U Y)
  proof: by
  apply codiscreteWithin_iff_locallyFiniteComplementWithin.2
  have : D.support = (U \ {x | D x = (0 : X -> Y) x}) := by
    ext x
    simp only [mem_support, ne_eq, Pi.zero_apply, Set.mem_sdiff, Set.mem_ofPred_eq, iff_and_self]
    exact (support_subset_iff.1 D.supportWithinDomain) x
  rw [← thi

中文:
定理 eq_zero_codiscreteWithin
  条件: [Zero Y] [T1Space X] (D : locallyFinsuppWithin U Y)
  证明: by
  apply codiscreteWithin_iff_locallyFiniteComplementWithin.2
  have : D.support = (U \ {x | D x = (0 : X -> Y) x}) := by
    ext x
    simp only [mem_support, ne_eq, Pi.zero_apply, Set.mem_sdiff, Set.mem_ofPred_eq, iff_and_self]
    exact (support_subset_iff.1 D.supportWithinDomain) x
  rw [← thi

Depends on / 依赖: D.support, D.supportLocallyFiniteWithinDomain, D.supportWithinDomain, Pi.zero_apply, Set.mem_ofPred_eq, Set.mem_sdiff, codiscreteWithin_iff_locallyFiniteComplementWithin, iff_and_self, mem_ofPred_eq, mem_sdiff, mem_support, ne_eq, support, supportLocallyFiniteWithinDomain, supportWithinDomain, support_subset_iff, zero_apply
-/
theorem eq_zero_codiscreteWithin [Zero Y] [T1Space X] (D : locallyFinsuppWithin U Y) :
    D =ᶠ[Filter.codiscreteWithin U] 0 := by
  apply codiscreteWithin_iff_locallyFiniteComplementWithin.2
  have : D.support = (U \ {x | D x = (0 : X -> Y) x}) := by
    ext x
    simp only [mem_support, ne_eq, Pi.zero_apply, Set.mem_sdiff, Set.mem_ofPred_eq, iff_and_self]
    exact (support_subset_iff.1 D.supportWithinDomain) x
  rw [← this]
  exact D.supportLocallyFiniteWithinDomain

/--
theorem `discreteSupport` / 定理 `discreteSupport`

English:
theorem discreteSupport
  given: [Zero Y] [T1Space X] (D : locallyFinsuppWithin U Y)
  proof: by
  have : D.support = {x | D x = 0}ᶜ inter U := by
    ext x
    constructor
    · exact fun hx => ⟨by tauto, D.supportWithinDomain hx⟩
    · intro hx
      rw [mem_inter_iff]; rw [mem_compl_iff]; rw [mem_ofPred_eq] at hx
      tauto
  rw [this]
  apply isDiscrete_of_codiscreteWithin
  rw [compl_c

中文:
定理 discreteSupport
  条件: [Zero Y] [T1Space X] (D : locallyFinsuppWithin U Y)
  证明: by
  have : D.support = {x | D x = 0}ᶜ inter U := by
    ext x
    constructor
    · exact fun hx => ⟨by tauto, D.supportWithinDomain hx⟩
    · intro hx
      rw [mem_inter_iff]; rw [mem_compl_iff]; rw [mem_ofPred_eq] at hx
      tauto
  rw [this]
  apply isDiscrete_of_codiscreteWithin
  rw [compl_c

Depends on / 依赖: D.support, D.supportLocallyFiniteWithinDomain, D.supportWithinDomain, compl_compl, isDiscrete_of_codiscreteWithin, mem_compl_iff, mem_inter_iff, mem_ofPred_eq, support, supportDiscreteWithin_iff_locallyFiniteWithin, supportLocallyFiniteWithinDomain, supportWithinDomain
-/
theorem discreteSupport [Zero Y] [T1Space X] (D : locallyFinsuppWithin U Y) :
    IsDiscrete D.support := by
  have : D.support = {x | D x = 0}ᶜ inter U := by
    ext x
    constructor
    · exact fun hx => ⟨by tauto, D.supportWithinDomain hx⟩
    · intro hx
      rw [mem_inter_iff]; rw [mem_compl_iff]; rw [mem_ofPred_eq] at hx
      tauto
  rw [this]
  apply isDiscrete_of_codiscreteWithin
  rw [compl_compl]
  apply (supportDiscreteWithin_iff_locallyFiniteWithin D.supportWithinDomain).2
  exact D.supportLocallyFiniteWithinDomain

/--
theorem `closedSupport` / 定理 `closedSupport`

English:
theorem closedSupport
  statement: [T1Space X] [Zero Y] (D : locallyFinsuppWithin U Y)
  proof: by
  convert!
    isClosed_sdiff_of_codiscreteWithin
      ((supportDiscreteWithin_iff_locallyFiniteWithin D.supportWithinDomain).2
        D.supportLocallyFiniteWithinDomain)
      hU
  ext x
  constructor <;> intro hx
  · simp_all [D.supportWithinDomain hx]
  · simp_all

中文:
定理 closedSupport
  结论: [T1Space X] [Zero Y] (D : locallyFinsuppWithin U Y)
  证明: by
  convert!
    isClosed_sdiff_of_codiscreteWithin
      ((supportDiscreteWithin_iff_locallyFiniteWithin D.supportWithinDomain).2
        D.supportLocallyFiniteWithinDomain)
      hU
  ext x
  constructor <;> intro hx
  · simp_all [D.supportWithinDomain hx]
  · simp_all

Depends on / 依赖: D.supportLocallyFiniteWithinDomain, D.supportWithinDomain, convert, isClosed_sdiff_of_codiscreteWithin, supportDiscreteWithin_iff_locallyFiniteWithin, supportLocallyFiniteWithinDomain, supportWithinDomain
-/
theorem closedSupport [T1Space X] [Zero Y] (D : locallyFinsuppWithin U Y)
    (hU : IsClosed U) :
    IsClosed D.support := by
  convert!
    isClosed_sdiff_of_codiscreteWithin
      ((supportDiscreteWithin_iff_locallyFiniteWithin D.supportWithinDomain).2
        D.supportLocallyFiniteWithinDomain)
      hU
  ext x
  constructor <;> intro hx
  · simp_all [D.supportWithinDomain hx]
  · simp_all

/--
theorem `finiteSupport` / 定理 `finiteSupport`

English:
theorem finiteSupport
  statement: [T2Space X] [Zero Y] (D : locallyFinsuppWithin U Y)
  proof: (hU.of_isClosed_subset (D.closedSupport hU.isClosed)
    D.supportWithinDomain).finite D.discreteSupport

中文:
定理 finiteSupport
  结论: [T2Space X] [Zero Y] (D : locallyFinsuppWithin U Y)
  证明: (hU.of_isClosed_subset (D.closedSupport hU.isClosed)
    D.supportWithinDomain).finite D.discreteSupport

Depends on / 依赖: D.closedSupport, D.discreteSupport, D.supportWithinDomain, closedSupport, discreteSupport, finite, hU.isClosed, hU.of_isClosed_subset, isClosed, of_isClosed_subset, supportWithinDomain
-/
theorem finiteSupport [T2Space X] [Zero Y] (D : locallyFinsuppWithin U Y)
    (hU : IsCompact U) :
    Set.Finite D.support :=
  (hU.of_isClosed_subset (D.closedSupport hU.isClosed)
    D.supportWithinDomain).finite D.discreteSupport

/-!
## Lattice ordered group structure

If `X` is a suitable instance, this section equips functions with locally finite support within `U`
with the standard structure of a lattice ordered group, where addition, comparison, min and max are
defined pointwise.
-/

variable (U) in
/--
Definition of `addSubmonoid` / `addSubmonoid` 的定义

English:
definition addSubmonoid
  signature: [AddMonoid Y]
  body: {f | f.support subseteq U ∧ forall z in U, exists t in 𝓝 z, Set.Finite (t inter f.support)}
  zero_mem' := by
    simp only [support_subset_iff, ne_eq, mem_ofPred_eq, Pi.zero_apply, not_true_eq_false,
      IsEmpty.forall_iff, implies_true, support_zero, inter_empty, finite_empty, and_true,
      tr

中文:
定义 addSubmonoid
  签名: [AddMonoid Y]
  定义体: {f | f.support subseteq U ∧ forall z in U, exists t in 𝓝 z, Set.Finite (t inter f.support)}
  zero_mem' := by
    simp only [support_subset_iff, ne_eq, mem_ofPred_eq, Pi.zero_apply, not_true_eq_false,
      IsEmpty.forall_iff, implies_true, support_zero, inter_empty, finite_empty, and_true,
      tr
-/
protected def addSubmonoid [AddMonoid Y] : AddSubmonoid (X -> Y) where
  carrier := {f | f.support subseteq U ∧ forall z in U, exists t in 𝓝 z, Set.Finite (t inter f.support)}
  zero_mem' := by
    simp only [support_subset_iff, ne_eq, mem_ofPred_eq, Pi.zero_apply, not_true_eq_false,
      IsEmpty.forall_iff, implies_true, support_zero, inter_empty, finite_empty, and_true,
      true_and]
    exact fun _ _ => ⟨⊤, univ_mem⟩
  add_mem' {f g} hf hg := by
    constructor
    · intro x hx
      contrapose hx
      simp [notMem_support.1 fun a => hx (hf.1 a), notMem_support.1 fun a => hx (hg.1 a)]
    · intro z hz
      obtain ⟨t₁, ht₁⟩ := hf.2 z hz
      obtain ⟨t₂, ht₂⟩ := hg.2 z hz
      use t₁ inter t₂, inter_mem ht₁.1 ht₂.1
      apply Set.Finite.subset (s := (t₁ inter f.support) union (t₂ inter g.support)) (ht₁.2.union ht₂.2)
      intro a ha
      simp_all only [support_subset_iff, ne_eq, mem_ofPred_eq,
        mem_inter_iff, mem_support, Pi.add_apply, mem_union, true_and]
      by_contra! hCon
      simp_all

/--
lemma `memAddSubmonoid` / 引理 `memAddSubmonoid`

English:
lemma memAddSubmonoid
  given: [AddMonoid Y] (D : locallyFinsuppWithin U Y)
  proof: ⟨D.supportWithinDomain, D.supportLocallyFiniteWithinDomain⟩

中文:
引理 memAddSubmonoid
  条件: [AddMonoid Y] (D : locallyFinsuppWithin U Y)
  证明: ⟨D.supportWithinDomain, D.supportLocallyFiniteWithinDomain⟩
-/
protected lemma memAddSubmonoid [AddMonoid Y] (D : locallyFinsuppWithin U Y) :
    (D : X -> Y) in locallyFinsuppWithin.addSubmonoid U :=
  ⟨D.supportWithinDomain, D.supportLocallyFiniteWithinDomain⟩

variable (U) in
/--
Definition of `addSubgroup` / `addSubgroup` 的定义

English:
definition addSubgroup
  signature: [AddGroup Y]
  body: {f | f.support subseteq U ∧ forall z in U, exists t in 𝓝 z, Set.Finite (t inter f.support)}
  __ := locallyFinsuppWithin.addSubmonoid U
  neg_mem' {f} hf := by simp_all

中文:
定义 addSubgroup
  签名: [AddGroup Y]
  定义体: {f | f.support subseteq U ∧ forall z in U, exists t in 𝓝 z, Set.Finite (t inter f.support)}
  __ := locallyFinsuppWithin.addSubmonoid U
  neg_mem' {f} hf := by simp_all
-/
protected def addSubgroup [AddGroup Y] : AddSubgroup (X -> Y) where
  carrier := {f | f.support subseteq U ∧ forall z in U, exists t in 𝓝 z, Set.Finite (t inter f.support)}
  __ := locallyFinsuppWithin.addSubmonoid U
  neg_mem' {f} hf := by simp_all

/--
lemma `memAddSubgroup` / 引理 `memAddSubgroup`

English:
lemma memAddSubgroup
  given: [AddGroup Y] (D : locallyFinsuppWithin U Y)
  proof: ⟨D.supportWithinDomain, D.supportLocallyFiniteWithinDomain⟩

中文:
引理 memAddSubgroup
  条件: [AddGroup Y] (D : locallyFinsuppWithin U Y)
  证明: ⟨D.supportWithinDomain, D.supportLocallyFiniteWithinDomain⟩
-/
protected lemma memAddSubgroup [AddGroup Y] (D : locallyFinsuppWithin U Y) :
    (D : X -> Y) in locallyFinsuppWithin.addSubgroup U :=
  ⟨D.supportWithinDomain, D.supportLocallyFiniteWithinDomain⟩

/--
Assign a function with locally finite support within `U` to a function in the subgroup.
-/
@[simps]
/--
Definition of `mk_of_mem_addSubmonoid` / `mk_of_mem_addSubmonoid` 的定义

English:
definition mk_of_mem_addSubmonoid
  signature: [AddMonoid Y] (f : X -> Y)
  body: ⟨f, hf.1, hf.2⟩

中文:
定义 mk_of_mem_addSubmonoid
  签名: [AddMonoid Y] (f : X -> Y)
  定义体: ⟨f, hf.1, hf.2⟩
-/
def mk_of_mem_addSubmonoid [AddMonoid Y] (f : X -> Y)
    (hf : f in locallyFinsuppWithin.addSubmonoid U) :
    locallyFinsuppWithin U Y := ⟨f, hf.1, hf.2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: Y] : Zero (locallyFinsuppWithin U Y) where
  body: mk_of_mem_addSubmonoid 0 zero_mem _

中文:
实例 [AddMonoid
  签名: Y] : Zero (locallyFinsuppWithin U Y) where
  定义体: mk_of_mem_addSubmonoid 0 zero_mem _

Depends on / 依赖: mk_of_mem_addSubmonoid, zero_mem
-/
instance [AddMonoid Y] : Zero (locallyFinsuppWithin U Y) where
zero := mk_of_mem_addSubmonoid 0 zero_mem _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: Y] : Add (locallyFinsuppWithin U Y) where
  body: mk_of_mem_addSubmonoid (D₁ + D₂) add_mem D₁.memAddSubmonoid D₂.memAddSubmonoid

中文:
实例 [AddMonoid
  签名: Y] : Add (locallyFinsuppWithin U Y) where
  定义体: mk_of_mem_addSubmonoid (D₁ + D₂) add_mem D₁.memAddSubmonoid D₂.memAddSubmonoid

Depends on / 依赖: add_mem, memAddSubmonoid, mk_of_mem_addSubmonoid
-/
instance [AddMonoid Y] : Add (locallyFinsuppWithin U Y) where
add D₁ D₂ := mk_of_mem_addSubmonoid (D₁ + D₂) add_mem D₁.memAddSubmonoid D₂.memAddSubmonoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: Y] : SMul Nat (locallyFinsuppWithin U Y) where
  body: mk_of_mem_addSubmonoid (n • D) nsmul_mem D.memAddSubmonoid n

中文:
实例 [AddMonoid
  签名: Y] : SMul 自然数 (locallyFinsuppWithin U Y) where
  定义体: mk_of_mem_addSubmonoid (n • D) nsmul_mem D.memAddSubmonoid n

Depends on / 依赖: D.memAddSubmonoid, memAddSubmonoid, mk_of_mem_addSubmonoid, nsmul_mem
-/
instance [AddMonoid Y] : SMul Nat (locallyFinsuppWithin U Y) where
smul n D := mk_of_mem_addSubmonoid (n • D) nsmul_mem D.memAddSubmonoid n

/--
Assign a function with locally finite support within `U` to a function in the subgroup.
-/
@[simps]
/--
Definition of `mk_of_mem_addSubgroup` / `mk_of_mem_addSubgroup` 的定义

English:
definition mk_of_mem_addSubgroup
  signature: [AddGroup Y] (f : X -> Y) (hf : f in locallyFinsuppWithin.addSubgroup U)
  body: ⟨f, hf.1, hf.2⟩

@[deprecated (since := "2026-03-06")] alias mk_of_mem := mk_of_mem_addSubgroup

中文:
定义 mk_of_mem_addSubgroup
  签名: [AddGroup Y] (f : X -> Y) (hf : f in locallyFinsuppWithin.addSubgroup U)
  定义体: ⟨f, hf.1, hf.2⟩

@[deprecated (since := "2026-03-06")] alias mk_of_mem := mk_of_mem_addSubgroup
-/
def mk_of_mem_addSubgroup [AddGroup Y] (f : X -> Y) (hf : f in locallyFinsuppWithin.addSubgroup U) :
    locallyFinsuppWithin U Y := ⟨f, hf.1, hf.2⟩

@[deprecated (since := "2026-03-06")] alias mk_of_mem := mk_of_mem_addSubgroup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddGroup
  signature: Y] : Neg (locallyFinsuppWithin U Y) where
  body: mk_of_mem_addSubgroup (-D) neg_mem D.memAddSubgroup

中文:
实例 [AddGroup
  签名: Y] : Neg (locallyFinsuppWithin U Y) where
  定义体: mk_of_mem_addSubgroup (-D) neg_mem D.memAddSubgroup

Depends on / 依赖: D.memAddSubgroup, memAddSubgroup, mk_of_mem_addSubgroup, neg_mem
-/
instance [AddGroup Y] : Neg (locallyFinsuppWithin U Y) where
neg D := mk_of_mem_addSubgroup (-D) neg_mem D.memAddSubgroup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddGroup
  signature: Y] : Sub (locallyFinsuppWithin U Y) where
  body: mk_of_mem_addSubgroup (D₁ - D₂) sub_mem D₁.memAddSubgroup D₂.memAddSubgroup

中文:
实例 [AddGroup
  签名: Y] : Sub (locallyFinsuppWithin U Y) where
  定义体: mk_of_mem_addSubgroup (D₁ - D₂) sub_mem D₁.memAddSubgroup D₂.memAddSubgroup

Depends on / 依赖: memAddSubgroup, mk_of_mem_addSubgroup, sub_mem
-/
instance [AddGroup Y] : Sub (locallyFinsuppWithin U Y) where
sub D₁ D₂ := mk_of_mem_addSubgroup (D₁ - D₂) sub_mem D₁.memAddSubgroup D₂.memAddSubgroup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddGroup
  signature: Y] : SMul Int (locallyFinsuppWithin U Y) where
  body: mk_of_mem_addSubgroup (n • D) zsmul_mem D.memAddSubgroup n

中文:
实例 [AddGroup
  签名: Y] : SMul 整数 (locallyFinsuppWithin U Y) where
  定义体: mk_of_mem_addSubgroup (n • D) zsmul_mem D.memAddSubgroup n

Depends on / 依赖: D.memAddSubgroup, memAddSubgroup, mk_of_mem_addSubgroup, zsmul_mem
-/
instance [AddGroup Y] : SMul Int (locallyFinsuppWithin U Y) where
smul n D := mk_of_mem_addSubgroup (n • D) zsmul_mem D.memAddSubgroup n

/--
lemma `coe_zero` / 引理 `coe_zero`

English:
lemma coe_zero
  given: [AddMonoid Y]
  proof: rfl

中文:
引理 coe_zero
  条件: [AddMonoid Y]
  证明: rfl
-/
@[simp] lemma coe_zero [AddMonoid Y] :
    ((0 : locallyFinsuppWithin U Y) : X -> Y) = 0 := rfl
/--
lemma `coe_add` / 引理 `coe_add`

English:
lemma coe_add
  given: [AddMonoid Y] (D₁ D₂ : locallyFinsuppWithin U Y)
  proof: rfl

中文:
引理 coe_add
  条件: [AddMonoid Y] (D₁ D₂ : locallyFinsuppWithin U Y)
  证明: rfl
-/
@[simp] lemma coe_add [AddMonoid Y] (D₁ D₂ : locallyFinsuppWithin U Y) :
    (↑(D₁ + D₂) : X -> Y) = D₁ + D₂ := rfl
/--
lemma `coe_neg` / 引理 `coe_neg`

English:
lemma coe_neg
  given: [AddGroup Y] (D : locallyFinsuppWithin U Y)
  proof: rfl

中文:
引理 coe_neg
  条件: [AddGroup Y] (D : locallyFinsuppWithin U Y)
  证明: rfl
-/
@[simp] lemma coe_neg [AddGroup Y] (D : locallyFinsuppWithin U Y) :
    (↑(-D) : X -> Y) = -(D : X -> Y) := rfl
/--
lemma `coe_sub` / 引理 `coe_sub`

English:
lemma coe_sub
  given: [AddGroup Y] (D₁ D₂ : locallyFinsuppWithin U Y)
  proof: rfl

中文:
引理 coe_sub
  条件: [AddGroup Y] (D₁ D₂ : locallyFinsuppWithin U Y)
  证明: rfl
-/
@[simp] lemma coe_sub [AddGroup Y] (D₁ D₂ : locallyFinsuppWithin U Y) :
    (↑(D₁ - D₂) : X -> Y) = D₁ - D₂ := rfl
/--
lemma `coe_nsmul` / 引理 `coe_nsmul`

English:
lemma coe_nsmul
  given: [AddMonoid Y] (D : locallyFinsuppWithin U Y) (n : Nat)
  proof: rfl

中文:
引理 coe_nsmul
  条件: [AddMonoid Y] (D : locallyFinsuppWithin U Y) (n : 自然数)
  证明: rfl
-/
@[simp] lemma coe_nsmul [AddMonoid Y] (D : locallyFinsuppWithin U Y) (n : Nat) :
    (↑(n • D) : X -> Y) = n • (D : X -> Y) := rfl
/--
lemma `coe_zsmul` / 引理 `coe_zsmul`

English:
lemma coe_zsmul
  given: [AddGroup Y] (D : locallyFinsuppWithin U Y) (n : Int)
  proof: rfl

中文:
引理 coe_zsmul
  条件: [AddGroup Y] (D : locallyFinsuppWithin U Y) (n : 整数)
  证明: rfl
-/
@[simp] lemma coe_zsmul [AddGroup Y] (D : locallyFinsuppWithin U Y) (n : Int) :
    (↑(n • D) : X -> Y) = n • (D : X -> Y) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: Y] : AddMonoid (locallyFinsuppWithin U Y)
  body: Injective.addMonoid (M₁ := locallyFinsuppWithin U Y) (M₂ := X -> Y)
    _ coe_injective coe_zero coe_add coe_nsmul

中文:
实例 [AddMonoid
  签名: Y] : AddMonoid (locallyFinsuppWithin U Y)
  定义体: Injective.addMonoid (M₁ := locallyFinsuppWithin U Y) (M₂ := X -> Y)
    _ coe_injective coe_zero coe_add coe_nsmul

Depends on / 依赖: Injective, Injective.addMonoid, addMonoid, coe_add, coe_injective, coe_nsmul, coe_zero, locallyFinsuppWithin
-/
instance [AddMonoid Y] : AddMonoid (locallyFinsuppWithin U Y) :=
  Injective.addMonoid (M₁ := locallyFinsuppWithin U Y) (M₂ := X -> Y)
    _ coe_injective coe_zero coe_add coe_nsmul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMonoid
  signature: Y] : AddCommMonoid (locallyFinsuppWithin U Y)
  body: Injective.addCommMonoid (M₁ := locallyFinsuppWithin U Y) (M₂ := X -> Y)
    _ coe_injective coe_zero coe_add coe_nsmul

中文:
实例 [AddCommMonoid
  签名: Y] : AddCommMonoid (locallyFinsuppWithin U Y)
  定义体: Injective.addCommMonoid (M₁ := locallyFinsuppWithin U Y) (M₂ := X -> Y)
    _ coe_injective coe_zero coe_add coe_nsmul

Depends on / 依赖: Injective, Injective.addCommMonoid, addCommMonoid, coe_add, coe_injective, coe_nsmul, coe_zero, locallyFinsuppWithin
-/
instance [AddCommMonoid Y] : AddCommMonoid (locallyFinsuppWithin U Y) :=
  Injective.addCommMonoid (M₁ := locallyFinsuppWithin U Y) (M₂ := X -> Y)
    _ coe_injective coe_zero coe_add coe_nsmul

/--
lemma `coe_sum` / 引理 `coe_sum`

English:
lemma coe_sum
  statement: [AddCommMonoid Y] {ι : Type*} {s : Finset ι}
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simp_all
  | insert => simp_all

中文:
引理 coe_sum
  结论: [AddCommMonoid Y] {ι : 类型} {s : Finset ι}
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simp_all
  | insert => simp_all
-/
@[simp] lemma coe_sum [AddCommMonoid Y] {ι : Type*} {s : Finset ι}
    {F : ι -> locallyFinsuppWithin U Y} :
    (↑(∑ n in s, F n) : X -> Y) = ∑ n in s, (F n : X -> Y) := by
  classical
  induction s using Finset.induction with
  | empty => simp_all
  | insert => simp_all

/--
lemma `coe_finsum` / 引理 `coe_finsum`

English:
lemma coe_finsum
  given: {ι : Type*} {F : ι -> locallyFinsuppWithin U Int}
  proof: by
  have : F.support = (fun i => (F i : X -> Int)).support := by
    simp [Set.ext_iff, DFunLike.ext_iff, funext_iff]
  by_cases h : F.support.Finite
  · rw [finsum_eq_sum F h, Function.locallyFinsuppWithin.coe_sum]
    have h₂ : (fun i => (F i : X -> Int)).support.Finite := by simp_all
    simp_al

中文:
引理 coe_finsum
  条件: {ι : 类型} {F : ι -> locallyFinsuppWithin U 整数}
  证明: by
  have : F.support = (fun i => (F i : X -> Int)).support := by
    simp [Set.ext_iff, DFunLike.ext_iff, funext_iff]
  by_cases h : F.support.Finite
  · rw [finsum_eq_sum F h, Function.locallyFinsuppWithin.coe_sum]
    have h₂ : (fun i => (F i : X -> Int)).support.Finite := by simp_all
    simp_al
-/
@[simp] lemma coe_finsum {ι : Type*} {F : ι -> locallyFinsuppWithin U Int} :
    (↑(∑ᶠ i, F i) : X -> Int) = ∑ᶠ i, (F i : X -> Int) := by
  have : F.support = (fun i => (F i : X -> Int)).support := by
    simp [Set.ext_iff, DFunLike.ext_iff, funext_iff]
  by_cases h : F.support.Finite
  · rw [finsum_eq_sum F h, Function.locallyFinsuppWithin.coe_sum]
    have h₂ : (fun i => (F i : X -> Int)).support.Finite := by simp_all
    simp_all [finsum_eq_sum _ h₂]
  · simp_all [finsum_of_infinite_support]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddGroup
  signature: Y] : AddGroup (locallyFinsuppWithin U Y)
  body: Injective.addGroup (M₁ := locallyFinsuppWithin U Y) (M₂ := X -> Y)
    _ coe_injective coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

中文:
实例 [AddGroup
  签名: Y] : AddGroup (locallyFinsuppWithin U Y)
  定义体: Injective.addGroup (M₁ := locallyFinsuppWithin U Y) (M₂ := X -> Y)
    _ coe_injective coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

Depends on / 依赖: Injective, Injective.addGroup, addGroup, coe_add, coe_injective, coe_neg, coe_nsmul, coe_sub, coe_zero, coe_zsmul, locallyFinsuppWithin
-/
instance [AddGroup Y] : AddGroup (locallyFinsuppWithin U Y) :=
  Injective.addGroup (M₁ := locallyFinsuppWithin U Y) (M₂ := X -> Y)
    _ coe_injective coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

/--
lemma `support_neg` / 引理 `support_neg`

English:
lemma support_neg
  given: [AddGroup Y] (D : locallyFinsuppWithin U Y)
  proof: by rw [support, coe_neg, Function.support_neg]

中文:
引理 support_neg
  条件: [AddGroup Y] (D : locallyFinsuppWithin U Y)
  证明: by rw [support, coe_neg, Function.support_neg]
-/
@[simp] lemma support_neg [AddGroup Y] (D : locallyFinsuppWithin U Y) :
    (-D).support = D.support := by rw [support, coe_neg, Function.support_neg]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommGroup
  signature: Y] : AddCommGroup (locallyFinsuppWithin U Y)
  body: Injective.addCommGroup (M₁ := locallyFinsuppWithin U Y) (M₂ := X -> Y)
    _ coe_injective coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

中文:
实例 [AddCommGroup
  签名: Y] : AddCommGroup (locallyFinsuppWithin U Y)
  定义体: Injective.addCommGroup (M₁ := locallyFinsuppWithin U Y) (M₂ := X -> Y)
    _ coe_injective coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

Depends on / 依赖: Injective, Injective.addCommGroup, addCommGroup, coe_add, coe_injective, coe_neg, coe_nsmul, coe_sub, coe_zero, coe_zsmul, locallyFinsuppWithin
-/
instance [AddCommGroup Y] : AddCommGroup (locallyFinsuppWithin U Y) :=
  Injective.addCommGroup (M₁ := locallyFinsuppWithin U Y) (M₂ := X -> Y)
    _ coe_injective coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LE
  signature: Y] [Zero Y] : LE (locallyFinsuppWithin U Y) where
  body: fun D₁ D₂ => (D₁ : X -> Y) <= D₂

中文:
实例 [LE
  签名: Y] [Zero Y] : LE (locallyFinsuppWithin U Y) where
  定义体: fun D₁ D₂ => (D₁ : X -> Y) <= D₂
-/
instance [LE Y] [Zero Y] : LE (locallyFinsuppWithin U Y) where
  le := fun D₁ D₂ => (D₁ : X -> Y) <= D₂

/--
lemma `le_def` / 引理 `le_def`

English:
lemma le_def
  given: [LE Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y}
  proof: ⟨(·),(·)⟩

中文:
引理 le_def
  条件: [LE Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y}
  证明: ⟨(·),(·)⟩
-/
lemma le_def [LE Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} :
    D₁ <= D₂ ↔ (D₁ : X -> Y) <= (D₂ : X -> Y) := ⟨(·),(·)⟩

/--
lemma `single_nonneg` / 引理 `single_nonneg`

English:
lemma single_nonneg
  given: [DecidableEq X] [Zero Y] [Preorder Y] {x : X} {y : Y}
  proof: by
  simp only [le_def, coe_single]
  apply Pi.single_nonneg

中文:
引理 single_nonneg
  条件: [DecidableEq X] [Zero Y] [Preorder Y] {x : X} {y : Y}
  证明: by
  simp only [le_def, coe_single]
  apply Pi.single_nonneg

Depends on / 依赖: Pi.single_nonneg, coe_single, le_def, single_nonneg
-/
lemma single_nonneg [DecidableEq X] [Zero Y] [Preorder Y] {x : X} {y : Y} :
    0 <= single x y ↔ 0 <= y := by
  simp only [le_def, coe_single]
  apply Pi.single_nonneg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: Y] [Zero Y] : LT (locallyFinsuppWithin U Y) where
  body: fun D₁ D₂ => (D₁ : X -> Y) < D₂

中文:
实例 [Preorder
  签名: Y] [Zero Y] : LT (locallyFinsuppWithin U Y) where
  定义体: fun D₁ D₂ => (D₁ : X -> Y) < D₂
-/
instance [Preorder Y] [Zero Y] : LT (locallyFinsuppWithin U Y) where
  lt := fun D₁ D₂ => (D₁ : X -> Y) < D₂

/--
lemma `lt_def` / 引理 `lt_def`

English:
lemma lt_def
  given: [Preorder Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y}
  proof: ⟨(·),(·)⟩

中文:
引理 lt_def
  条件: [Preorder Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y}
  证明: ⟨(·),(·)⟩
-/
lemma lt_def [Preorder Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} :
    D₁ < D₂ ↔ (D₁ : X -> Y) < (D₂ : X -> Y) := ⟨(·),(·)⟩

/--
lemma `single_pos` / 引理 `single_pos`

English:
lemma single_pos
  given: [DecidableEq X] [Zero Y] [Preorder Y] {x : X} {y : Y}
  proof: by
  rw [lt_def]; rw [coe_single]
  exact Pi.single_pos

中文:
引理 single_pos
  条件: [DecidableEq X] [Zero Y] [Preorder Y] {x : X} {y : Y}
  证明: by
  rw [lt_def]; rw [coe_single]
  exact Pi.single_pos

Depends on / 依赖: Pi.single_pos, coe_single, lt_def, single_pos
-/
lemma single_pos [DecidableEq X] [Zero Y] [Preorder Y] {x : X} {y : Y} :
    0 < single x y ↔ 0 < y := by
  rw [lt_def]; rw [coe_single]
  exact Pi.single_pos

/--
lemma `single_pos_nat_one` / 引理 `single_pos_nat_one`

English:
lemma single_pos_nat_one
  given: [DecidableEq X] {x : X}
  proof: single_pos.2 Nat.one_pos

中文:
引理 single_pos_nat_one
  条件: [DecidableEq X] {x : X}
  证明: single_pos.2 Nat.one_pos
-/
@[simp] lemma single_pos_nat_one [DecidableEq X] {x : X} :
    0 < single x 1 := single_pos.2 Nat.one_pos

/--
lemma `single_pos_int_one` / 引理 `single_pos_int_one`

English:
lemma single_pos_int_one
  given: [DecidableEq X] {x : X}
  proof: single_pos.2 Int.one_pos

中文:
引理 single_pos_int_one
  条件: [DecidableEq X] {x : X}
  证明: single_pos.2 Int.one_pos
-/
@[simp] lemma single_pos_int_one [DecidableEq X] {x : X} :
    0 < single x (1 : Int) := single_pos.2 Int.one_pos

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SemilatticeSup
  signature: Y] [Zero Y] : Max (locallyFinsuppWithin U Y) where
  body: { toFun z := max (D₁ z) (D₂ z)
    supportWithinDomain' := by
      intro x
      contrapose
      intro hx
      simp [notMem_support.1 fun a => hx (D₁.supportWithinDomain a),
        notMem_support.1 fun a => hx (D₂.supportWithinDomain a)]
    supportLocallyFiniteWithinDomain' := by
      intro z 

中文:
实例 [SemilatticeSup
  签名: Y] [Zero Y] : Max (locallyFinsuppWithin U Y) where
  定义体: { toFun z := max (D₁ z) (D₂ z)
    supportWithinDomain' := by
      intro x
      contrapose
      intro hx
      simp [notMem_support.1 fun a => hx (D₁.supportWithinDomain a),
        notMem_support.1 fun a => hx (D₂.supportWithinDomain a)]
    supportLocallyFiniteWithinDomain' := by
      intro z 

Depends on / 依赖: Finite, Set.Finite.subset, contrapose, inter_mem, notMem_support, subset, support, supportLocallyFiniteWithinDomain, supportWithinDomain
-/
instance [SemilatticeSup Y] [Zero Y] : Max (locallyFinsuppWithin U Y) where
  max D₁ D₂ :=
  { toFun z := max (D₁ z) (D₂ z)
    supportWithinDomain' := by
      intro x
      contrapose
      intro hx
      simp [notMem_support.1 fun a => hx (D₁.supportWithinDomain a),
        notMem_support.1 fun a => hx (D₂.supportWithinDomain a)]
    supportLocallyFiniteWithinDomain' := by
      intro z hz
      obtain ⟨t₁, ht₁⟩ := D₁.supportLocallyFiniteWithinDomain z hz
      obtain ⟨t₂, ht₂⟩ := D₂.supportLocallyFiniteWithinDomain z hz
      use t₁ inter t₂, inter_mem ht₁.1 ht₂.1
      apply Set.Finite.subset (s := (t₁ inter D₁.support) union (t₂ inter D₂.support)) (ht₁.2.union ht₂.2)
      intro a ha
      simp_all only [mem_inter_iff, mem_support, ne_eq, mem_union, true_and]
      by_contra! hCon
      simp_all }

@[simp]
/--
lemma `max_apply` / 引理 `max_apply`

English:
lemma max_apply
  given: [SemilatticeSup Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} {x : X}
  proof: rfl

中文:
引理 max_apply
  条件: [SemilatticeSup Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} {x : X}
  证明: rfl
-/
lemma max_apply [SemilatticeSup Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} {x : X} :
    max D₁ D₂ x = max (D₁ x) (D₂ x) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SemilatticeInf
  signature: Y] [Zero Y] : Min (locallyFinsuppWithin U Y) where
  body: { toFun z := min (D₁ z) (D₂ z)
    supportWithinDomain' := by
      intro x
      contrapose
      intro hx
      simp [notMem_support.1 fun a => hx (D₁.supportWithinDomain a),
        notMem_support.1 fun a => hx (D₂.supportWithinDomain a)]
    supportLocallyFiniteWithinDomain' := by
      intro z 

中文:
实例 [SemilatticeInf
  签名: Y] [Zero Y] : Min (locallyFinsuppWithin U Y) where
  定义体: { toFun z := min (D₁ z) (D₂ z)
    supportWithinDomain' := by
      intro x
      contrapose
      intro hx
      simp [notMem_support.1 fun a => hx (D₁.supportWithinDomain a),
        notMem_support.1 fun a => hx (D₂.supportWithinDomain a)]
    supportLocallyFiniteWithinDomain' := by
      intro z 

Depends on / 依赖: Finite, Set.Finite.subset, contrapose, inter_mem, notMem_support, subset, support, supportLocallyFiniteWithinDomain, supportWithinDomain
-/
instance [SemilatticeInf Y] [Zero Y] : Min (locallyFinsuppWithin U Y) where
  min D₁ D₂ :=
  { toFun z := min (D₁ z) (D₂ z)
    supportWithinDomain' := by
      intro x
      contrapose
      intro hx
      simp [notMem_support.1 fun a => hx (D₁.supportWithinDomain a),
        notMem_support.1 fun a => hx (D₂.supportWithinDomain a)]
    supportLocallyFiniteWithinDomain' := by
      intro z hz
      obtain ⟨t₁, ht₁⟩ := D₁.supportLocallyFiniteWithinDomain z hz
      obtain ⟨t₂, ht₂⟩ := D₂.supportLocallyFiniteWithinDomain z hz
      use t₁ inter t₂, inter_mem ht₁.1 ht₂.1
      apply Set.Finite.subset (s := (t₁ inter D₁.support) union (t₂ inter D₂.support)) (ht₁.2.union ht₂.2)
      intro a ha
      simp_all only [mem_inter_iff, mem_support, ne_eq, mem_union, true_and]
      by_contra! hCon
      simp_all }

@[simp]
/--
lemma `min_apply` / 引理 `min_apply`

English:
lemma min_apply
  given: [SemilatticeInf Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} {x : X}
  proof: rfl

中文:
引理 min_apply
  条件: [SemilatticeInf Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} {x : X}
  证明: rfl
-/
lemma min_apply [SemilatticeInf Y] [Zero Y] {D₁ D₂ : locallyFinsuppWithin U Y} {x : X} :
    min D₁ D₂ x = min (D₁ x) (D₂ x) := rfl

section Lattice
variable [Lattice Y]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: Y] : Lattice (locallyFinsuppWithin U Y) where
  body: by simp [le_def]
  le_trans D₁ D₂ D₃ h₁₂ h₂₃ := fun x => (h₁₂ x).trans (h₂₃ x)
  le_antisymm D₁ D₂ h₁₂ h₂₁ := by
    ext x
    exact le_antisymm (h₁₂ x) (h₂₁ x)
  sup := max
  le_sup_left D₁ D₂ := fun x => by simp
  le_sup_right D₁ D₂ := fun x => by simp
  sup_le D₁ D₂ D₃ h₁₃ h₂₃ := fun x => by simp

中文:
实例 [Zero
  签名: Y] : Lattice (locallyFinsuppWithin U Y) where
  定义体: by simp [le_def]
  le_trans D₁ D₂ D₃ h₁₂ h₂₃ := fun x => (h₁₂ x).trans (h₂₃ x)
  le_antisymm D₁ D₂ h₁₂ h₂₁ := by
    ext x
    exact le_antisymm (h₁₂ x) (h₂₁ x)
  sup := max
  le_sup_left D₁ D₂ := fun x => by simp
  le_sup_right D₁ D₂ := fun x => by simp
  sup_le D₁ D₂ D₃ h₁₃ h₂₃ := fun x => by simp

Depends on / 依赖: inf_le_left, inf_le_right, le_antisymm, le_def, le_inf, le_sup_left, le_sup_right, le_trans, sup_le
-/
instance [Zero Y] : Lattice (locallyFinsuppWithin U Y) where
  le_refl := by simp [le_def]
  le_trans D₁ D₂ D₃ h₁₂ h₂₃ := fun x => (h₁₂ x).trans (h₂₃ x)
  le_antisymm D₁ D₂ h₁₂ h₂₁ := by
    ext x
    exact le_antisymm (h₁₂ x) (h₂₁ x)
  sup := max
  le_sup_left D₁ D₂ := fun x => by simp
  le_sup_right D₁ D₂ := fun x => by simp
  sup_le D₁ D₂ D₃ h₁₃ h₂₃ := fun x => by simp [h₁₃ x, h₂₃ x]
  inf := min
  inf_le_left D₁ D₂ := fun x => by simp
  inf_le_right D₁ D₂ := fun x => by simp
  le_inf D₁ D₂ D₃ h₁₃ h₂₃ := fun x => by simp [h₁₃ x, h₂₃ x]

variable [AddCommGroup Y]

/--
lemma `posPart_apply` / 引理 `posPart_apply`

English:
lemma posPart_apply
  given: (a : locallyFinsuppWithin U Y) (x : X)
  statement: a⁺ x = (a x)⁺
  proof: rfl

中文:
引理 posPart_apply
  条件: (a : locallyFinsuppWithin U Y) (x : X)
  结论: a⁺ x = (a x)⁺
  证明: rfl
-/
@[simp] lemma posPart_apply (a : locallyFinsuppWithin U Y) (x : X) : a⁺ x = (a x)⁺ := rfl
/--
lemma `negPart_apply` / 引理 `negPart_apply`

English:
lemma negPart_apply
  given: (a : locallyFinsuppWithin U Y) (x : X)
  statement: a⁻ x = (a x)⁻
  proof: rfl

中文:
引理 negPart_apply
  条件: (a : locallyFinsuppWithin U Y) (x : X)
  结论: a⁻ x = (a x)⁻
  证明: rfl
-/
@[simp] lemma negPart_apply (a : locallyFinsuppWithin U Y) (x : X) : a⁻ x = (a x)⁻ := rfl

end Lattice

section LinearOrder
variable [AddCommGroup Y] [LinearOrder Y] [IsOrderedAddMonoid Y]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedAddMonoid (locallyFinsuppWithin U Y)
  body: fun _ _ _ _ => by simpa [le_def]

中文:
实例 :
  签名: IsOrderedAddMonoid (locallyFinsuppWithin U Y)
  定义体: fun _ _ _ _ => by simpa [le_def]

Depends on / 依赖: le_def
-/
instance : IsOrderedAddMonoid (locallyFinsuppWithin U Y) where
  add_le_add_left := fun _ _ _ _ => by simpa [le_def]

/--
theorem `posPart_add` / 定理 `posPart_add`

English:
theorem posPart_add
  given: (f₁ f₂ : Function.locallyFinsuppWithin U Y)
  proof: by
  repeat rw [posPart_def]
  intro x
  simp only [Function.locallyFinsuppWithin.max_apply, Function.locallyFinsuppWithin.coe_add,
    Pi.add_apply, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, sup_le_iff]
  constructor
  · simp [add_le_add]
  · simp [add_nonneg]

中文:
定理 posPart_add
  条件: (f₁ f₂ : Function.locallyFinsuppWithin U Y)
  证明: by
  repeat rw [posPart_def]
  intro x
  simp only [Function.locallyFinsuppWithin.max_apply, Function.locallyFinsuppWithin.coe_add,
    Pi.add_apply, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, sup_le_iff]
  constructor
  · simp [add_le_add]
  · simp [add_nonneg]

Depends on / 依赖: Function, Function.locallyFinsuppWithin.coe_add, Function.locallyFinsuppWithin.coe_zero, Function.locallyFinsuppWithin.max_apply, Pi.add_apply, Pi.zero_apply, add_apply, add_le_add, add_nonneg, coe_add, coe_zero, locallyFinsuppWithin, max_apply, posPart_def, repeat, sup_le_iff, zero_apply
-/
theorem posPart_add (f₁ f₂ : Function.locallyFinsuppWithin U Y) :
    (f₁ + f₂)⁺ <= f₁⁺ + f₂⁺ := by
  repeat rw [posPart_def]
  intro x
  simp only [Function.locallyFinsuppWithin.max_apply, Function.locallyFinsuppWithin.coe_add,
    Pi.add_apply, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, sup_le_iff]
  constructor
  · simp [add_le_add]
  · simp [add_nonneg]

/--
theorem `negPart_add` / 定理 `negPart_add`

English:
theorem negPart_add
  given: (f₁ f₂ : Function.locallyFinsuppWithin U Y)
  proof: by
  repeat rw [negPart_def]
  intro x
  simp only [neg_add_rev, Function.locallyFinsuppWithin.max_apply,
    Function.locallyFinsuppWithin.coe_add, Function.locallyFinsuppWithin.coe_neg, Pi.add_apply,
    Pi.neg_apply, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, sup_le_iff]
  constructor

中文:
定理 negPart_add
  条件: (f₁ f₂ : Function.locallyFinsuppWithin U Y)
  证明: by
  repeat rw [negPart_def]
  intro x
  simp only [neg_add_rev, Function.locallyFinsuppWithin.max_apply,
    Function.locallyFinsuppWithin.coe_add, Function.locallyFinsuppWithin.coe_neg, Pi.add_apply,
    Pi.neg_apply, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, sup_le_iff]
  constructor

Depends on / 依赖: Function, Function.locallyFinsuppWithin.coe_add, Function.locallyFinsuppWithin.coe_neg, Function.locallyFinsuppWithin.coe_zero, Function.locallyFinsuppWithin.max_apply, Pi.add_apply, Pi.neg_apply, Pi.zero_apply, add_apply, add_comm, add_le_add, add_nonneg, coe_add, coe_neg, coe_zero, locallyFinsuppWithin, max_apply, negPart_def, neg_add_rev, neg_apply
-/
theorem negPart_add (f₁ f₂ : Function.locallyFinsuppWithin U Y) :
    (f₁ + f₂)⁻ <= f₁⁻ + f₂⁻ := by
  repeat rw [negPart_def]
  intro x
  simp only [neg_add_rev, Function.locallyFinsuppWithin.max_apply,
    Function.locallyFinsuppWithin.coe_add, Function.locallyFinsuppWithin.coe_neg, Pi.add_apply,
    Pi.neg_apply, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, sup_le_iff]
  constructor
  · simp [add_comm, add_le_add]
  · simp [add_nonneg]

/--
Taking the positive part of a function with locally finite support commutes with
scalar multiplication by a natural number.
-/
@[simp]
/--
theorem `nsmul_posPart` / 定理 `nsmul_posPart`

English:
theorem nsmul_posPart
  given: (n : Nat) (f : locallyFinsuppWithin U Y)
  statement: (n • f)⁺ = n • f⁺
  proof: by
  ext x
  simp only [posPart, max_apply, coe_nsmul, Pi.smul_apply, coe_zero, Pi.zero_apply]
  by_cases h : f x < 0
  · simpa [max_eq_right_of_lt h] using nsmul_le_nsmul_right h.le n
  · simpa [not_lt.1 h] using nsmul_nonneg (not_lt.1 h) n

中文:
定理 nsmul_posPart
  条件: (n : 自然数) (f : locallyFinsuppWithin U Y)
  结论: (n • f)⁺ = n • f⁺
  证明: by
  ext x
  simp only [posPart, max_apply, coe_nsmul, Pi.smul_apply, coe_zero, Pi.zero_apply]
  by_cases h : f x < 0
  · simpa [max_eq_right_of_lt h] using nsmul_le_nsmul_right h.le n
  · simpa [not_lt.1 h] using nsmul_nonneg (not_lt.1 h) n

Depends on / 依赖: Pi.smul_apply, Pi.zero_apply, coe_nsmul, coe_zero, h.le, max_apply, max_eq_right_of_lt, not_lt, nsmul_le_nsmul_right, nsmul_nonneg, posPart, smul_apply, zero_apply
-/
theorem nsmul_posPart (n : Nat) (f : locallyFinsuppWithin U Y) : (n • f)⁺ = n • f⁺ := by
  ext x
  simp only [posPart, max_apply, coe_nsmul, Pi.smul_apply, coe_zero, Pi.zero_apply]
  by_cases h : f x < 0
  · simpa [max_eq_right_of_lt h] using nsmul_le_nsmul_right h.le n
  · simpa [not_lt.1 h] using nsmul_nonneg (not_lt.1 h) n

/--
Taking the negative part of a function with locally finite support commutes with
scalar multiplication by a natural number.
-/
@[simp]
/--
theorem `nsmul_negPart` / 定理 `nsmul_negPart`

English:
theorem nsmul_negPart
  given: (n : Nat) (f : locallyFinsuppWithin U Y)
  statement: (n • f)⁻ = n • f⁻
  proof: by
  ext x
  simp only [negPart, max_apply, coe_neg, coe_nsmul, Pi.neg_apply, Pi.smul_apply, coe_zero,
    Pi.zero_apply]
  by_cases h : -f x < 0
  · simpa [max_eq_right_of_lt h] using nsmul_le_nsmul_right h.le n
  · simpa [not_lt.1 h] using nsmul_nonneg (not_lt.1 h) n

中文:
定理 nsmul_negPart
  条件: (n : 自然数) (f : locallyFinsuppWithin U Y)
  结论: (n • f)⁻ = n • f⁻
  证明: by
  ext x
  simp only [negPart, max_apply, coe_neg, coe_nsmul, Pi.neg_apply, Pi.smul_apply, coe_zero,
    Pi.zero_apply]
  by_cases h : -f x < 0
  · simpa [max_eq_right_of_lt h] using nsmul_le_nsmul_right h.le n
  · simpa [not_lt.1 h] using nsmul_nonneg (not_lt.1 h) n

Depends on / 依赖: Pi.neg_apply, Pi.smul_apply, Pi.zero_apply, coe_neg, coe_nsmul, coe_zero, h.le, max_apply, max_eq_right_of_lt, negPart, neg_apply, not_lt, nsmul_le_nsmul_right, nsmul_nonneg, smul_apply, zero_apply
-/
theorem nsmul_negPart (n : Nat) (f : locallyFinsuppWithin U Y) : (n • f)⁻ = n • f⁻ := by
  ext x
  simp only [negPart, max_apply, coe_neg, coe_nsmul, Pi.neg_apply, Pi.smul_apply, coe_zero,
    Pi.zero_apply]
  by_cases h : -f x < 0
  · simpa [max_eq_right_of_lt h] using nsmul_le_nsmul_right h.le n
  · simpa [not_lt.1 h] using nsmul_nonneg (not_lt.1 h) n

/--
lemma `exists_single_le_pos` / 引理 `exists_single_le_pos`

English:
lemma exists_single_le_pos
  given: [DecidableEq X] {D : locallyFinsupp X Int} (h : 0 < D)
  proof: by
  obtain ⟨z, hz⟩ : exists z, D z != 0 := by simpa [D.ext_iff] using! (ne_of_lt h).symm
  refine ⟨z, fun e => ?_⟩
  obtain (rfl | he) := eq_or_ne e z
  · simpa [single_apply] using! Int.lt_iff_le_and_ne.mpr ⟨h.le e, hz.symm⟩
  · simpa [he, single_apply] using! h.le e

中文:
引理 exists_single_le_pos
  条件: [DecidableEq X] {D : locallyFinsupp X 整数} (h : 0 < D)
  证明: by
  obtain ⟨z, hz⟩ : exists z, D z != 0 := by simpa [D.ext_iff] using! (ne_of_lt h).symm
  refine ⟨z, fun e => ?_⟩
  obtain (rfl | he) := eq_or_ne e z
  · simpa [single_apply] using! Int.lt_iff_le_and_ne.mpr ⟨h.le e, hz.symm⟩
  · simpa [he, single_apply] using! h.le e

Depends on / 依赖: D.ext_iff, Int.lt_iff_le_and_ne.mpr, eq_or_ne, ext_iff, h.le, hz.symm, lt_iff_le_and_ne, ne_of_lt, single_apply
-/
lemma exists_single_le_pos [DecidableEq X] {D : locallyFinsupp X Int} (h : 0 < D) :
    exists e, single e 1 <= D := by
  obtain ⟨z, hz⟩ : exists z, D z != 0 := by simpa [D.ext_iff] using! (ne_of_lt h).symm
  refine ⟨z, fun e => ?_⟩
  obtain (rfl | he) := eq_or_ne e z
  · simpa [single_apply] using! Int.lt_iff_le_and_ne.mpr ⟨h.le e, hz.symm⟩
  · simpa [he, single_apply] using! h.le e

end LinearOrder

/-!
## Restriction
-/

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V subseteq U)
  body: by
    classical
    exact fun z => if hz : z in V then D z else 0
  supportWithinDomain' := by
    intro x hx
    simp_rw [dite_eq_ite, mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hx
    exact hx.1
  supportLocallyFiniteWithinDomain' := by
    intro z hz
    obtain ⟨t, ht⟩ := D.supp

中文:
定义 restrict
  签名: [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V subseteq U)
  定义体: by
    classical
    exact fun z => if hz : z in V then D z else 0
  supportWithinDomain' := by
    intro x hx
    simp_rw [dite_eq_ite, mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hx
    exact hx.1
  supportLocallyFiniteWithinDomain' := by
    intro z hz
    obtain ⟨t, ht⟩ := D.supp

Depends on / 依赖: Classical, Classical.not_imp, D.support, D.supportLocallyFiniteWithinDomain, Finite, Set.Finite.subset, classical, dite_eq_ite, ite_eq_right_iff, mem_support, ne_eq, not_imp, simp_rw, subset, support, supportLocallyFiniteWithinDomain, supportWithinDomain
-/
noncomputable def restrict [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V subseteq U) :
    locallyFinsuppWithin V Y where
  toFun := by
    classical
    exact fun z => if hz : z in V then D z else 0
  supportWithinDomain' := by
    intro x hx
    simp_rw [dite_eq_ite, mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hx
    exact hx.1
  supportLocallyFiniteWithinDomain' := by
    intro z hz
    obtain ⟨t, ht⟩ := D.supportLocallyFiniteWithinDomain z (h hz)
    use t, ht.1
    apply Set.Finite.subset (s := t inter D.support) ht.2
    intro _ _
    simp_all

open scoped Classical in
/--
lemma `restrict_apply` / 引理 `restrict_apply`

English:
lemma restrict_apply
  given: [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V subseteq U) (z : X)
  proof: rfl

中文:
引理 restrict_apply
  条件: [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V subseteq U) (z : X)
  证明: rfl
-/
lemma restrict_apply [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V subseteq U) (z : X) :
    (D.restrict h) z = if z in V then D z else 0 := rfl

/--
lemma `restrict_eqOn` / 引理 `restrict_eqOn`

English:
lemma restrict_eqOn
  given: [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V subseteq U)
  proof: by
  intro _ _
  simp_all [restrict_apply]

中文:
引理 restrict_eqOn
  条件: [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V subseteq U)
  证明: by
  intro _ _
  simp_all [restrict_apply]

Depends on / 依赖: restrict_apply
-/
lemma restrict_eqOn [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V subseteq U) :
    Set.EqOn (D.restrict h) D V := by
  intro _ _
  simp_all [restrict_apply]

/--
lemma `restrict_eqOn_compl` / 引理 `restrict_eqOn_compl`

English:
lemma restrict_eqOn_compl
  given: [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V subseteq U)
  proof: by
  intro _ hx
  simp_all

中文:
引理 restrict_eqOn_compl
  条件: [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V subseteq U)
  证明: by
  intro _ hx
  simp_all
-/
lemma restrict_eqOn_compl [Zero Y] {V : Set X} (D : locallyFinsuppWithin U Y) (h : V subseteq U) :
    Set.EqOn (D.restrict h) 0 Vᶜ := by
  intro _ hx
  simp_all

/--
lemma `restrict_zero` / 引理 `restrict_zero`

English:
lemma restrict_zero
  given: [Zero Y] {U V : Set X} (hV : V subseteq U)
  proof: by
  ext
  rw [restrict_apply]
  aesop

中文:
引理 restrict_zero
  条件: [Zero Y] {U V : Set X} (hV : V subseteq U)
  证明: by
  ext
  rw [restrict_apply]
  aesop
-/
@[simp] lemma restrict_zero [Zero Y] {U V : Set X} (hV : V subseteq U) :
    restrict (0 : Function.locallyFinsuppWithin U Y) hV = 0 := by
  ext
  rw [restrict_apply]
  aesop

/--
Definition of `restrictMonoidHom` / `restrictMonoidHom` 的定义

English:
definition restrictMonoidHom
  signature: [AddCommGroup Y] {V : Set X} (h : V subseteq U)
  body: D.restrict h
  map_zero' := by
    ext x
    simp [restrict_apply]
  map_add' D₁ D₂ := by
    ext x
    by_cases hx : x in V
    <;> simp [restrict_apply, hx]

@[simp]

中文:
定义 restrictMonoidHom
  签名: [AddCommGroup Y] {V : Set X} (h : V subseteq U)
  定义体: D.restrict h
  map_zero' := by
    ext x
    simp [restrict_apply]
  map_add' D₁ D₂ := by
    ext x
    by_cases hx : x in V
    <;> simp [restrict_apply, hx]

@[simp]

Depends on / 依赖: D.restrict, restrict
-/
noncomputable def restrictMonoidHom [AddCommGroup Y] {V : Set X} (h : V subseteq U) :
    locallyFinsuppWithin U Y ->+ locallyFinsuppWithin V Y where
  toFun D := D.restrict h
  map_zero' := by
    ext x
    simp [restrict_apply]
  map_add' D₁ D₂ := by
    ext x
    by_cases hx : x in V
    <;> simp [restrict_apply, hx]

@[simp]
/--
lemma `restrictMonoidHom_apply` / 引理 `restrictMonoidHom_apply`

English:
lemma restrictMonoidHom_apply
  statement: [AddCommGroup Y] {V : Set X} (D : locallyFinsuppWithin U Y)
  proof: by rfl

中文:
引理 restrictMonoidHom_apply
  结论: [AddCommGroup Y] {V : Set X} (D : locallyFinsuppWithin U Y)
  证明: by rfl
-/
lemma restrictMonoidHom_apply [AddCommGroup Y] {V : Set X} (D : locallyFinsuppWithin U Y)
    (h : V subseteq U) :
    restrictMonoidHom h D = D.restrict h := by rfl

/--
lemma `sum_apply_smul_single_eq_self` / 引理 `sum_apply_smul_single_eq_self`

English:
lemma sum_apply_smul_single_eq_self
  statement: [DecidableEq X] [AddCommMonoid Y] {U : Set X}
  proof: by
  have : (fun x => (single x (F x)).restrict (subset_univ U)).support subseteq h.toFinset := by
    intro
    contrapose
    aesop
  rw [finsum_eq_sum_of_support_subset _ this]
  ext z
  by_cases hz : z ∉ U
  · aesop
  simp [restrict_apply]
  by_cases hz : z in F.support
  · aesop
  · aesop

中文:
引理 sum_apply_smul_single_eq_self
  结论: [DecidableEq X] [AddCommMonoid Y] {U : Set X}
  证明: by
  have : (fun x => (single x (F x)).restrict (subset_univ U)).support subseteq h.toFinset := by
    intro
    contrapose
    aesop
  rw [finsum_eq_sum_of_support_subset _ this]
  ext z
  by_cases hz : z ∉ U
  · aesop
  simp [restrict_apply]
  by_cases hz : z in F.support
  · aesop
  · aesop
-/
@[simp] lemma sum_apply_smul_single_eq_self [DecidableEq X] [AddCommMonoid Y] {U : Set X}
    {F : Function.locallyFinsuppWithin U Y} (h : F.support.Finite) :
    ∑ᶠ x, ((single x (F x)).restrict (subset_univ U)) = F := by
  have : (fun x => (single x (F x)).restrict (subset_univ U)).support subseteq h.toFinset := by
    intro
    contrapose
    aesop
  rw [finsum_eq_sum_of_support_subset _ this]
  ext z
  by_cases hz : z ∉ U
  · aesop
  simp [restrict_apply]
  by_cases hz : z in F.support
  · aesop
  · aesop

/--
lemma `sum_apply_smul_single_eq_self_on_univ` / 引理 `sum_apply_smul_single_eq_self_on_univ`

English:
lemma sum_apply_smul_single_eq_self_on_univ
  statement: [DecidableEq X] {D : locallyFinsupp X Int}
  proof: by
  ext w
  simp only [coe_sum, Finset.sum_apply, single_apply, Finset.sum_ite_eq]
  set s := h.toFinset with hs
  by_cases hw : w in s
  · simp [hw]
  · simp only [hw, if_false]
    have : w ∉ support D := by simpa only [hs, Set.Finite.mem_toFinset] using hw
    exact (notMem_support.mp this).symm

中文:
引理 sum_apply_smul_single_eq_self_on_univ
  结论: [DecidableEq X] {D : locallyFinsupp X 整数}
  证明: by
  ext w
  simp only [coe_sum, Finset.sum_apply, single_apply, Finset.sum_ite_eq]
  set s := h.toFinset with hs
  by_cases hw : w in s
  · simp [hw]
  · simp only [hw, if_false]
    have : w ∉ support D := by simpa only [hs, Set.Finite.mem_toFinset] using hw
    exact (notMem_support.mp this).symm
-/
@[simp] lemma sum_apply_smul_single_eq_self_on_univ [DecidableEq X] {D : locallyFinsupp X Int}
    (h : D.support.Finite) :
    ∑ z in h.toFinset, single z (D z) = D := by
  ext w
  simp only [coe_sum, Finset.sum_apply, single_apply, Finset.sum_ite_eq]
  set s := h.toFinset with hs
  by_cases hw : w in s
  · simp [hw]
  · simp only [hw, if_false]
    have : w ∉ support D := by simpa only [hs, Set.Finite.mem_toFinset] using hw
    exact (notMem_support.mp this).symm

/--
Definition of `restrictLatticeHom` / `restrictLatticeHom` 的定义

English:
definition restrictLatticeHom
  signature: [AddCommGroup Y] [Lattice Y] {V : Set X} (h : V subseteq U)
  body: D.restrict h
  map_sup' D₁ D₂ := by
    ext x
    by_cases hx : x in V
    <;> simp [locallyFinsuppWithin.restrict_apply, hx]
  map_inf' D₁ D₂ := by
    ext x
    by_cases hx : x in V
    <;> simp [locallyFinsuppWithin.restrict_apply, hx]

@[simp]

中文:
定义 restrictLatticeHom
  签名: [AddCommGroup Y] [Lattice Y] {V : Set X} (h : V subseteq U)
  定义体: D.restrict h
  map_sup' D₁ D₂ := by
    ext x
    by_cases hx : x in V
    <;> simp [locallyFinsuppWithin.restrict_apply, hx]
  map_inf' D₁ D₂ := by
    ext x
    by_cases hx : x in V
    <;> simp [locallyFinsuppWithin.restrict_apply, hx]

@[simp]

Depends on / 依赖: D.restrict, restrict
-/
noncomputable def restrictLatticeHom [AddCommGroup Y] [Lattice Y] {V : Set X} (h : V subseteq U) :
    LatticeHom (locallyFinsuppWithin U Y) (locallyFinsuppWithin V Y) where
  toFun D := D.restrict h
  map_sup' D₁ D₂ := by
    ext x
    by_cases hx : x in V
    <;> simp [locallyFinsuppWithin.restrict_apply, hx]
  map_inf' D₁ D₂ := by
    ext x
    by_cases hx : x in V
    <;> simp [locallyFinsuppWithin.restrict_apply, hx]

@[simp]
/--
lemma `restrictLatticeHom_apply` / 引理 `restrictLatticeHom_apply`

English:
lemma restrictLatticeHom_apply
  statement: [AddCommGroup Y] [Lattice Y] {V : Set X}
  proof: by rfl

中文:
引理 restrictLatticeHom_apply
  结论: [AddCommGroup Y] [Lattice Y] {V : Set X}
  证明: by rfl
-/
lemma restrictLatticeHom_apply [AddCommGroup Y] [Lattice Y] {V : Set X}
    (D : locallyFinsuppWithin U Y) (h : V subseteq U) :
    restrictLatticeHom h D = D.restrict h := by rfl
/--
lemma `restrict_posPart` / 引理 `restrict_posPart`

English:
lemma restrict_posPart
  given: {V : Set X} (D : locallyFinsuppWithin U Int) (h : V subseteq U)
  proof: by
  ext x
  simp only [locallyFinsuppWithin.restrict_apply, locallyFinsuppWithin.posPart_apply]
  aesop

中文:
引理 restrict_posPart
  条件: {V : Set X} (D : locallyFinsuppWithin U 整数) (h : V subseteq U)
  证明: by
  ext x
  simp only [locallyFinsuppWithin.restrict_apply, locallyFinsuppWithin.posPart_apply]
  aesop

Depends on / 依赖: locallyFinsuppWithin, locallyFinsuppWithin.posPart_apply, locallyFinsuppWithin.restrict_apply, posPart_apply, restrict_apply
-/
lemma restrict_posPart {V : Set X} (D : locallyFinsuppWithin U Int) (h : V subseteq U) :
    D⁺.restrict h = (D.restrict h)⁺ := by
  ext x
  simp only [locallyFinsuppWithin.restrict_apply, locallyFinsuppWithin.posPart_apply]
  aesop

/--
lemma `restrict_negPart` / 引理 `restrict_negPart`

English:
lemma restrict_negPart
  given: {V : Set X} (D : locallyFinsuppWithin U Int) (h : V subseteq U)
  proof: by
  ext x
  simp only [locallyFinsuppWithin.restrict_apply, locallyFinsuppWithin.negPart_apply]
  aesop

中文:
引理 restrict_negPart
  条件: {V : Set X} (D : locallyFinsuppWithin U 整数) (h : V subseteq U)
  证明: by
  ext x
  simp only [locallyFinsuppWithin.restrict_apply, locallyFinsuppWithin.negPart_apply]
  aesop

Depends on / 依赖: locallyFinsuppWithin, locallyFinsuppWithin.negPart_apply, locallyFinsuppWithin.restrict_apply, negPart_apply, restrict_apply
-/
lemma restrict_negPart {V : Set X} (D : locallyFinsuppWithin U Int) (h : V subseteq U) :
    D⁻.restrict h = (D.restrict h)⁻ := by
  ext x
  simp only [locallyFinsuppWithin.restrict_apply, locallyFinsuppWithin.negPart_apply]
  aesop

/--
lemma `disjoint_nhdsWithin_cofinite_of_mem` / 引理 `disjoint_nhdsWithin_cofinite_of_mem`

English:
lemma disjoint_nhdsWithin_cofinite_of_mem
  statement: [Zero Y]
  proof: by
  rw [disjoint_cofinite_right]
  obtain ⟨t, h₁t, h₂t⟩ := f.supportLocallyFiniteWithinDomain p hp
  refine ⟨t inter f.support, ?_, h₂t⟩
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  grind

中文:
引理 disjoint_nhdsWithin_cofinite_of_mem
  结论: [Zero Y]
  证明: by
  rw [disjoint_cofinite_right]
  obtain ⟨t, h₁t, h₂t⟩ := f.supportLocallyFiniteWithinDomain p hp
  refine ⟨t inter f.support, ?_, h₂t⟩
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  grind

Depends on / 依赖: disjoint_cofinite_right, f.support, f.supportLocallyFiniteWithinDomain, mem_nhdsWithin_iff_exists_mem_nhds_inter, support, supportLocallyFiniteWithinDomain
-/
lemma disjoint_nhdsWithin_cofinite_of_mem [Zero Y]
    (f : locallyFinsuppWithin U Y) (p : X) (hp : p in U) :
    Disjoint (𝓝[f.support] p) cofinite := by
  rw [disjoint_cofinite_right]
  obtain ⟨t, h₁t, h₂t⟩ := f.supportLocallyFiniteWithinDomain p hp
  refine ⟨t inter f.support, ?_, h₂t⟩
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  grind

/--
lemma `_root_.Function.locallyFinsupp.disjoint_nhdsWithin_cofinite` / 引理 `_root_.Function.locallyFinsupp.disjoint_nhdsWithin_cofinite`

English:
lemma _root_.Function.locallyFinsupp.disjoint_nhdsWithin_cofinite
  proof: disjoint_nhdsWithin_cofinite_of_mem f p (mem_univ _)

中文:
引理 _root_.Function.locallyFinsupp.disjoint_nhdsWithin_cofinite
  证明: disjoint_nhdsWithin_cofinite_of_mem f p (mem_univ _)

Depends on / 依赖: disjoint_nhdsWithin_cofinite_of_mem, mem_univ
-/
lemma _root_.Function.locallyFinsupp.disjoint_nhdsWithin_cofinite
    [Zero Y] (f : locallyFinsupp X Y) (p : X) :
    Disjoint (𝓝[f.support] p) cofinite :=
  disjoint_nhdsWithin_cofinite_of_mem f p (mem_univ _)

end Function.locallyFinsuppWithin
