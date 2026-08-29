/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Frédéric Dupuis
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Convex cones

In an `R`-module `M`, we define a convex cone as a set `s` such that `a • x + b • y ∈ s` whenever
`x, y ∈ s` and `a, b > 0`. We prove that convex cones form a `CompleteLattice`, and define their
images (`ConvexCone.map`) and preimages (`ConvexCone.comap`) under linear maps.

We define pointed, blunt, flat and salient cones, and prove the correspondence between
convex cones and ordered modules.

We define `Convex.toCone` to be the minimal cone that includes a given convex set.

## Main statements

In `Mathlib/Analysis/Convex/Cone/Extension.lean` we prove
the M. Riesz extension theorem and a form of the Hahn-Banach theorem.

In `Mathlib/Analysis/Convex/Cone/Dual.lean` we prove
a variant of the hyperplane separation theorem.

## Implementation notes

While `Convex R` is a predicate on sets, `ConvexCone R M` is a bundled convex cone.

## References

* https://en.wikipedia.org/wiki/Convex_cone
* [Stephen P. Boyd and Lieven Vandenberghe, *Convex Optimization*][boydVandenberghe2004]
* [Emo Welzl and Bernd Gärtner, *Cone Programming*][welzl_garter]
-/

@[expose] public section

assert_not_exists TopologicalSpace Real Cardinal

open Set LinearMap Pointwise

variable {𝕜 R G M N O : Type*}

/-! ### Definition of `ConvexCone` and basic properties -/

section Definitions

variable [Semiring R] [PartialOrder R]

variable (R M) in
/-- A convex cone is a subset `s` of an `R`-module such that `a • x + b • y ∈ s` whenever `a, b > 0`
and `x, y ∈ s`. -/
@[wikidata Q2256541]
/--
Definition of `ConvexCone` / `ConvexCone` 的定义

English:
structure ConvexCone
  parameters: [AddCommMonoid M] [SMul R M]
  axioms and operations (3):
    - carrier : Set M
    - smul_mem' : forall ⦃c : R⦄, 0 < c -> forall ⦃x : M⦄, x in carrier -> c • x in carrier
    - add_mem' : forall ⦃x⦄ (_ : x in carrier) ⦃y⦄ (_ : y in carrier), x + y in carrier

中文:
结构 余nvexCone
  参数: [加法交换幺半群 M] [标量乘法 R M]
  公理与运算 (3 个):
    - carrier : 集合 M
    - smul_mem' : 对任意 ⦃c : R⦄, 0 < c -> 对任意 ⦃x : M⦄, x in carrier -> c • x in carrier
    - add_mem' : 对任意 ⦃x⦄ (_ : x in carrier) ⦃y⦄ (_ : y in carrier), x + y in carrier
-/
structure ConvexCone [AddCommMonoid M] [SMul R M] where
  /-- The **carrier set** underlying this cone: the set of points contained in it -/
  carrier : Set M
  smul_mem' : forall ⦃c : R⦄, 0 < c -> forall ⦃x : M⦄, x in carrier -> c • x in carrier
  add_mem' : forall ⦃x⦄ (_ : x in carrier) ⦃y⦄ (_ : y in carrier), x + y in carrier

end Definitions

namespace ConvexCone

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [AddCommMonoid M]

section SMul

variable [SMul R M] {C C₁ C₂ : ConvexCone R M} {s : Set M} {c : R} {x : M}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (ConvexCone R M) M
  body: carrier
  coe_injective C₁ C₂ h := by cases C₁; congr!

中文:
实例 :
  签名: 集合状 (余nvexCone R M) M
  定义体: carrier
  coe_injective C₁ C₂ h := by cases C₁; congr!

Depends on / 依赖: carrier
-/
instance : SetLike (ConvexCone R M) M where
  coe := carrier
  coe_injective C₁ C₂ h := by cases C₁; congr!

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (ConvexCone R M)
  body: .ofSetLike (ConvexCone R M) M

中文:
实例 :
  签名: 偏序 (余nvexCone R M)
  定义体: .ofSetLike (ConvexCone R M) M

Depends on / 依赖: ConvexCone, ofSetLike
-/
instance : PartialOrder (ConvexCone R M) := .ofSetLike (ConvexCone R M) M

/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (s : Set M) (h₁ h₂)
  statement: ↑(mk (R := R) s h₁ h₂) = s
  proof: rfl

中文:
引理 coe_mk
  条件: (s : 集合 M) (h₁ h₂)
  结论: ↑(mk (R := R) s h₁ h₂) = s
  证明: rfl
-/
@[simp, norm_cast] lemma coe_mk (s : Set M) (h₁ h₂) : ↑(mk (R := R) s h₁ h₂) = s := rfl

/--
lemma `mem_mk` / 引理 `mem_mk`

English:
lemma mem_mk
  given: {h₁ h₂}
  statement: x in mk (R := R) s h₁ h₂ ↔ x in s
  proof: .rfl

中文:
引理 mem_mk
  条件: {h₁ h₂}
  结论: x in mk (R := R) s h₁ h₂ ↔ x in s
  证明: .rfl
-/
@[simp] lemma mem_mk {h₁ h₂} : x in mk (R := R) s h₁ h₂ ↔ x in s := .rfl

/-- Two `ConvexCone`s are equal if they have the same elements. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (h : forall x, x in C₁ ↔ x in C₂)
  statement: C₁ = C₂
  proof: SetLike.ext h

中文:
定理 ext
  条件: (h : 对任意 x, x in C₁ ↔ x in C₂)
  结论: C₁ = C₂
  证明: SetLike.ext h

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext (h : forall x, x in C₁ ↔ x in C₂) : C₁ = C₂ := SetLike.ext h

variable (C) in
@[aesop 90% (rule_sets := [SetLike])]
/--
lemma `smul_mem` / 引理 `smul_mem`

English:
lemma smul_mem
  given: (hc : 0 < c) (hx : x in C)
  statement: c • x in C
  proof: C.smul_mem' hc hx

中文:
引理 smul_mem
  条件: (hc : 0 < c) (hx : x in C)
  结论: c • x in C
  证明: C.smul_mem' hc hx
-/
protected lemma smul_mem (hc : 0 < c) (hx : x in C) : c • x in C := C.smul_mem' hc hx

variable (C) in
/--
lemma `add_mem` / 引理 `add_mem`

English:
lemma add_mem
  given: ⦃x⦄ (hx : x in C) ⦃y⦄ (hy : y in C)
  statement: x + y in C
  proof: C.add_mem' hx hy

中文:
引理 add_mem
  条件: ⦃x⦄ (hx : x in C) ⦃y⦄ (hy : y in C)
  结论: x + y in C
  证明: C.add_mem' hx hy
-/
protected lemma add_mem ⦃x⦄ (hx : x in C) ⦃y⦄ (hy : y in C) : x + y in C := C.add_mem' hx hy

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddMemClass (ConvexCone R M) M
  body: add_mem' _ ha hb

中文:
实例 :
  签名: 加法Mem类 (余nvexCone R M) M
  定义体: add_mem' _ ha hb

Depends on / 依赖: add_mem
-/
instance : AddMemClass (ConvexCone R M) M where add_mem ha hb := add_mem' _ ha hb

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (C : ConvexCone R M) (s : Set M) (hs : s = C)
  body: s
  add_mem' := hs.symm ▸ C.add_mem'
  smul_mem' := by simpa [hs] using! C.smul_mem'

中文:
定义 copy
  签名: (C : 余nvexCone R M) (s : 集合 M) (hs : s = C)
  定义体: s
  add_mem' := hs.symm ▸ C.add_mem'
  smul_mem' := by simpa [hs] using! C.smul_mem'
-/
@[simps] protected def copy (C : ConvexCone R M) (s : Set M) (hs : s = C) : ConvexCone R M where
  carrier := s
  add_mem' := hs.symm ▸ C.add_mem'
  smul_mem' := by simpa [hs] using! C.smul_mem'

/--
lemma `copy_eq` / 引理 `copy_eq`

English:
lemma copy_eq
  given: (C : ConvexCone R M) (s : Set M) (hs)
  statement: C.copy s hs = C
  proof: SetLike.coe_injective hs

中文:
引理 copy_eq
  条件: (C : 余nvexCone R M) (s : 集合 M) (hs)
  结论: C.copy s hs = C
  证明: SetLike.coe_injective hs

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
lemma copy_eq (C : ConvexCone R M) (s : Set M) (hs) : C.copy s hs = C := SetLike.coe_injective hs

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (ConvexCone R M)
  body: ⟨⋂ C in S, C, fun _r hr _x hx => mem_biInter fun C hC => C.smul_mem hr mem_iInter₂.1 hx C hC,
      fun _ hx _ hy =>
      mem_biInter fun C hC => add_mem (mem_iInter₂.1 hx C hC) (mem_iInter₂.1 hy C hC)⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 下确界集 (余nvexCone R M)
  定义体: ⟨⋂ C in S, C, fun _r hr _x hx => mem_biInter fun C hC => C.smul_mem hr mem_iInter₂.1 hx C hC,
      fun _ hx _ hy =>
      mem_biInter fun C hC => add_mem (mem_iInter₂.1 hx C hC) (mem_iInter₂.1 hy C hC)⟩

@[simp, norm_cast]

Depends on / 依赖: C.smul_mem, add_mem, mem_biInter, smul_mem
-/
instance : InfSet (ConvexCone R M) where
  sInf S :=
⟨⋂ C in S, C, fun _r hr _x hx => mem_biInter fun C hC => C.smul_mem hr mem_iInter₂.1 hx C hC,
      fun _ hx _ hy =>
      mem_biInter fun C hC => add_mem (mem_iInter₂.1 hx C hC) (mem_iInter₂.1 hy C hC)⟩

@[simp, norm_cast]
/--
lemma `coe_sInf` / 引理 `coe_sInf`

English:
lemma coe_sInf
  given: (S : Set (ConvexCone R M))
  statement: ↑(sInf S) = ⋂ C in S, (C : Set M)
  proof: rfl

中文:
引理 coe_sInf
  条件: (S : 集合 (余nvexCone R M))
  结论: ↑(sInf S) = ⋂ C in S, (C : 集合 M)
  证明: rfl
-/
lemma coe_sInf (S : Set (ConvexCone R M)) : ↑(sInf S) = ⋂ C in S, (C : Set M) := rfl

/--
lemma `mem_sInf` / 引理 `mem_sInf`

English:
lemma mem_sInf
  given: {S : Set (ConvexCone R M)}
  statement: x in sInf S ↔ forall C in S, x in C
  proof: mem_iInter₂

@[simp, norm_cast]

中文:
引理 mem_sInf
  条件: {S : 集合 (余nvexCone R M)}
  结论: x in sInf S ↔ 对任意 C in S, x in C
  证明: mem_iInter₂

@[simp, norm_cast]
-/
@[simp] lemma mem_sInf {S : Set (ConvexCone R M)} : x in sInf S ↔ forall C in S, x in C := mem_iInter₂

@[simp, norm_cast]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι : Sort*} (f : ι -> ConvexCone R M)
  statement: ↑(iInf f) = ⋂ i, (f i : Set M)
  proof: by
  simp [iInf]

@[simp]

中文:
定理 coe_iInf
  条件: {ι : 类型层*} (f : ι -> 余nvexCone R M)
  结论: ↑(iInf f) = ⋂ i, (f i : 集合 M)
  证明: by
  simp [iInf]

@[simp]
-/
theorem coe_iInf {ι : Sort*} (f : ι -> ConvexCone R M) : ↑(iInf f) = ⋂ i, (f i : Set M) := by
  simp [iInf]

@[simp]
/--
lemma `mem_iInf` / 引理 `mem_iInf`

English:
lemma mem_iInf
  given: {ι : Sort*} {f : ι -> ConvexCone R M}
  statement: x in iInf f ↔ forall i, x in f i
  proof: mem_iInter₂.trans by simp

中文:
引理 mem_iInf
  条件: {ι : 类型层*} {f : ι -> 余nvexCone R M}
  结论: x in iInf f ↔ 对任意 i, x in f i
  证明: mem_iInter₂.trans by simp
-/
lemma mem_iInf {ι : Sort*} {f : ι -> ConvexCone R M} : x in iInf f ↔ forall i, x in f i :=
mem_iInter₂.trans by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSemilatticeInf (ConvexCone R M)
  body: .of_image SetLike.coe_subset_coe isGLB_biInf

中文:
实例 :
  签名: 余mpleteSemilatticeInf (余nvexCone R M)
  定义体: .of_image SetLike.coe_subset_coe isGLB_biInf

Depends on / 依赖: SetLike, SetLike.coe_subset_coe, coe_subset_coe, isGLB_biInf, of_image
-/
instance : CompleteSemilatticeInf (ConvexCone R M) where
  isGLB_sInf _ := .of_image SetLike.coe_subset_coe isGLB_biInf

variable (R s) in
/--
Definition of `hull` / `hull` 的定义

English:
definition hull
  signature: : ConvexCone R M
  body: sInf {C : ConvexCone R M | s subseteq C}

中文:
定义 hull
  签名: : 余nvexCone R M
  定义体: sInf {C : ConvexCone R M | s subseteq C}

Depends on / 依赖: ConvexCone, subseteq
-/
def hull : ConvexCone R M := sInf {C : ConvexCone R M | s subseteq C}

/--
lemma `subset_hull` / 引理 `subset_hull`

English:
lemma subset_hull
  statement: s subseteq hull R s
  proof: by simp [hull]

中文:
引理 subset_hull
  结论: s subseteq hull R s
  证明: by simp [hull]
-/
lemma subset_hull : s subseteq hull R s := by simp [hull]

/--
lemma `hull_min` / 引理 `hull_min`

English:
lemma hull_min
  given: (hsC : s subseteq C)
  statement: hull R s <= C
  proof: sInf_le hsC

中文:
引理 hull_min
  条件: (hsC : s subseteq C)
  结论: hull R s <= C
  证明: sInf_le hsC

Depends on / 依赖: sInf_le
-/
lemma hull_min (hsC : s subseteq C) : hull R s <= C := sInf_le hsC

/--
lemma `hull_le_iff` / 引理 `hull_le_iff`

English:
lemma hull_le_iff
  statement: hull R s <= C ↔ s subseteq C
  proof: ⟨subset_hull.trans, hull_min⟩

中文:
引理 hull_le_iff
  结论: hull R s <= C ↔ s subseteq C
  证明: ⟨subset_hull.trans, hull_min⟩

Depends on / 依赖: hull_min, subset_hull, subset_hull.trans
-/
lemma hull_le_iff : hull R s <= C ↔ s subseteq C := ⟨subset_hull.trans, hull_min⟩

/--
lemma `gc_hull_coe` / 引理 `gc_hull_coe`

English:
lemma gc_hull_coe
  statement: GaloisConnection (hull R : Set M -> ConvexCone R M) (↑)
  proof: fun _C _s => hull_le_iff

中文:
引理 gc_hull_coe
  结论: GaloisConnection (hull R : 集合 M -> 余nvexCone R M) (↑)
  证明: fun _C _s => hull_le_iff

Depends on / 依赖: hull_le_iff
-/
lemma gc_hull_coe : GaloisConnection (hull R : Set M -> ConvexCone R M) (↑) :=
  fun _C _s => hull_le_iff

/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion (hull R : Set M -> ConvexCone R M) (↑) where
  body: gc_hull_coe
  le_l_u _ := subset_hull
choice s hs := (hull R s).copy s subset_hull.antisymm hs
  choice_eq _ _ := copy_eq _ _ _

中文:
定义 gi
  签名: : Galois嵌入 (hull R : 集合 M -> 余nvexCone R M) (↑) where
  定义体: gc_hull_coe
  le_l_u _ := subset_hull
choice s hs := (hull R s).copy s subset_hull.antisymm hs
  choice_eq _ _ := copy_eq _ _ _
-/
protected def gi : GaloisInsertion (hull R : Set M -> ConvexCone R M) (↑) where
  gc := gc_hull_coe
  le_l_u _ := subset_hull
choice s hs := (hull R s).copy s subset_hull.antisymm hs
  choice_eq _ _ := copy_eq _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (ConvexCone R M)
  body: ⟨⟨∅, fun _ _ _ => False.elim, fun _ => False.elim⟩⟩

中文:
实例 :
  签名: 底元素 (余nvexCone R M)
  定义体: ⟨⟨∅, fun _ _ _ => False.elim, fun _ => False.elim⟩⟩

Depends on / 依赖: False.elim
-/
instance : Bot (ConvexCone R M) :=
  ⟨⟨∅, fun _ _ _ => False.elim, fun _ => False.elim⟩⟩

/--
lemma `notMem_bot` / 引理 `notMem_bot`

English:
lemma notMem_bot
  statement: x ∉ (⊥ : ConvexCone R M)
  proof: id

中文:
引理 notMem_bot
  结论: x ∉ (⊥ : 余nvexCone R M)
  证明: id
-/
@[simp] lemma notMem_bot : x ∉ (⊥ : ConvexCone R M) := id

/--
lemma `coe_bot` / 引理 `coe_bot`

English:
lemma coe_bot
  statement: ↑(⊥ : ConvexCone R M) = (∅ : Set M)
  proof: rfl

@[simp, norm_cast]

中文:
引理 coe_bot
  结论: ↑(⊥ : 余nvexCone R M) = (∅ : 集合 M)
  证明: rfl

@[simp, norm_cast]
-/
@[simp, norm_cast] lemma coe_bot : ↑(⊥ : ConvexCone R M) = (∅ : Set M) := rfl

@[simp, norm_cast]
/--
lemma `coe_eq_empty` / 引理 `coe_eq_empty`

English:
lemma coe_eq_empty
  statement: (C : Set M) = ∅ ↔ C = ⊥
  proof: by rw [← coe_bot (R := R)]; norm_cast

中文:
引理 coe_eq_empty
  结论: (C : 集合 M) = ∅ ↔ C = ⊥
  证明: by rw [← coe_bot (R := R)]; norm_cast

Depends on / 依赖: coe_bot
-/
lemma coe_eq_empty : (C : Set M) = ∅ ↔ C = ⊥ := by rw [← coe_bot (R := R)]; norm_cast

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (ConvexCone R M)
  body: ⊥
  bot_le _ := empty_subset _
  __ := instCompleteSemilatticeInf
  __ := ConvexCone.gi.liftCompleteLattice

中文:
实例 :
  签名: 完备格 (余nvexCone R M)
  定义体: ⊥
  bot_le _ := empty_subset _
  __ := instCompleteSemilatticeInf
  __ := ConvexCone.gi.liftCompleteLattice
-/
instance : CompleteLattice (ConvexCone R M) where
  bot := ⊥
  bot_le _ := empty_subset _
  __ := instCompleteSemilatticeInf
  __ := ConvexCone.gi.liftCompleteLattice

variable (C₁ C₂) in
/--
lemma `coe_inf` / 引理 `coe_inf`

English:
lemma coe_inf
  statement: (C₁ ⊓ C₂) = (C₁ inter C₂ : Set M)
  proof: rfl

中文:
引理 coe_inf
  结论: (C₁ ⊓ C₂) = (C₁ inter C₂ : 集合 M)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_inf : (C₁ ⊓ C₂) = (C₁ inter C₂ : Set M) := rfl

/--
lemma `mem_inf` / 引理 `mem_inf`

English:
lemma mem_inf
  statement: x in C₁ ⊓ C₂ ↔ x in C₁ ∧ x in C₂
  proof: .rfl

中文:
引理 mem_inf
  结论: x in C₁ ⊓ C₂ ↔ x in C₁ ∧ x in C₂
  证明: .rfl
-/
@[simp] lemma mem_inf : x in C₁ ⊓ C₂ ↔ x in C₁ ∧ x in C₂ := .rfl

/--
lemma `mem_top` / 引理 `mem_top`

English:
lemma mem_top
  statement: x in (⊤ : ConvexCone R M)
  proof: mem_univ x

中文:
引理 mem_top
  结论: x in (⊤ : 余nvexCone R M)
  证明: mem_univ x
-/
@[simp] lemma mem_top : x in (⊤ : ConvexCone R M) := mem_univ x

/--
lemma `coe_top` / 引理 `coe_top`

English:
lemma coe_top
  statement: ↑(⊤ : ConvexCone R M) = (univ : Set M)
  proof: rfl

中文:
引理 coe_top
  结论: ↑(⊤ : 余nvexCone R M) = (univ : 集合 M)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_top : ↑(⊤ : ConvexCone R M) = (univ : Set M) := rfl

/--
lemma `disjoint_coe` / 引理 `disjoint_coe`

English:
lemma disjoint_coe
  statement: Disjoint (C₁ : Set M) C₂ ↔ Disjoint C₁ C₂
  proof: by
  simp [disjoint_iff, ← coe_inf]

中文:
引理 disjoint_coe
  结论: Disjoint (C₁ : 集合 M) C₂ ↔ Disjoint C₁ C₂
  证明: by
  simp [disjoint_iff, ← coe_inf]
-/
@[simp, norm_cast] lemma disjoint_coe : Disjoint (C₁ : Set M) C₂ ↔ Disjoint C₁ C₂ := by
  simp [disjoint_iff, ← coe_inf]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (ConvexCone R M)
  body: ⟨⊥⟩

中文:
实例 :
  签名: 可居 (余nvexCone R M)
  定义体: ⟨⊥⟩
-/
instance : Inhabited (ConvexCone R M) := ⟨⊥⟩

end SMul

section Module

variable [Module R M] (C : ConvexCone R M)

/--
theorem `convex` / 定理 `convex`

English:
theorem convex
  statement: Convex R (C : Set M)
  proof: convex_iff_forall_pos.2 fun _ hx _ hy _ _ ha hb _ => add_mem (C.smul_mem ha hx) (C.smul_mem hb hy)

中文:
定理 convex
  结论: 凸 R (C : 集合 M)
  证明: convex_iff_forall_pos.2 fun _ hx _ hy _ _ ha hb _ => add_mem (C.smul_mem ha hx) (C.smul_mem hb hy)
-/
protected theorem convex : Convex R (C : Set M) :=
  convex_iff_forall_pos.2 fun _ hx _ hy _ _ ha hb _ => add_mem (C.smul_mem ha hx) (C.smul_mem hb hy)

end Module

section Maps

variable [AddCommMonoid N] [AddCommMonoid O]
variable [Module R M] [Module R N] [Module R O]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : M ->ₗ[R] N) (C : ConvexCone R M)
  body: f '' C
  smul_mem' := fun c hc _ ⟨x, hx, hy⟩ => hy ▸ f.map_smul c x ▸ mem_image_of_mem f (C.smul_mem hc hx)
  add_mem' := fun _ ⟨x₁, hx₁, hy₁⟩ _ ⟨x₂, hx₂, hy₂⟩ =>
    hy₁ ▸ hy₂ ▸ f.map_add x₁ x₂ ▸ mem_image_of_mem f (add_mem hx₁ hx₂)

@[simp, norm_cast]

中文:
定义 map
  签名: (f : M ->ₗ[R] N) (C : 余nvexCone R M)
  定义体: f '' C
  smul_mem' := fun c hc _ ⟨x, hx, hy⟩ => hy ▸ f.map_smul c x ▸ mem_image_of_mem f (C.smul_mem hc hx)
  add_mem' := fun _ ⟨x₁, hx₁, hy₁⟩ _ ⟨x₂, hx₂, hy₂⟩ =>
    hy₁ ▸ hy₂ ▸ f.map_add x₁ x₂ ▸ mem_image_of_mem f (add_mem hx₁ hx₂)

@[simp, norm_cast]
-/
def map (f : M ->ₗ[R] N) (C : ConvexCone R M) : ConvexCone R N where
  carrier := f '' C
  smul_mem' := fun c hc _ ⟨x, hx, hy⟩ => hy ▸ f.map_smul c x ▸ mem_image_of_mem f (C.smul_mem hc hx)
  add_mem' := fun _ ⟨x₁, hx₁, hy₁⟩ _ ⟨x₂, hx₂, hy₂⟩ =>
    hy₁ ▸ hy₂ ▸ f.map_add x₁ x₂ ▸ mem_image_of_mem f (add_mem hx₁ hx₂)

@[simp, norm_cast]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  given: (C : ConvexCone R M) (f : M ->ₗ[R] N)
  statement: (C.map f : Set N) = f '' C
  proof: rfl

@[simp]

中文:
定理 coe_map
  条件: (C : 余nvexCone R M) (f : M ->ₗ[R] N)
  结论: (C.map f : 集合 N) = f '' C
  证明: rfl

@[simp]
-/
theorem coe_map (C : ConvexCone R M) (f : M ->ₗ[R] N) : (C.map f : Set N) = f '' C :=
  rfl

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {f : M ->ₗ[R] N} {C : ConvexCone R M} {y : N}
  statement: y in C.map f ↔ exists x in C, f x = y
  proof: Set.mem_image f C y

中文:
定理 mem_map
  条件: {f : M ->ₗ[R] N} {C : 余nvexCone R M} {y : N}
  结论: y in C.map f ↔ 存在 x in C, f x = y
  证明: Set.mem_image f C y

Depends on / 依赖: Set.mem_image, mem_image
-/
theorem mem_map {f : M ->ₗ[R] N} {C : ConvexCone R M} {y : N} : y in C.map f ↔ exists x in C, f x = y :=
  Set.mem_image f C y

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (g : N ->ₗ[R] O) (f : M ->ₗ[R] N) (C : ConvexCone R M)
  proof: SetLike.coe_injective image_image g f C

@[simp]

中文:
定理 map_map
  条件: (g : N ->ₗ[R] O) (f : M ->ₗ[R] N) (C : 余nvexCone R M)
  证明: SetLike.coe_injective image_image g f C

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, image_image
-/
theorem map_map (g : N ->ₗ[R] O) (f : M ->ₗ[R] N) (C : ConvexCone R M) :
    (C.map f).map g = C.map (g.comp f) :=
SetLike.coe_injective image_image g f C

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (C : ConvexCone R M)
  statement: C.map LinearMap.id = C
  proof: SetLike.coe_injective image_id _

中文:
定理 map_id
  条件: (C : 余nvexCone R M)
  结论: C.map 线性映射.id = C
  证明: SetLike.coe_injective image_id _

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, image_id
-/
theorem map_id (C : ConvexCone R M) : C.map LinearMap.id = C :=
SetLike.coe_injective image_id _

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : M ->ₗ[R] N) (C : ConvexCone R N)
  body: f ⁻¹' C
  smul_mem' c hc x hx := by
    rw [mem_preimage]; rw [f.map_smul c]
    exact C.smul_mem hc hx
  add_mem' x hx y hy := by
    rw [mem_preimage]; rw [f.map_add]
    exact add_mem hx hy

@[simp]

中文:
定义 comap
  签名: (f : M ->ₗ[R] N) (C : 余nvexCone R N)
  定义体: f ⁻¹' C
  smul_mem' c hc x hx := by
    rw [mem_preimage]; rw [f.map_smul c]
    exact C.smul_mem hc hx
  add_mem' x hx y hy := by
    rw [mem_preimage]; rw [f.map_add]
    exact add_mem hx hy

@[simp]
-/
def comap (f : M ->ₗ[R] N) (C : ConvexCone R N) : ConvexCone R M where
  carrier := f ⁻¹' C
  smul_mem' c hc x hx := by
    rw [mem_preimage]; rw [f.map_smul c]
    exact C.smul_mem hc hx
  add_mem' x hx y hy := by
    rw [mem_preimage]; rw [f.map_add]
    exact add_mem hx hy

@[simp]
/--
theorem `coe_comap` / 定理 `coe_comap`

English:
theorem coe_comap
  given: (f : M ->ₗ[R] N) (C : ConvexCone R N)
  statement: (C.comap f : Set M) = f ⁻¹' C
  proof: rfl

@[simp]

中文:
定理 coe_comap
  条件: (f : M ->ₗ[R] N) (C : 余nvexCone R N)
  结论: (C.comap f : 集合 M) = f ⁻¹' C
  证明: rfl

@[simp]
-/
theorem coe_comap (f : M ->ₗ[R] N) (C : ConvexCone R N) : (C.comap f : Set M) = f ⁻¹' C :=
  rfl

@[simp]
/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  given: (C : ConvexCone R M)
  statement: C.comap LinearMap.id = C
  proof: rfl

中文:
定理 comap_id
  条件: (C : 余nvexCone R M)
  结论: C.comap 线性映射.id = C
  证明: rfl
-/
theorem comap_id (C : ConvexCone R M) : C.comap LinearMap.id = C :=
  rfl

/--
theorem `comap_comap` / 定理 `comap_comap`

English:
theorem comap_comap
  given: (g : N ->ₗ[R] O) (f : M ->ₗ[R] N) (C : ConvexCone R O)
  proof: rfl

@[simp]

中文:
定理 comap_comap
  条件: (g : N ->ₗ[R] O) (f : M ->ₗ[R] N) (C : 余nvexCone R O)
  证明: rfl

@[simp]
-/
theorem comap_comap (g : N ->ₗ[R] O) (f : M ->ₗ[R] N) (C : ConvexCone R O) :
    (C.comap g).comap f = C.comap (g.comp f) :=
  rfl

@[simp]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: {f : M ->ₗ[R] N} {C : ConvexCone R N} {x : M}
  statement: x in C.comap f ↔ f x in C
  proof: Iff.rfl

中文:
定理 mem_comap
  条件: {f : M ->ₗ[R] N} {C : 余nvexCone R N} {x : M}
  结论: x in C.comap f ↔ f x in C
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_comap {f : M ->ₗ[R] N} {C : ConvexCone R N} {x : M} : x in C.comap f ↔ f x in C :=
  Iff.rfl

end Maps

end OrderedSemiring

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

section MulAction

variable [AddCommMonoid M]
variable [MulAction 𝕜 M] (C : ConvexCone 𝕜 M)

/--
theorem `smul_mem_iff` / 定理 `smul_mem_iff`

English:
theorem smul_mem_iff
  given: {c : 𝕜} (hc : 0 < c) {x : M}
  statement: c • x in C ↔ x in C
  proof: ⟨fun h => inv_smul_smul₀ hc.ne' x ▸ C.smul_mem (inv_pos.2 hc) h, C.smul_mem hc⟩

中文:
定理 smul_mem_iff
  条件: {c : 𝕜} (hc : 0 < c) {x : M}
  结论: c • x in C ↔ x in C
  证明: ⟨fun h => inv_smul_smul₀ hc.ne' x ▸ C.smul_mem (inv_pos.2 hc) h, C.smul_mem hc⟩

Depends on / 依赖: C.smul_mem, hc.ne, inv_pos, smul_mem
-/
theorem smul_mem_iff {c : 𝕜} (hc : 0 < c) {x : M} : c • x in C ↔ x in C :=
  ⟨fun h => inv_smul_smul₀ hc.ne' x ▸ C.smul_mem (inv_pos.2 hc) h, C.smul_mem hc⟩

end MulAction
end LinearOrderedField

/-! ### Convex cones with extra properties -/


section OrderedSemiring

variable [Semiring R] [PartialOrder R]

section AddCommMonoid

variable [AddCommMonoid M] [SMul R M] {C C₁ C₂ : ConvexCone R M}

/--
Definition of `Pointed` / `Pointed` 的定义

English:
definition Pointed
  signature: (C : ConvexCone R M)
  body: (0 : M) in C

中文:
定义 Pointed
  签名: (C : 余nvexCone R M)
  定义体: (0 : M) in C
-/
def Pointed (C : ConvexCone R M) : Prop := (0 : M) in C

/--
Definition of `Blunt` / `Blunt` 的定义

English:
definition Blunt
  signature: (C : ConvexCone R M)
  body: (0 : M) ∉ C

中文:
定义 Blunt
  签名: (C : 余nvexCone R M)
  定义体: (0 : M) ∉ C
-/
def Blunt (C : ConvexCone R M) : Prop := (0 : M) ∉ C

/--
lemma `blunt_iff_not_pointed` / 引理 `blunt_iff_not_pointed`

English:
lemma blunt_iff_not_pointed
  statement: C.Blunt ↔ ¬ C.Pointed
  proof: .rfl

中文:
引理 blunt_iff_not_pointed
  结论: C.Blunt ↔ ¬ C.Pointed
  证明: .rfl
-/
lemma blunt_iff_not_pointed : C.Blunt ↔ ¬ C.Pointed := .rfl
/--
lemma `pointed_iff_not_blunt` / 引理 `pointed_iff_not_blunt`

English:
lemma pointed_iff_not_blunt
  statement: C.Pointed ↔ ¬ C.Blunt
  proof: by simp [Blunt, Pointed]

中文:
引理 pointed_iff_not_blunt
  结论: C.Pointed ↔ ¬ C.Blunt
  证明: by simp [Blunt, Pointed]

Depends on / 依赖: Pointed
-/
lemma pointed_iff_not_blunt : C.Pointed ↔ ¬ C.Blunt := by simp [Blunt, Pointed]

/--
theorem `Pointed.mono` / 定理 `Pointed.mono`

English:
theorem Pointed.mono
  given: (h : C₁ <= C₂)
  statement: C₁.Pointed -> C₂.Pointed
  proof: @h _

中文:
定理 Pointed.mono
  条件: (h : C₁ <= C₂)
  结论: C₁.Pointed -> C₂.Pointed
  证明: @h _
-/
theorem Pointed.mono (h : C₁ <= C₂) : C₁.Pointed -> C₂.Pointed := @h _
/--
theorem `Blunt.anti` / 定理 `Blunt.anti`

English:
theorem Blunt.anti
  given: (h : C₂ <= C₁)
  statement: C₁.Blunt -> C₂.Blunt
  proof: (· ∘ @h 0)

中文:
定理 Blunt.anti
  条件: (h : C₂ <= C₁)
  结论: C₁.Blunt -> C₂.Blunt
  证明: (· ∘ @h 0)
-/
theorem Blunt.anti (h : C₂ <= C₁) : C₁.Blunt -> C₂.Blunt := (· ∘ @h 0)

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup G] [SMul R G] {C C₁ C₂ : ConvexCone R G}

/--
Definition of `Flat` / `Flat` 的定义

English:
definition Flat
  signature: (C : ConvexCone R G)
  body: exists x in C, x != (0 : G) ∧ -x in C

中文:
定义 平坦
  签名: (C : 余nvexCone R G)
  定义体: exists x in C, x != (0 : G) ∧ -x in C
-/
def Flat (C : ConvexCone R G) : Prop := exists x in C, x != (0 : G) ∧ -x in C

/--
Definition of `Salient` / `Salient` 的定义

English:
definition Salient
  signature: (C : ConvexCone R G)
  body: forall x in C, x != (0 : G) -> -x ∉ C

中文:
定义 Salient
  签名: (C : 余nvexCone R G)
  定义体: forall x in C, x != (0 : G) -> -x ∉ C
-/
def Salient (C : ConvexCone R G) : Prop := forall x in C, x != (0 : G) -> -x ∉ C

/--
theorem `salient_iff_not_flat` / 定理 `salient_iff_not_flat`

English:
theorem salient_iff_not_flat
  statement: C.Salient ↔ ¬ C.Flat
  proof: by simp [Salient, Flat]

中文:
定理 salient_iff_not_flat
  结论: C.Salient ↔ ¬ C.平坦
  证明: by simp [Salient, Flat]

Depends on / 依赖: Salient
-/
theorem salient_iff_not_flat : C.Salient ↔ ¬ C.Flat := by simp [Salient, Flat]

/--
theorem `Flat.mono` / 定理 `Flat.mono`

English:
theorem Flat.mono
  given: (h : C₁ <= C₂)
  statement: C₁.Flat -> C₂.Flat

中文:
定理 平坦.mono
  条件: (h : C₁ <= C₂)
  结论: C₁.平坦 -> C₂.平坦
-/
theorem Flat.mono (h : C₁ <= C₂) : C₁.Flat -> C₂.Flat
  | ⟨x, hxS, hx, hnxS⟩ => ⟨x, h hxS, hx, h hnxS⟩

/--
theorem `Salient.anti` / 定理 `Salient.anti`

English:
theorem Salient.anti
  given: (h : C₂ <= C₁)
  statement: C₁.Salient -> C₂.Salient
  proof: fun hS x hxT hx hnT => hS x (h hxT) hx (h hnT)

中文:
定理 Salient.anti
  条件: (h : C₂ <= C₁)
  结论: C₁.Salient -> C₂.Salient
  证明: fun hS x hxT hx hnT => hS x (h hxT) hx (h hnT)
-/
theorem Salient.anti (h : C₂ <= C₁) : C₁.Salient -> C₂.Salient :=
  fun hS x hxT hx hnT => hS x (h hxT) hx (h hnT)

/--
theorem `Flat.pointed` / 定理 `Flat.pointed`

English:
theorem Flat.pointed
  given: (hC : C.Flat)
  statement: C.Pointed
  proof: by
  obtain ⟨x, hx, _, hxneg⟩ := hC
  rw [Pointed]; rw [← add_neg_cancel x]
  exact add_mem hx hxneg

中文:
定理 平坦.pointed
  条件: (hC : C.平坦)
  结论: C.Pointed
  证明: by
  obtain ⟨x, hx, _, hxneg⟩ := hC
  rw [Pointed]; rw [← add_neg_cancel x]
  exact add_mem hx hxneg

Depends on / 依赖: Pointed, add_mem, add_neg_cancel
-/
theorem Flat.pointed (hC : C.Flat) : C.Pointed := by
  obtain ⟨x, hx, _, hxneg⟩ := hC
  rw [Pointed]; rw [← add_neg_cancel x]
  exact add_mem hx hxneg

/--
theorem `Blunt.salient` / 定理 `Blunt.salient`

English:
theorem Blunt.salient
  statement: C.Blunt -> C.Salient
  proof: by
  rw [salient_iff_not_flat]; rw [blunt_iff_not_pointed]
  exact mt Flat.pointed

中文:
定理 Blunt.salient
  结论: C.Blunt -> C.Salient
  证明: by
  rw [salient_iff_not_flat]; rw [blunt_iff_not_pointed]
  exact mt Flat.pointed

Depends on / 依赖: Flat.pointed, blunt_iff_not_pointed, pointed, salient_iff_not_flat
-/
theorem Blunt.salient : C.Blunt -> C.Salient := by
  rw [salient_iff_not_flat]; rw [blunt_iff_not_pointed]
  exact mt Flat.pointed

/-- A pointed convex cone defines a preorder. -/
@[instance_reducible]
/--
Definition of `toPreorder` / `toPreorder` 的定义

English:
definition toPreorder
  signature: (C : ConvexCone R G) (h₁ : C.Pointed)
  body: y - x in C
  le_refl x := by rw [sub_self x]; exact h₁
  le_trans x y z xy zy := by simpa using add_mem zy xy

中文:
定义 toPreorder
  签名: (C : 余nvexCone R G) (h₁ : C.Pointed)
  定义体: y - x in C
  le_refl x := by rw [sub_self x]; exact h₁
  le_trans x y z xy zy := by simpa using add_mem zy xy
-/
def toPreorder (C : ConvexCone R G) (h₁ : C.Pointed) : Preorder G where
  le x y := y - x in C
  le_refl x := by rw [sub_self x]; exact h₁
  le_trans x y z xy zy := by simpa using add_mem zy xy

/-- A pointed and salient cone defines a partial order. -/
@[instance_reducible]
/--
Definition of `toPartialOrder` / `toPartialOrder` 的定义

English:
definition toPartialOrder
  signature: (C : ConvexCone R G) (h₁ : C.Pointed) (h₂ : C.Salient)
  body: { toPreorder C h₁ with
    le_antisymm := by
      intro a b ab ba
      by_contra h
      have h' : b - a != 0 := fun h'' => h (eq_of_sub_eq_zero h'').symm
      have H := h₂ (b - a) ab h'
      rw [neg_sub b a] at H
      exact H ba }

中文:
定义 toPartialOrder
  签名: (C : 余nvexCone R G) (h₁ : C.Pointed) (h₂ : C.Salient)
  定义体: { toPreorder C h₁ with
    le_antisymm := by
      intro a b ab ba
      by_contra h
      have h' : b - a != 0 := fun h'' => h (eq_of_sub_eq_zero h'').symm
      have H := h₂ (b - a) ab h'
      rw [neg_sub b a] at H
      exact H ba }

Depends on / 依赖: eq_of_sub_eq_zero, le_antisymm, neg_sub, toPreorder
-/
def toPartialOrder (C : ConvexCone R G) (h₁ : C.Pointed) (h₂ : C.Salient) : PartialOrder G :=
  { toPreorder C h₁ with
    le_antisymm := by
      intro a b ab ba
      by_contra h
      have h' : b - a != 0 := fun h'' => h (eq_of_sub_eq_zero h'').symm
      have H := h₂ (b - a) ab h'
      rw [neg_sub b a] at H
      exact H ba }

/--
lemma `to_isOrderedAddMonoid` / 引理 `to_isOrderedAddMonoid`

English:
lemma to_isOrderedAddMonoid
  given: (C : ConvexCone R G) (h₁ : C.Pointed) (h₂ : C.Salient)
  proof: toPartialOrder C h₁ h₂
    IsOrderedAddMonoid G where
  __ := toPartialOrder C h₁ h₂
  add_le_add_left a b hab c := show b + c - (a + c) in C by rwa [add_sub_add_right_eq_sub]

中文:
引理 to_isOrderedAddMonoid
  条件: (C : 余nvexCone R G) (h₁ : C.Pointed) (h₂ : C.Salient)
  证明: toPartialOrder C h₁ h₂
    IsOrderedAddMonoid G where
  __ := toPartialOrder C h₁ h₂
  add_le_add_left a b hab c := show b + c - (a + c) in C by rwa [add_sub_add_right_eq_sub]

Depends on / 依赖: toPartialOrder
-/
lemma to_isOrderedAddMonoid (C : ConvexCone R G) (h₁ : C.Pointed) (h₂ : C.Salient) :
    let _ := toPartialOrder C h₁ h₂
    IsOrderedAddMonoid G where
  __ := toPartialOrder C h₁ h₂
  add_le_add_left a b hab c := show b + c - (a + c) in C by rwa [add_sub_add_right_eq_sub]

end AddCommGroup

section Module

section Monoid

variable [AddCommMonoid M] [Module R M] {C₁ C₂ : ConvexCone R M} {x : M}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (ConvexCone R M)
  body: ⟨⟨0, fun _ _ => by simp, fun _ => by simp⟩⟩

中文:
实例 :
  签名: 零 (余nvexCone R M)
  定义体: ⟨⟨0, fun _ _ => by simp, fun _ => by simp⟩⟩
-/
instance : Zero (ConvexCone R M) :=
  ⟨⟨0, fun _ _ => by simp, fun _ => by simp⟩⟩

/--
lemma `mem_zero` / 引理 `mem_zero`

English:
lemma mem_zero
  statement: x in (0 : ConvexCone R M) ↔ x = 0
  proof: .rfl

中文:
引理 mem_zero
  结论: x in (0 : 余nvexCone R M) ↔ x = 0
  证明: .rfl
-/
@[simp] lemma mem_zero : x in (0 : ConvexCone R M) ↔ x = 0 := .rfl

/--
lemma `coe_zero` / 引理 `coe_zero`

English:
lemma coe_zero
  statement: ((0 : ConvexCone R M) : Set M) = 0
  proof: rfl

中文:
引理 coe_zero
  结论: ((0 : 余nvexCone R M) : 集合 M) = 0
  证明: rfl
-/
@[simp, norm_cast] lemma coe_zero : ((0 : ConvexCone R M) : Set M) = 0 := rfl

/--
theorem `pointed_zero` / 定理 `pointed_zero`

English:
theorem pointed_zero
  statement: (0 : ConvexCone R M).Pointed
  proof: by rw [Pointed, mem_zero]

中文:
定理 pointed_zero
  结论: (0 : 余nvexCone R M).Pointed
  证明: by rw [Pointed, mem_zero]

Depends on / 依赖: Pointed, mem_zero
-/
theorem pointed_zero : (0 : ConvexCone R M).Pointed := by rw [Pointed, mem_zero]

/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: : Add (ConvexCone R M) where
  body: {
    carrier := C₁ + C₂
    smul_mem' := by
      rintro c hc _ ⟨x, hx, y, hy, rfl⟩
      rw [smul_add]
      use c • x, C₁.smul_mem hc hx, c • y, C₂.smul_mem hc hy
    add_mem' := by
      rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩ y ⟨y₁, hy₁, y₂, hy₂, rfl⟩
      exact ⟨x₁ + y₁, add_mem hx₁ hy₁, x₂ + y₂, ad

中文:
实例 instAdd
  签名: : 加法 (余nvexCone R M) where
  定义体: {
    carrier := C₁ + C₂
    smul_mem' := by
      rintro c hc _ ⟨x, hx, y, hy, rfl⟩
      rw [smul_add]
      use c • x, C₁.smul_mem hc hx, c • y, C₂.smul_mem hc hy
    add_mem' := by
      rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩ y ⟨y₁, hy₁, y₂, hy₂, rfl⟩
      exact ⟨x₁ + y₁, add_mem hx₁ hy₁, x₂ + y₂, ad
-/
instance instAdd : Add (ConvexCone R M) where
  add C₁ C₂ := {
    carrier := C₁ + C₂
    smul_mem' := by
      rintro c hc _ ⟨x, hx, y, hy, rfl⟩
      rw [smul_add]
      use c • x, C₁.smul_mem hc hx, c • y, C₂.smul_mem hc hy
    add_mem' := by
      rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩ y ⟨y₁, hy₁, y₂, hy₂, rfl⟩
      exact ⟨x₁ + y₁, add_mem hx₁ hy₁, x₂ + y₂, add_mem hx₂ hy₂, add_add_add_comm ..⟩
  }

/--
lemma `coe_add` / 引理 `coe_add`

English:
lemma coe_add
  given: (C₁ C₂ : ConvexCone R M)
  statement: ↑(C₁ + C₂) = (C₁ + C₂ : Set M)
  proof: rfl

中文:
引理 coe_add
  条件: (C₁ C₂ : 余nvexCone R M)
  结论: ↑(C₁ + C₂) = (C₁ + C₂ : 集合 M)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_add (C₁ C₂ : ConvexCone R M) : ↑(C₁ + C₂) = (C₁ + C₂ : Set M) := rfl
/--
lemma `mem_add` / 引理 `mem_add`

English:
lemma mem_add
  statement: x in C₁ + C₂ ↔ exists y in C₁, exists z in C₂, y + z = x
  proof: .rfl

中文:
引理 mem_add
  结论: x in C₁ + C₂ ↔ 存在 y in C₁, 存在 z in C₂, y + z = x
  证明: .rfl
-/
@[simp] lemma mem_add : x in C₁ + C₂ ↔ exists y in C₁, exists z in C₂, y + z = x := .rfl

/--
Instance `instAddZeroClass` / 实例 `instAddZeroClass`

English:
instance instAddZeroClass
  signature: : AddZeroClass (ConvexCone R M) where
  body: by ext; simp
  add_zero _ := by ext; simp

中文:
实例 instAddZeroClass
  签名: : 加法零类 (余nvexCone R M) where
  定义体: by ext; simp
  add_zero _ := by ext; simp

Depends on / 依赖: add_zero
-/
instance instAddZeroClass : AddZeroClass (ConvexCone R M) where
  zero_add _ := by ext; simp
  add_zero _ := by ext; simp

/--
Instance `instAddCommSemigroup` / 实例 `instAddCommSemigroup`

English:
instance instAddCommSemigroup
  signature: : AddCommSemigroup (ConvexCone R M) where
  body: SetLike.coe_injective add_assoc _ _ _
add_comm _ _ := SetLike.coe_injective add_comm _ _

中文:
实例 instAddCommSemigroup
  签名: : 加法交换半群 (余nvexCone R M) where
  定义体: SetLike.coe_injective add_assoc _ _ _
add_comm _ _ := SetLike.coe_injective add_comm _ _

Depends on / 依赖: SetLike, SetLike.coe_injective, add_assoc, coe_injective
-/
instance instAddCommSemigroup : AddCommSemigroup (ConvexCone R M) where
add_assoc _ _ _ := SetLike.coe_injective add_assoc _ _ _
add_comm _ _ := SetLike.coe_injective add_comm _ _

end Monoid

section Reproducing

variable [AddCommGroup M] [Module R M]

/--
Definition of `IsReproducing` / `IsReproducing` 的定义

English:
definition IsReproducing
  signature: (C : ConvexCone R M)
  body: (C : Set M) - (C : Set M) = Set.univ

中文:
定义 IsReproducing
  签名: (C : 余nvexCone R M)
  定义体: (C : Set M) - (C : Set M) = Set.univ

Depends on / 依赖: Set.univ
-/
def IsReproducing (C : ConvexCone R M) : Prop :=
  (C : Set M) - (C : Set M) = Set.univ

/--
theorem `IsReproducing.of_univ_subset` / 定理 `IsReproducing.of_univ_subset`

English:
theorem IsReproducing.of_univ_subset
  statement: {C : ConvexCone R M}
  proof: Set.eq_univ_iff_forall.mpr fun _ => h (Set.mem_univ _)

中文:
定理 IsReproducing.of_univ_subset
  结论: {C : 余nvexCone R M}
  证明: Set.eq_univ_iff_forall.mpr fun _ => h (Set.mem_univ _)

Depends on / 依赖: Set.eq_univ_iff_forall.mpr, Set.mem_univ, eq_univ_iff_forall, mem_univ
-/
theorem IsReproducing.of_univ_subset {C : ConvexCone R M}
    (h : Set.univ subseteq (C : Set M) - (C : Set M)) : C.IsReproducing :=
  Set.eq_univ_iff_forall.mpr fun _ => h (Set.mem_univ _)

/--
lemma `IsReproducing.sub_eq_univ` / 引理 `IsReproducing.sub_eq_univ`

English:
lemma IsReproducing.sub_eq_univ
  given: {C : ConvexCone R M} (hC : C.IsReproducing)
  proof: hC

中文:
引理 IsReproducing.sub_eq_univ
  条件: {C : 余nvexCone R M} (hC : C.IsReproducing)
  证明: hC
-/
lemma IsReproducing.sub_eq_univ {C : ConvexCone R M} (hC : C.IsReproducing) :
    (C : Set M) - (C : Set M) = Set.univ :=
  hC

end Reproducing

section Generating

variable [AddCommMonoid M] [Module R M]

/-- A convex cone `C` is generating if its linear span is the entire `R`-module `M`.

`IsGenerating` is equivalent to `IsReproducing` modulo some conditions.
See `IsReproducing.isGenerating` and `IsGenerating.isReproducing` for details. -/
@[simp, deprecated "write out the definition" (since := "2026-03-30")]
/--
Definition of `IsGenerating` / `IsGenerating` 的定义

English:
definition IsGenerating
  signature: (C : ConvexCone R M)
  body: Submodule.span R (C : Set M) = ⊤

中文:
定义 是Generating
  签名: (C : 余nvexCone R M)
  定义体: Submodule.span R (C : Set M) = ⊤

Depends on / 依赖: Submodule, Submodule.span
-/
def IsGenerating (C : ConvexCone R M) : Prop :=
  Submodule.span R (C : Set M) = ⊤

/-- A sufficient criteria for a convex cone `C` to be generating is that top is less than or equal
to the linear span of `C`. -/
@[deprecated "no replacement" (since := "2026-03-30")]
/--
theorem `IsGenerating.of_top_le_span` / 定理 `IsGenerating.of_top_le_span`

English:
theorem IsGenerating.of_top_le_span
  given: {C : ConvexCone R M} (h : ⊤ <= Submodule.span R (C : Set M))
  proof: eq_top_iff.mpr h

中文:
定理 是Generating.of_top_le_span
  条件: {C : 余nvexCone R M} (h : ⊤ <= 子模.span R (C : 集合 M))
  证明: eq_top_iff.mpr h

Depends on / 依赖: eq_top_iff, eq_top_iff.mpr
-/
theorem IsGenerating.of_top_le_span {C : ConvexCone R M} (h : ⊤ <= Submodule.span R (C : Set M)) :
    C.IsGenerating :=
  eq_top_iff.mpr h

/-- The linear span of a generating convex cone equals top. -/
@[deprecated "no replacement" (since := "2026-03-30")]
/--
lemma `IsGenerating.span_eq_top` / 引理 `IsGenerating.span_eq_top`

English:
lemma IsGenerating.span_eq_top
  given: {C : ConvexCone R M} (hC : C.IsGenerating)
  proof: hC

中文:
引理 是Generating.span_eq_top
  条件: {C : 余nvexCone R M} (hC : C.是Generating)
  证明: hC
-/
lemma IsGenerating.span_eq_top {C : ConvexCone R M} (hC : C.IsGenerating) :
    Submodule.span R (C : Set M) = ⊤ :=
  hC

/-- Top is less than or equal to the linear span of a generating convex cone. -/
@[deprecated "no replacement" (since := "2026-03-30")]
/--
lemma `IsGenerating.top_le_span` / 引理 `IsGenerating.top_le_span`

English:
lemma IsGenerating.top_le_span
  given: {C : ConvexCone R M} (hC : C.IsGenerating)
  proof: hC.span_eq_top.ge

中文:
引理 是Generating.top_le_span
  条件: {C : 余nvexCone R M} (hC : C.是Generating)
  证明: hC.span_eq_top.ge

Depends on / 依赖: hC.span_eq_top.ge, span_eq_top
-/
lemma IsGenerating.top_le_span {C : ConvexCone R M} (hC : C.IsGenerating) :
    ⊤ <= Submodule.span R (C : Set M) :=
  hC.span_eq_top.ge

/-- The whole `R`-module `M` (viewed as the top convex cone) is generating. -/
@[deprecated "no replacement" (since := "2026-03-30")]
/--
theorem `isGenerating_top` / 定理 `isGenerating_top`

English:
theorem isGenerating_top
  statement: (⊤ : ConvexCone R M).IsGenerating
  proof: by
  simp

中文:
定理 isGenerating_top
  结论: (⊤ : 余nvexCone R M).是Generating
  证明: by
  simp
-/
theorem isGenerating_top : (⊤ : ConvexCone R M).IsGenerating := by
  simp

/-- The empty convex cone is generating iff the module is a subsingleton. -/
@[deprecated "no replacement" (since := "2026-03-30")]
/--
theorem `isGenerating_bot_iff` / 定理 `isGenerating_bot_iff`

English:
theorem isGenerating_bot_iff
  statement: (⊥ : ConvexCone R M).IsGenerating ↔ Subsingleton M
  proof: by
  simpa only [IsGenerating, coe_bot, Submodule.span_empty, ← Submodule.subsingleton_iff R] using
    subsingleton_iff_bot_eq_top

中文:
定理 isGenerating_bot_iff
  结论: (⊥ : 余nvexCone R M).是Generating ↔ 子单例 M
  证明: by
  simpa only [IsGenerating, coe_bot, Submodule.span_empty, ← Submodule.subsingleton_iff R] using
    subsingleton_iff_bot_eq_top

Depends on / 依赖: IsGenerating, Submodule, Submodule.span_empty, Submodule.subsingleton_iff, coe_bot, span_empty, subsingleton_iff, subsingleton_iff_bot_eq_top
-/
theorem isGenerating_bot_iff : (⊥ : ConvexCone R M).IsGenerating ↔ Subsingleton M := by
  simpa only [IsGenerating, coe_bot, Submodule.span_empty, ← Submodule.subsingleton_iff R] using
    subsingleton_iff_bot_eq_top

/-- In a subsingleton module, the empty convex cone is generating. -/
@[deprecated "no replacement" (since := "2026-03-30")]
/--
theorem `isGenerating_bot` / 定理 `isGenerating_bot`

English:
theorem isGenerating_bot
  given: [Subsingleton M]
  statement: (⊥ : ConvexCone R M).IsGenerating
  proof: isGenerating_bot_iff.mpr inferInstance

中文:
定理 isGenerating_bot
  条件: [子单例 M]
  结论: (⊥ : 余nvexCone R M).是Generating
  证明: isGenerating_bot_iff.mpr inferInstance

Depends on / 依赖: isGenerating_bot_iff, isGenerating_bot_iff.mpr
-/
theorem isGenerating_bot [Subsingleton M] : (⊥ : ConvexCone R M).IsGenerating :=
  isGenerating_bot_iff.mpr inferInstance

/-- A convex cone containing a generating cone is also a generating cone. -/
@[gcongr, deprecated "no replacement" (since := "2026-03-30")]
/--
theorem `IsGenerating.mono` / 定理 `IsGenerating.mono`

English:
theorem IsGenerating.mono
  given: {C₁ C₂ : ConvexCone R M} (h : C₁ <= C₂) (hgen : C₁.IsGenerating)
  proof: by
  rw [IsGenerating]; rw [← top_le_iff] at hgen ⊢
  exact hgen.trans (Submodule.span_mono h)

中文:
定理 是Generating.mono
  条件: {C₁ C₂ : 余nvexCone R M} (h : C₁ <= C₂) (hgen : C₁.是Generating)
  证明: by
  rw [IsGenerating]; rw [← top_le_iff] at hgen ⊢
  exact hgen.trans (Submodule.span_mono h)

Depends on / 依赖: IsGenerating, Submodule, Submodule.span_mono, hgen.trans, span_mono, top_le_iff
-/
theorem IsGenerating.mono {C₁ C₂ : ConvexCone R M} (h : C₁ <= C₂) (hgen : C₁.IsGenerating) :
    C₂.IsGenerating := by
  rw [IsGenerating]; rw [← top_le_iff] at hgen ⊢
  exact hgen.trans (Submodule.span_mono h)

/--
theorem `IsReproducing.span_eq_top` / 定理 `IsReproducing.span_eq_top`

English:
theorem IsReproducing.span_eq_top
  statement: {R : Type*} {M : Type*} [Ring R] [PartialOrder R]
  proof: by
  rw [eq_top_iff]
  rintro x -
  rw [IsReproducing]; rw [Set.eq_univ_iff_forall] at h
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_sub.mp (h x)
  exact sub_mem (Submodule.subset_span hy) (Submodule.subset_span hz)

@[deprecated (since := "2026-03-30")] alias IsReproducing.isGenerating := IsReproducing

中文:
定理 IsReproducing.span_eq_top
  结论: {R : 类型} {M : 类型} [环 R] [偏序 R]
  证明: by
  rw [eq_top_iff]
  rintro x -
  rw [IsReproducing]; rw [Set.eq_univ_iff_forall] at h
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_sub.mp (h x)
  exact sub_mem (Submodule.subset_span hy) (Submodule.subset_span hz)

@[deprecated (since := "2026-03-30")] alias IsReproducing.isGenerating := IsReproducing

Depends on / 依赖: IsReproducing, Set.eq_univ_iff_forall, Set.mem_sub.mp, Submodule, Submodule.subset_span, eq_top_iff, eq_univ_iff_forall, mem_sub, sub_mem, subset_span
-/
theorem IsReproducing.span_eq_top {R : Type*} {M : Type*} [Ring R] [PartialOrder R]
    [AddCommGroup M] [Module R M] {C : ConvexCone R M} (h : C.IsReproducing) :
    Submodule.span R (C : Set M) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  rw [IsReproducing]; rw [Set.eq_univ_iff_forall] at h
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_sub.mp (h x)
  exact sub_mem (Submodule.subset_span hy) (Submodule.subset_span hz)

@[deprecated (since := "2026-03-30")] alias IsReproducing.isGenerating := IsReproducing.span_eq_top

/--
theorem `IsReproducing.of_span_eq_top` / 定理 `IsReproducing.of_span_eq_top`

English:
theorem IsReproducing.of_span_eq_top
  statement: {R : Type*} {M : Type*} [Ring R] [LinearOrder R]
  proof: by
  rw [IsReproducing]; rw [Set.eq_univ_iff_forall]
  intro x
  -- A generating cone in a nontrivial module must be nonempty
  have hne : (C : Set M).Nonempty := Set.nonempty_iff_ne_empty.2 fun h' => by simp [h'] at h
  -- Build the submodule S = C - C and show span C ⊆ S
  let S : Submodule R M :=

中文:
定理 IsReproducing.of_span_eq_top
  结论: {R : 类型} {M : 类型} [环 R] [线性序 R]
  证明: by
  rw [IsReproducing]; rw [Set.eq_univ_iff_forall]
  intro x
  -- A generating cone in a nontrivial module must be nonempty
  have hne : (C : Set M).Nonempty := Set.nonempty_iff_ne_empty.2 fun h' => by simp [h'] at h
  -- Build the submodule S = C - C and show span C ⊆ S
  let S : Submodule R M :=

Depends on / 依赖: IsReproducing, Set.eq_univ_iff_forall, eq_univ_iff_forall
-/
theorem IsReproducing.of_span_eq_top {R : Type*} {M : Type*} [Ring R] [LinearOrder R]
    [AddLeftStrictMono R] [AddCommGroup M] [Nontrivial M] [Module R M] {C : ConvexCone R M}
    (h : Submodule.span R (C : Set M) = ⊤) :
    C.IsReproducing := by
  rw [IsReproducing]; rw [Set.eq_univ_iff_forall]
  intro x
  -- A generating cone in a nontrivial module must be nonempty
  have hne : (C : Set M).Nonempty := Set.nonempty_iff_ne_empty.2 fun h' => by simp [h'] at h
  -- Build the submodule S = C - C and show span C ⊆ S
  let S : Submodule R M := {
    carrier := (C : Set M) - (C : Set M)
    add_mem' := by
      rintro _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      exact ⟨y₁ + y₂, C.add_mem hy₁ hy₂, z₁ + z₂, C.add_mem hz₁ hz₂, add_sub_add_comm ..⟩
    zero_mem' := by
      obtain ⟨c, hc⟩ := hne
      exact ⟨c, hc, c, hc, sub_self c⟩
    smul_mem' := by
      rintro r _ ⟨y, hy, z, hz, rfl⟩
      simp only [Set.mem_sub, SetLike.mem_coe]
      rcases lt_trichotomy r 0 with hr | rfl | hr
      · -- r < 0: use (-r) • z - (-r) • y = r • (y - z)
        refine ⟨(-r) • z, C.smul_mem (neg_pos.mpr hr) hz,
               (-r) • y, C.smul_mem (neg_pos.mpr hr) hy, ?_⟩
        rw [neg_smul]; rw [neg_smul]; rw [neg_sub_neg]; rw [smul_sub]
      · -- r = 0
        simp only [zero_smul]
        obtain ⟨c, hc⟩ := hne
        exact ⟨c, hc, c, hc, sub_self c⟩
      · -- r > 0: use r • y - r • z
        exact ⟨r • y, C.smul_mem hr hy, r • z, C.smul_mem hr hz, (smul_sub r y z).symm⟩}
  have hCS : (C : Set M) subseteq S := fun x hx =>
    let ⟨c, hc⟩ := hne; ⟨x + c, C.add_mem hx hc, c, hc, add_sub_cancel_right x c⟩
  exact (h ▸ Submodule.span_le.mpr hCS) trivial

@[deprecated (since := "2026-03-30")]
alias IsGenerating.isReproducing := IsReproducing.of_span_eq_top

/--
theorem `span_eq_top_iff_isReproducing` / 定理 `span_eq_top_iff_isReproducing`

English:
theorem span_eq_top_iff_isReproducing
  statement: {R : Type*} {M : Type*} [Ring R] [LinearOrder R]
  proof: ⟨.of_span_eq_top, IsReproducing.span_eq_top⟩

@[deprecated (since := "2026-03-30")]
alias isGenerating_iff_isReproducing := IsReproducing.span_eq_top

中文:
定理 span_eq_top_iff_isReproducing
  结论: {R : 类型} {M : 类型} [环 R] [线性序 R]
  证明: ⟨.of_span_eq_top, IsReproducing.span_eq_top⟩

@[deprecated (since := "2026-03-30")]
alias isGenerating_iff_isReproducing := IsReproducing.span_eq_top

Depends on / 依赖: IsReproducing, IsReproducing.span_eq_top, of_span_eq_top, span_eq_top
-/
theorem span_eq_top_iff_isReproducing {R : Type*} {M : Type*} [Ring R] [LinearOrder R]
    [AddLeftStrictMono R] [AddCommGroup M] [Nontrivial M] [Module R M] {C : ConvexCone R M} :
    Submodule.span R (C : Set M) = ⊤ ↔ C.IsReproducing :=
  ⟨.of_span_eq_top, IsReproducing.span_eq_top⟩

@[deprecated (since := "2026-03-30")]
alias isGenerating_iff_isReproducing := IsReproducing.span_eq_top

end Generating

end Module

end OrderedSemiring

section Field
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup M] [Module 𝕜 M]
  {C : ConvexCone 𝕜 M} {s : Set M} {x : M}

/--
lemma `mem_hull_of_convex` / 引理 `mem_hull_of_convex`

English:
lemma mem_hull_of_convex
  given: (hs : Convex 𝕜 s)
  statement: x in hull 𝕜 s ↔ exists r : 𝕜, 0 < r ∧ x in r • s where
  proof: hull_min (C := {
              carrier := {y | exists r : 𝕜, 0 < r ∧ y in r • s}
              smul_mem' := by
                intro r₁ hr₁ y ⟨r₂, hr₂, hy⟩
                refine ⟨r₁ * r₂, mul_pos hr₁ hr₂, ?_⟩
                rw [mul_smul]
                exact smul_mem_smul_set hy
              add

中文:
引理 mem_hull_of_convex
  条件: (hs : 凸 𝕜 s)
  结论: x in hull 𝕜 s ↔ 存在 r : 𝕜, 0 < r ∧ x in r • s where
  证明: hull_min (C := {
              carrier := {y | exists r : 𝕜, 0 < r ∧ y in r • s}
              smul_mem' := by
                intro r₁ hr₁ y ⟨r₂, hr₂, hy⟩
                refine ⟨r₁ * r₂, mul_pos hr₁ hr₂, ?_⟩
                rw [mul_smul]
                exact smul_mem_smul_set hy
              add

Depends on / 依赖: hull_min
-/
lemma mem_hull_of_convex (hs : Convex 𝕜 s) : x in hull 𝕜 s ↔ exists r : 𝕜, 0 < r ∧ x in r • s where
  mp hx := hull_min (C := {
              carrier := {y | exists r : 𝕜, 0 < r ∧ y in r • s}
              smul_mem' := by
                intro r₁ hr₁ y ⟨r₂, hr₂, hy⟩
                refine ⟨r₁ * r₂, mul_pos hr₁ hr₂, ?_⟩
                rw [mul_smul]
                exact smul_mem_smul_set hy
              add_mem' := by
                rintro y₁ ⟨r₁, hr₁, hy₁⟩ y₂ ⟨r₂, hr₂, hy₂⟩
                refine ⟨r₁ + r₂, add_pos hr₁ hr₂, ?_⟩
                rw [hs.add_smul hr₁.le hr₂.le]
                exact add_mem_add hy₁ hy₂
            }) (fun y hy => ⟨1, by simpa⟩) hx
mpr := by rintro ⟨r, hr, y, hy, rfl⟩; exact (hull 𝕜 s).smul_mem hr subset_hull hy

/--
lemma `coe_hull_of_convex` / 引理 `coe_hull_of_convex`

English:
lemma coe_hull_of_convex
  given: (hs : Convex 𝕜 s)
  statement: hull 𝕜 s = {x | exists r : 𝕜, 0 < r ∧ x in r • s}
  proof: by
  ext; exact mem_hull_of_convex hs

中文:
引理 coe_hull_of_convex
  条件: (hs : 凸 𝕜 s)
  结论: hull 𝕜 s = {x | 存在 r : 𝕜, 0 < r ∧ x in r • s}
  证明: by
  ext; exact mem_hull_of_convex hs

Depends on / 依赖: mem_hull_of_convex
-/
lemma coe_hull_of_convex (hs : Convex 𝕜 s) : hull 𝕜 s = {x | exists r : 𝕜, 0 < r ∧ x in r • s} := by
  ext; exact mem_hull_of_convex hs

/--
lemma `disjoint_hull_left_of_convex` / 引理 `disjoint_hull_left_of_convex`

English:
lemma disjoint_hull_left_of_convex
  given: (hs : Convex 𝕜 s)
  statement: Disjoint (hull 𝕜 s) C ↔ Disjoint s C where
  proof: by rw [← disjoint_coe]; exact .mono_left subset_hull
  mpr := by
    simp_rw [← disjoint_coe, disjoint_left, SetLike.mem_coe, mem_hull_of_convex hs]
    rintro hsC _ ⟨r, hr, y, hy, rfl⟩
    exact (C.smul_mem_iff hr).not.mpr (hsC hy)

中文:
引理 disjoint_hull_left_of_convex
  条件: (hs : 凸 𝕜 s)
  结论: Disjoint (hull 𝕜 s) C ↔ Disjoint s C where
  证明: by rw [← disjoint_coe]; exact .mono_left subset_hull
  mpr := by
    simp_rw [← disjoint_coe, disjoint_left, SetLike.mem_coe, mem_hull_of_convex hs]
    rintro hsC _ ⟨r, hr, y, hy, rfl⟩
    exact (C.smul_mem_iff hr).not.mpr (hsC hy)

Depends on / 依赖: C.smul_mem_iff, SetLike, SetLike.mem_coe, disjoint_coe, disjoint_left, mem_coe, mem_hull_of_convex, mono_left, not.mpr, simp_rw, smul_mem_iff, subset_hull
-/
lemma disjoint_hull_left_of_convex (hs : Convex 𝕜 s) : Disjoint (hull 𝕜 s) C ↔ Disjoint s C where
  mp := by rw [← disjoint_coe]; exact .mono_left subset_hull
  mpr := by
    simp_rw [← disjoint_coe, disjoint_left, SetLike.mem_coe, mem_hull_of_convex hs]
    rintro hsC _ ⟨r, hr, y, hy, rfl⟩
    exact (C.smul_mem_iff hr).not.mpr (hsC hy)

/--
lemma `disjoint_hull_right_of_convex` / 引理 `disjoint_hull_right_of_convex`

English:
lemma disjoint_hull_right_of_convex
  given: (hs : Convex 𝕜 s)
  statement: Disjoint C (hull 𝕜 s) ↔ Disjoint ↑C s
  proof: by
  rw [disjoint_comm]; rw [disjoint_hull_left_of_convex hs]; rw [disjoint_comm]

中文:
引理 disjoint_hull_right_of_convex
  条件: (hs : 凸 𝕜 s)
  结论: Disjoint C (hull 𝕜 s) ↔ Disjoint ↑C s
  证明: by
  rw [disjoint_comm]; rw [disjoint_hull_left_of_convex hs]; rw [disjoint_comm]

Depends on / 依赖: disjoint_comm, disjoint_hull_left_of_convex
-/
lemma disjoint_hull_right_of_convex (hs : Convex 𝕜 s) : Disjoint C (hull 𝕜 s) ↔ Disjoint ↑C s := by
  rw [disjoint_comm]; rw [disjoint_hull_left_of_convex hs]; rw [disjoint_comm]

end Field
end ConvexCone

namespace Submodule

/-! ### Submodules are cones -/


section OrderedSemiring

variable [Semiring R] [PartialOrder R]

section AddCommMonoid

variable [AddCommMonoid M] [Module R M] {C C₁ C₂ : Submodule R M} {x : M}

/--
Definition of `toConvexCone` / `toConvexCone` 的定义

English:
definition toConvexCone
  signature: (C : Submodule R M)
  body: C
  smul_mem' c _ _ hx := C.smul_mem c hx
  add_mem' _ hx _ hy := C.add_mem hx hy

中文:
定义 toConvexCone
  签名: (C : 子模 R M)
  定义体: C
  smul_mem' c _ _ hx := C.smul_mem c hx
  add_mem' _ hx _ hy := C.add_mem hx hy
-/
def toConvexCone (C : Submodule R M) : ConvexCone R M where
  carrier := C
  smul_mem' c _ _ hx := C.smul_mem c hx
  add_mem' _ hx _ hy := C.add_mem hx hy

/--
lemma `coe_toConvexCone` / 引理 `coe_toConvexCone`

English:
lemma coe_toConvexCone
  given: (C : Submodule R M)
  statement: C.toConvexCone = (C : Set M)
  proof: rfl

中文:
引理 coe_toConvexCone
  条件: (C : 子模 R M)
  结论: C.toConvexCone = (C : 集合 M)
  证明: rfl
-/
@[simp] lemma coe_toConvexCone (C : Submodule R M) : C.toConvexCone = (C : Set M) := rfl

/--
lemma `mem_toConvexCone` / 引理 `mem_toConvexCone`

English:
lemma mem_toConvexCone
  statement: x in C.toConvexCone ↔ x in C
  proof: .rfl

@[simp]

中文:
引理 mem_toConvexCone
  结论: x in C.toConvexCone ↔ x in C
  证明: .rfl

@[simp]
-/
@[simp] lemma mem_toConvexCone : x in C.toConvexCone ↔ x in C := .rfl

@[simp]
/--
lemma `toConvexCone_le_toConvexCone` / 引理 `toConvexCone_le_toConvexCone`

English:
lemma toConvexCone_le_toConvexCone
  statement: C₁.toConvexCone <= C₂.toConvexCone ↔ C₁ <= C₂
  proof: .rfl

中文:
引理 toConvexCone_le_toConvexCone
  结论: C₁.toConvexCone <= C₂.toConvexCone ↔ C₁ <= C₂
  证明: .rfl
-/
lemma toConvexCone_le_toConvexCone : C₁.toConvexCone <= C₂.toConvexCone ↔ C₁ <= C₂ := .rfl

/--
lemma `toConvexCone_bot` / 引理 `toConvexCone_bot`

English:
lemma toConvexCone_bot
  statement: (⊥ : Submodule R M).toConvexCone = 0
  proof: rfl

中文:
引理 toConvexCone_bot
  结论: (⊥ : 子模 R M).toConvexCone = 0
  证明: rfl
-/
@[simp] lemma toConvexCone_bot : (⊥ : Submodule R M).toConvexCone = 0 := rfl
/--
lemma `toConvexCone_top` / 引理 `toConvexCone_top`

English:
lemma toConvexCone_top
  statement: (⊤ : Submodule R M).toConvexCone = ⊤
  proof: rfl

@[simp]

中文:
引理 toConvexCone_top
  结论: (⊤ : 子模 R M).toConvexCone = ⊤
  证明: rfl

@[simp]
-/
@[simp] lemma toConvexCone_top : (⊤ : Submodule R M).toConvexCone = ⊤ := rfl

@[simp]
/--
lemma `toConvexCone_inf` / 引理 `toConvexCone_inf`

English:
lemma toConvexCone_inf
  given: (C₁ C₂ : Submodule R M)
  proof: rfl

@[simp]

中文:
引理 toConvexCone_inf
  条件: (C₁ C₂ : 子模 R M)
  证明: rfl

@[simp]
-/
lemma toConvexCone_inf (C₁ C₂ : Submodule R M) :
    (C₁ ⊓ C₂).toConvexCone = C₁.toConvexCone ⊓ C₂.toConvexCone := rfl

@[simp]
/--
lemma `pointed_toConvexCone` / 引理 `pointed_toConvexCone`

English:
lemma pointed_toConvexCone
  given: (C : Submodule R M)
  statement: C.toConvexCone.Pointed
  proof: C.zero_mem

中文:
引理 pointed_toConvexCone
  条件: (C : 子模 R M)
  结论: C.toConvexCone.Pointed
  证明: C.zero_mem

Depends on / 依赖: C.zero_mem, zero_mem
-/
lemma pointed_toConvexCone (C : Submodule R M) : C.toConvexCone.Pointed := C.zero_mem

end AddCommMonoid

end OrderedSemiring

end Submodule

/-! ### Positive cone of an ordered module -/

namespace ConvexCone

section PositiveCone
variable [Semiring R] [PartialOrder R] [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  [Module R M] [PosSMulMono R M] {x : M}

variable (R M) in
/--
Definition of `positive` / `positive` 的定义

English:
definition positive
  signature: : ConvexCone R M where
  body: Set.Ici 0
  smul_mem' _ hc _ (hx : _ <= _) := smul_nonneg hc.le hx
  add_mem' _ (hx : _ <= _) _ (hy : _ <= _) := add_nonneg hx hy

中文:
定义 positive
  签名: : 余nvexCone R M where
  定义体: Set.Ici 0
  smul_mem' _ hc _ (hx : _ <= _) := smul_nonneg hc.le hx
  add_mem' _ (hx : _ <= _) _ (hy : _ <= _) := add_nonneg hx hy

Depends on / 依赖: Set.Ici
-/
def positive : ConvexCone R M where
  carrier := Set.Ici 0
  smul_mem' _ hc _ (hx : _ <= _) := smul_nonneg hc.le hx
  add_mem' _ (hx : _ <= _) _ (hy : _ <= _) := add_nonneg hx hy

/--
lemma `mem_positive` / 引理 `mem_positive`

English:
lemma mem_positive
  statement: x in positive R M ↔ 0 <= x
  proof: .rfl

中文:
引理 mem_positive
  结论: x in positive R M ↔ 0 <= x
  证明: .rfl
-/
@[simp] lemma mem_positive : x in positive R M ↔ 0 <= x := .rfl

variable (R M) in
@[simp]
/--
theorem `coe_positive` / 定理 `coe_positive`

English:
theorem coe_positive
  statement: ↑(positive R M) = Set.Ici (0 : M)
  proof: rfl

中文:
定理 coe_positive
  结论: ↑(positive R M) = 集合.左闭右无界区间 (0 : M)
  证明: rfl
-/
theorem coe_positive : ↑(positive R M) = Set.Ici (0 : M) :=
  rfl

/--
lemma `salient_positive` / 引理 `salient_positive`

English:
lemma salient_positive
  statement: {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]
  proof: fun x hx_nonneg hx_ne_zero hx_nonpos => lt_irrefl (0 : G) by
simpa using add_pos_of_nonneg_of_pos hx_nonpos hx_nonneg.lt_of_ne' hx_ne_zero

中文:
引理 salient_positive
  结论: {G : 类型} [加法交换群 G] [偏序 G] [是OrderedAdd幺半群 G]
  证明: fun x hx_nonneg hx_ne_zero hx_nonpos => lt_irrefl (0 : G) by
simpa using add_pos_of_nonneg_of_pos hx_nonpos hx_nonneg.lt_of_ne' hx_ne_zero

Depends on / 依赖: add_pos_of_nonneg_of_pos, hx_ne_zero, hx_nonneg, hx_nonneg.lt_of_ne, hx_nonpos, lt_irrefl, lt_of_ne
-/
lemma salient_positive {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]
    [Module R G] [PosSMulMono R G] : Salient (positive R G) :=
fun x hx_nonneg hx_ne_zero hx_nonpos => lt_irrefl (0 : G) by
simpa using add_pos_of_nonneg_of_pos hx_nonpos hx_nonneg.lt_of_ne' hx_ne_zero

/--
theorem `pointed_positive` / 定理 `pointed_positive`

English:
theorem pointed_positive
  statement: Pointed (positive R M)
  proof: le_refl 0

中文:
定理 pointed_positive
  结论: Pointed (positive R M)
  证明: le_refl 0

Depends on / 依赖: le_refl
-/
theorem pointed_positive : Pointed (positive R M) :=
  le_refl 0

end PositiveCone

section StrictlyPositiveCone
variable [Semiring R] [PartialOrder R] [AddCommGroup M] [PartialOrder M] [IsOrderedAddMonoid M]
  [Module R M] [PosSMulStrictMono R M] {x : M}

variable (R M) in
/--
Definition of `strictlyPositive` / `strictlyPositive` 的定义

English:
definition strictlyPositive
  signature: : ConvexCone R M where
  body: Set.Ioi 0
  smul_mem' _ hc _ (hx : _ < _) := smul_pos hc hx
  add_mem' _ hx _ hy := add_pos hx hy

@[simp]

中文:
定义 strictlyPositive
  签名: : 余nvexCone R M where
  定义体: Set.Ioi 0
  smul_mem' _ hc _ (hx : _ < _) := smul_pos hc hx
  add_mem' _ hx _ hy := add_pos hx hy

@[simp]

Depends on / 依赖: Set.Ioi
-/
def strictlyPositive : ConvexCone R M where
  carrier := Set.Ioi 0
  smul_mem' _ hc _ (hx : _ < _) := smul_pos hc hx
  add_mem' _ hx _ hy := add_pos hx hy

@[simp]
/--
lemma `mem_strictlyPositive` / 引理 `mem_strictlyPositive`

English:
lemma mem_strictlyPositive
  statement: x in strictlyPositive R M ↔ 0 < x
  proof: .rfl

中文:
引理 mem_strictlyPositive
  结论: x in strictlyPositive R M ↔ 0 < x
  证明: .rfl
-/
lemma mem_strictlyPositive : x in strictlyPositive R M ↔ 0 < x := .rfl

variable (R M) in
@[simp]
/--
theorem `coe_strictlyPositive` / 定理 `coe_strictlyPositive`

English:
theorem coe_strictlyPositive
  statement: ↑(strictlyPositive R M) = Set.Ioi (0 : M)
  proof: rfl

中文:
定理 coe_strictlyPositive
  结论: ↑(strictlyPositive R M) = 集合.左开右无界区间 (0 : M)
  证明: rfl
-/
theorem coe_strictlyPositive : ↑(strictlyPositive R M) = Set.Ioi (0 : M) :=
  rfl

/--
lemma `strictlyPositive_le_positive` / 引理 `strictlyPositive_le_positive`

English:
lemma strictlyPositive_le_positive
  statement: strictlyPositive R M <= positive R M
  proof: fun _ => le_of_lt

中文:
引理 strictlyPositive_le_positive
  结论: strictlyPositive R M <= positive R M
  证明: fun _ => le_of_lt

Depends on / 依赖: le_of_lt
-/
lemma strictlyPositive_le_positive : strictlyPositive R M <= positive R M := fun _ => le_of_lt

/--
theorem `salient_strictlyPositive` / 定理 `salient_strictlyPositive`

English:
theorem salient_strictlyPositive
  statement: Salient (strictlyPositive R M)
  proof: salient_positive.anti strictlyPositive_le_positive

中文:
定理 salient_strictlyPositive
  结论: Salient (strictlyPositive R M)
  证明: salient_positive.anti strictlyPositive_le_positive

Depends on / 依赖: salient_positive, salient_positive.anti, strictlyPositive_le_positive
-/
theorem salient_strictlyPositive : Salient (strictlyPositive R M) :=
  salient_positive.anti strictlyPositive_le_positive

/--
theorem `blunt_strictlyPositive` / 定理 `blunt_strictlyPositive`

English:
theorem blunt_strictlyPositive
  statement: Blunt (strictlyPositive R M)
  proof: lt_irrefl 0

中文:
定理 blunt_strictlyPositive
  结论: Blunt (strictlyPositive R M)
  证明: lt_irrefl 0

Depends on / 依赖: lt_irrefl
-/
theorem blunt_strictlyPositive : Blunt (strictlyPositive R M) :=
  lt_irrefl 0

end StrictlyPositiveCone

end ConvexCone

/-! ### Cone over a convex set -/


section ConeFromConvex

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup M] [Module 𝕜 M]

namespace Convex

/-- The set of vectors proportional to those in a convex set forms a convex cone. -/
@[deprecated "Use `ConvexCone.hull` and `ConvexCone.coe_hull_of_convex`" (since := "2026-03-30")]
/--
Definition of `toCone` / `toCone` 的定义

English:
definition toCone
  signature: (s : Set M) (hs : Convex 𝕜 s)
  body: by
  apply ConvexCone.mk (⋃ (c : 𝕜) (_ : 0 < c), c • s) <;> simp only [mem_iUnion, mem_smul_set]
  · rintro c c_pos _ ⟨c', c'_pos, x, hx, rfl⟩
    exact ⟨c * c', mul_pos c_pos c'_pos, x, hx, (smul_smul _ _ _).symm⟩
  · rintro _ ⟨cx, cx_pos, x, hx, rfl⟩ _ ⟨cy, cy_pos, y, hy, rfl⟩
    have : 0 < cx + 

中文:
定义 toCone
  签名: (s : 集合 M) (hs : 凸 𝕜 s)
  定义体: by
  apply ConvexCone.mk (⋃ (c : 𝕜) (_ : 0 < c), c • s) <;> simp only [mem_iUnion, mem_smul_set]
  · rintro c c_pos _ ⟨c', c'_pos, x, hx, rfl⟩
    exact ⟨c * c', mul_pos c_pos c'_pos, x, hx, (smul_smul _ _ _).symm⟩
  · rintro _ ⟨cx, cx_pos, x, hx, rfl⟩ _ ⟨cy, cy_pos, y, hy, rfl⟩
    have : 0 < cx + 

Depends on / 依赖: ConvexCone, ConvexCone.mk, _pos, add_pos, c_pos, convex_iff_div, cx_pos, cx_pos.le, cy_pos, cy_pos.le, mem_iUnion, mem_smul_set, mul_div_assoc, mul_pos, smul_add, smul_smul, this.ne
-/
def toCone (s : Set M) (hs : Convex 𝕜 s) : ConvexCone 𝕜 M := by
  apply ConvexCone.mk (⋃ (c : 𝕜) (_ : 0 < c), c • s) <;> simp only [mem_iUnion, mem_smul_set]
  · rintro c c_pos _ ⟨c', c'_pos, x, hx, rfl⟩
    exact ⟨c * c', mul_pos c_pos c'_pos, x, hx, (smul_smul _ _ _).symm⟩
  · rintro _ ⟨cx, cx_pos, x, hx, rfl⟩ _ ⟨cy, cy_pos, y, hy, rfl⟩
    have : 0 < cx + cy := add_pos cx_pos cy_pos
    refine ⟨_, this, _, convex_iff_div.1 hs hx hy cx_pos.le cy_pos.le this, ?_⟩
    simp only [smul_add, smul_smul, mul_div_assoc', mul_div_cancel_left₀ _ this.ne']

variable {s : Set M} (hs : Convex 𝕜 s) {x : M}

@[deprecated ConvexCone.mem_hull_of_convex (since := "2026-03-30")]
/--
theorem `mem_toCone` / 定理 `mem_toCone`

English:
theorem mem_toCone
  statement: x in hs.toCone s ↔ exists c : 𝕜, 0 < c ∧ exists y in s, c • y = x
  proof: by
  simp only [toCone, ConvexCone.mem_mk, mem_iUnion, mem_smul_set, eq_comm, exists_prop]

@[deprecated ConvexCone.mem_hull_of_convex (since := "2026-03-30")]

中文:
定理 mem_toCone
  结论: x in hs.toCone s ↔ 存在 c : 𝕜, 0 < c ∧ 存在 y in s, c • y = x
  证明: by
  simp only [toCone, ConvexCone.mem_mk, mem_iUnion, mem_smul_set, eq_comm, exists_prop]

@[deprecated ConvexCone.mem_hull_of_convex (since := "2026-03-30")]

Depends on / 依赖: ConvexCone, ConvexCone.mem_mk, eq_comm, exists_prop, mem_iUnion, mem_mk, mem_smul_set, toCone
-/
theorem mem_toCone : x in hs.toCone s ↔ exists c : 𝕜, 0 < c ∧ exists y in s, c • y = x := by
  simp only [toCone, ConvexCone.mem_mk, mem_iUnion, mem_smul_set, eq_comm, exists_prop]

@[deprecated ConvexCone.mem_hull_of_convex (since := "2026-03-30")]
/--
theorem `mem_toCone'` / 定理 `mem_toCone'`

English:
theorem mem_toCone'
  statement: x in hs.toCone s ↔ exists c : 𝕜, 0 < c ∧ c • x in s
  proof: by
  refine hs.mem_toCone.trans ⟨?_, ?_⟩
  · rintro ⟨c, hc, y, hy, rfl⟩
    exact ⟨c⁻¹, inv_pos.2 hc, by rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]⟩
  · rintro ⟨c, hc, hcx⟩
    exact ⟨c⁻¹, inv_pos.2 hc, _, hcx, by rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]⟩

@[deprecated ConvexCone.subs

中文:
定理 mem_toCone'
  结论: x in hs.toCone s ↔ 存在 c : 𝕜, 0 < c ∧ c • x in s
  证明: by
  refine hs.mem_toCone.trans ⟨?_, ?_⟩
  · rintro ⟨c, hc, y, hy, rfl⟩
    exact ⟨c⁻¹, inv_pos.2 hc, by rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]⟩
  · rintro ⟨c, hc, hcx⟩
    exact ⟨c⁻¹, inv_pos.2 hc, _, hcx, by rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]⟩

@[deprecated ConvexCone.subs

Depends on / 依赖: hc.ne, hs.mem_toCone.trans, inv_pos, mem_toCone, one_smul, smul_smul
-/
theorem mem_toCone' : x in hs.toCone s ↔ exists c : 𝕜, 0 < c ∧ c • x in s := by
  refine hs.mem_toCone.trans ⟨?_, ?_⟩
  · rintro ⟨c, hc, y, hy, rfl⟩
    exact ⟨c⁻¹, inv_pos.2 hc, by rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]⟩
  · rintro ⟨c, hc, hcx⟩
    exact ⟨c⁻¹, inv_pos.2 hc, _, hcx, by rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]⟩

@[deprecated ConvexCone.subset_hull (since := "2026-03-30")]
/--
theorem `subset_toCone` / 定理 `subset_toCone`

English:
theorem subset_toCone
  statement: s subseteq hs.toCone s
  proof: fun x hx =>
  hs.mem_toCone'.2 ⟨1, zero_lt_one, by rwa [one_smul]⟩

中文:
定理 subset_toCone
  结论: s subseteq hs.toCone s
  证明: fun x hx =>
  hs.mem_toCone'.2 ⟨1, zero_lt_one, by rwa [one_smul]⟩
-/
theorem subset_toCone : s subseteq hs.toCone s := fun x hx =>
  hs.mem_toCone'.2 ⟨1, zero_lt_one, by rwa [one_smul]⟩

/-- `hs.toCone s` is the least cone that includes `s`. -/
@[deprecated "`ConvexCone.gi.gc.isLeast_l`" (since := "2026-03-30")]
/--
theorem `toCone_isLeast` / 定理 `toCone_isLeast`

English:
theorem toCone_isLeast
  statement: IsLeast { t : ConvexCone 𝕜 M | s subseteq t } (hs.toCone s)
  proof: by
  refine ⟨hs.subset_toCone, fun t ht x hx => ?_⟩
  rcases hs.mem_toCone.1 hx with ⟨c, hc, y, hy, rfl⟩
  exact t.smul_mem hc (ht hy)

@[deprecated "`ConvexCone.gi.gc.isLUB_u.sSup_eq`" (since := "2026-03-30")]

中文:
定理 toCone_isLeast
  结论: IsLeast { t : 余nvexCone 𝕜 M | s subseteq t } (hs.toCone s)
  证明: by
  refine ⟨hs.subset_toCone, fun t ht x hx => ?_⟩
  rcases hs.mem_toCone.1 hx with ⟨c, hc, y, hy, rfl⟩
  exact t.smul_mem hc (ht hy)

@[deprecated "`ConvexCone.gi.gc.isLUB_u.sSup_eq`" (since := "2026-03-30")]

Depends on / 依赖: hs.mem_toCone, hs.subset_toCone, mem_toCone, smul_mem, subset_toCone, t.smul_mem
-/
theorem toCone_isLeast : IsLeast { t : ConvexCone 𝕜 M | s subseteq t } (hs.toCone s) := by
  refine ⟨hs.subset_toCone, fun t ht x hx => ?_⟩
  rcases hs.mem_toCone.1 hx with ⟨c, hc, y, hy, rfl⟩
  exact t.smul_mem hc (ht hy)

@[deprecated "`ConvexCone.gi.gc.isLUB_u.sSup_eq`" (since := "2026-03-30")]
/--
theorem `toCone_eq_sInf` / 定理 `toCone_eq_sInf`

English:
theorem toCone_eq_sInf
  statement: hs.toCone s = sInf { t : ConvexCone 𝕜 M | s subseteq t }
  proof: hs.toCone_isLeast.isGLB.sInf_eq.symm

中文:
定理 toCone_eq_sInf
  结论: hs.toCone s = sInf { t : 余nvexCone 𝕜 M | s subseteq t }
  证明: hs.toCone_isLeast.isGLB.sInf_eq.symm

Depends on / 依赖: hs.toCone_isLeast.isGLB.sInf_eq.symm, sInf_eq, toCone_isLeast
-/
theorem toCone_eq_sInf : hs.toCone s = sInf { t : ConvexCone 𝕜 M | s subseteq t } :=
  hs.toCone_isLeast.isGLB.sInf_eq.symm

end Convex

@[deprecated "no replacement" (since := "2026-03-30")]
/--
theorem `convexHull_toCone_isLeast` / 定理 `convexHull_toCone_isLeast`

English:
theorem convexHull_toCone_isLeast
  given: (s : Set M)
  proof: by
  convert! (convex_convexHull 𝕜 s).toCone_isLeast using 1
  ext t
  exact ⟨fun h => convexHull_min h t.convex, (subset_convexHull 𝕜 s).trans⟩

@[deprecated "no replacement" (since := "2026-03-30")]

中文:
定理 convexHull_toCone_isLeast
  条件: (s : 集合 M)
  证明: by
  convert! (convex_convexHull 𝕜 s).toCone_isLeast using 1
  ext t
  exact ⟨fun h => convexHull_min h t.convex, (subset_convexHull 𝕜 s).trans⟩

@[deprecated "no replacement" (since := "2026-03-30")]

Depends on / 依赖: convert, convex, convexHull_min, convex_convexHull, subset_convexHull, t.convex, toCone_isLeast
-/
theorem convexHull_toCone_isLeast (s : Set M) :
    IsLeast { t : ConvexCone 𝕜 M | s subseteq t } ((convex_convexHull 𝕜 s).toCone _) := by
  convert! (convex_convexHull 𝕜 s).toCone_isLeast using 1
  ext t
  exact ⟨fun h => convexHull_min h t.convex, (subset_convexHull 𝕜 s).trans⟩

@[deprecated "no replacement" (since := "2026-03-30")]
/--
theorem `convexHull_toCone_eq_sInf` / 定理 `convexHull_toCone_eq_sInf`

English:
theorem convexHull_toCone_eq_sInf
  given: (s : Set M)
  proof: Eq.symm IsGLB.sInf_eq IsLeast.isGLB convexHull_toCone_isLeast s

中文:
定理 convexHull_toCone_eq_sInf
  条件: (s : 集合 M)
  证明: Eq.symm IsGLB.sInf_eq IsLeast.isGLB convexHull_toCone_isLeast s

Depends on / 依赖: Eq.symm, IsGLB.sInf_eq, IsLeast, IsLeast.isGLB, convexHull_toCone_isLeast, sInf_eq
-/
theorem convexHull_toCone_eq_sInf (s : Set M) :
    (convex_convexHull 𝕜 s).toCone _ = sInf { t : ConvexCone 𝕜 M | s subseteq t } :=
Eq.symm IsGLB.sInf_eq IsLeast.isGLB convexHull_toCone_isLeast s

end ConeFromConvex
