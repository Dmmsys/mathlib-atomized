/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.OmegaCompletePartialOrder

/-! # Saturation of a submonoid

We define a submonoid `s` to be saturated if `x * y ∈ s → x ∈ s ∧ y ∈ s`. The type of all
saturated submonoids forms a complete lattice. For a given submonoid `s` we construct the saturation
of `s` as the smallest saturated submonoid containing `s`, which when the underlying type is a
commutative monoid, is given by the formula `{x : M | ∃ y : M, x * y ∈ s}`.

Saturated submonoids are used in the context of localisations.

We also define the type of saturated submonoids, and endow on it the structure of a complete
lattice.

## Main Definitions

* `Submonoid.MulSaturated`: the condition `x * y ∈ s ↔ x ∈ s ∧ y ∈ s`. Not to be confused with
  `Submonoid.PowSaturated`.
* `SaturatedSubmonoid`: the type of `Submonoid` satisfying `MulSaturated`. It is a complete lattice.
* `Submonoid.saturation`: the smallest saturated submonoid containing a given submonoid.

-/

@[expose] public section

namespace Submonoid

/-- Given a submonoid `s` of `M`, we say that `s` is **saturated** if it satisfies
`x * y ∈ s → x ∈ s ∧ y ∈ s`.

It is called `MulSaturated` here to be distinguished from `Submonoid.PowSaturated` or
`AddSubmonoid.NSMulSaturated`, which is also called "saturated" in the literature. -/
@[to_additive
/-- Given an additive submonoid `s` of `M`, we say that `s` is **saturated** if it satisfies
`x + y ∈ s → x ∈ s ∧ y ∈ s`.

It is called `AddSaturated` here to be distinguished from `Submonoid.PowSaturated` or
`AddSubmonoid.NSMulSaturated`, which is also called "saturated" in the literature. -/]
/--
Definition of `MulSaturated` / `MulSaturated` 的定义

English:
definition MulSaturated
  signature: {M : Type*} [MulOneClass M] (s : Submonoid M)
  body: forall ⦃x y⦄, x * y in s -> x in s ∧ y in s

中文:
定义 MulSaturated
  签名: {M : 类型} [MulOne类 M] (s : 子幺半群 M)
  定义体: forall ⦃x y⦄, x * y in s -> x in s ∧ y in s
-/
def MulSaturated {M : Type*} [MulOneClass M] (s : Submonoid M) : Prop :=
  forall ⦃x y⦄, x * y in s -> x in s ∧ y in s

namespace MulSaturated
variable {M : Type*} [MulOneClass M] {s s₁ s₂ : Submonoid M}
  (h : s.MulSaturated) (h₁ : s₁.MulSaturated) (h₂ : s₂.MulSaturated)

include h in
@[to_additive]
/--
theorem `mul_mem_iff` / 定理 `mul_mem_iff`

English:
theorem mul_mem_iff
  given: {x y : M}
  statement: x * y in s ↔ x in s ∧ y in s
  proof: ⟨@h _ _, and_imp.mpr mul_mem⟩

@[to_additive]

中文:
定理 mul_mem_iff
  条件: {x y : M}
  结论: x * y in s ↔ x in s ∧ y in s
  证明: ⟨@h _ _, and_imp.mpr mul_mem⟩

@[to_additive]

Depends on / 依赖: and_imp, and_imp.mpr, mul_mem
-/
theorem mul_mem_iff {x y : M} : x * y in s ↔ x in s ∧ y in s :=
  ⟨@h _ _, and_imp.mpr mul_mem⟩

@[to_additive]
/--
theorem `top` / 定理 `top`

English:
theorem top
  statement: MulSaturated (⊤ : Submonoid M)
  proof: fun _ _ _ => ⟨trivial, trivial⟩

include h₁ h₂ in
@[to_additive]

中文:
定理 top
  结论: MulSaturated (⊤ : 子幺半群 M)
  证明: fun _ _ _ => ⟨trivial, trivial⟩

include h₁ h₂ in
@[to_additive]
-/
theorem top : MulSaturated (⊤ : Submonoid M) := fun _ _ _ => ⟨trivial, trivial⟩

include h₁ h₂ in
@[to_additive]
/--
theorem `inf` / 定理 `inf`

English:
theorem inf
  statement: MulSaturated (s₁ ⊓ s₂)
  proof: fun _ _ hxy => ⟨⟨(h₁ hxy.1).1, (h₂ hxy.2).1⟩, (h₁ hxy.1).2, (h₂ hxy.2).2⟩

@[to_additive]

中文:
定理 下确界
  结论: MulSaturated (s₁ ⊓ s₂)
  证明: fun _ _ hxy => ⟨⟨(h₁ hxy.1).1, (h₂ hxy.2).1⟩, (h₁ hxy.1).2, (h₂ hxy.2).2⟩

@[to_additive]
-/
theorem inf : MulSaturated (s₁ ⊓ s₂) :=
  fun _ _ hxy => ⟨⟨(h₁ hxy.1).1, (h₂ hxy.2).1⟩, (h₁ hxy.1).2, (h₂ hxy.2).2⟩

@[to_additive]
/--
theorem `sInf` / 定理 `sInf`

English:
theorem sInf
  given: {f : Set (Submonoid M)} (hf : forall s in f, s.MulSaturated)
  proof: fun _ _ hxy => by
  simp_rw [mem_sInf] at hxy ⊢
  exact ⟨fun s hs => (hf s hs <| hxy s hs).1, fun s hs => (hf s hs <| hxy s hs).2⟩

@[to_additive]

中文:
定理 sInf
  条件: {f : 集合 (子幺半群 M)} (hf : 对任意 s in f, s.MulSaturated)
  证明: fun _ _ hxy => by
  simp_rw [mem_sInf] at hxy ⊢
  exact ⟨fun s hs => (hf s hs <| hxy s hs).1, fun s hs => (hf s hs <| hxy s hs).2⟩

@[to_additive]

Depends on / 依赖: mem_sInf, simp_rw
-/
theorem sInf {f : Set (Submonoid M)} (hf : forall s in f, s.MulSaturated) :
    (sInf f).MulSaturated := fun _ _ hxy => by
  simp_rw [mem_sInf] at hxy ⊢
  exact ⟨fun s hs => (hf s hs <| hxy s hs).1, fun s hs => (hf s hs <| hxy s hs).2⟩

@[to_additive]
/--
theorem `iInf` / 定理 `iInf`

English:
theorem iInf
  given: {ι : Sort*} {f : ι -> Submonoid M} (hf : forall i, (f i).MulSaturated)
  proof: sInf Set.forall_mem_range.mpr hf

中文:
定理 iInf
  条件: {ι : 类型层*} {f : ι -> 子幺半群 M} (hf : 对任意 i, (f i).MulSaturated)
  证明: sInf Set.forall_mem_range.mpr hf

Depends on / 依赖: Set.forall_mem_range.mpr, forall_mem_range
-/
theorem iInf {ι : Sort*} {f : ι -> Submonoid M} (hf : forall i, (f i).MulSaturated) :
    (iInf f).MulSaturated :=
sInf Set.forall_mem_range.mpr hf

/-- If `M` is commutative, we only need to check the left condition `x ∈ s`. -/
@[to_additive /-- If `M` is commutative, we only need to check the left condition `x ∈ s`. -/]
/--
theorem `of_left` / 定理 `of_left`

English:
theorem of_left
  statement: {M : Type*} [CommMonoid M] {s : Submonoid M}
  proof: fun x y hxy => ⟨h hxy, h mul_comm x y ▸ hxy⟩

中文:
定理 of_left
  结论: {M : 类型} [交换幺半群 M] {s : 子幺半群 M}
  证明: fun x y hxy => ⟨h hxy, h mul_comm x y ▸ hxy⟩

Depends on / 依赖: mul_comm
-/
theorem of_left {M : Type*} [CommMonoid M] {s : Submonoid M}
    (h : forall ⦃x y⦄, x * y in s -> x in s) : s.MulSaturated :=
fun x y hxy => ⟨h hxy, h mul_comm x y ▸ hxy⟩

/-- If `M` is commutative, we only need to check the right condition `y ∈ s`. -/
@[to_additive /-- If `M` is commutative, we only need to check the right condition `y ∈ s`. -/]
/--
theorem `of_right` / 定理 `of_right`

English:
theorem of_right
  statement: {M : Type*} [CommMonoid M] {s : Submonoid M}
  proof: of_left fun x y => mul_comm x y ▸ @h y x

中文:
定理 of_right
  结论: {M : 类型} [交换幺半群 M] {s : 子幺半群 M}
  证明: of_left fun x y => mul_comm x y ▸ @h y x

Depends on / 依赖: mul_comm, of_left
-/
theorem of_right {M : Type*} [CommMonoid M] {s : Submonoid M}
    (h : forall ⦃x y⦄, x * y in s -> y in s) : s.MulSaturated :=
  of_left fun x y => mul_comm x y ▸ @h y x

end MulSaturated

end Submonoid

-- automatic generation failed
/--
Definition of `SaturatedAddSubmonoid` / `SaturatedAddSubmonoid` 的定义

English:
structure SaturatedAddSubmonoid
  parameters: (M : Type*) [AddZeroClass M]
  extends: AddSubmonoid M
  axioms and operations (1):
    - addSaturated : toAddSubmonoid.AddSaturated

中文:
结构 SaturatedAdd子幺半群
  参数: (M : 类型) [加法零类 M]
  继承: 加法子幺半群 M
  公理与运算 (1 个):
    - addSaturated : toAddSubmonoid.AddSaturated
-/
structure SaturatedAddSubmonoid (M : Type*) [AddZeroClass M] extends AddSubmonoid M where
  addSaturated : toAddSubmonoid.AddSaturated

/--
Definition of `SaturatedSubmonoid` / `SaturatedSubmonoid` 的定义

English:
structure SaturatedSubmonoid
  parameters: (M : Type*) [MulOneClass M]
  extends: Submonoid M
  axioms and operations (1):
    - mulSaturated : toSubmonoid.MulSaturated

中文:
结构 饱和子幺半群
  参数: (M : 类型) [MulOne类 M]
  继承: 子幺半群 M
  公理与运算 (1 个):
    - mulSaturated : toSubmonoid.MulSaturated
-/
@[to_additive] structure SaturatedSubmonoid (M : Type*) [MulOneClass M] extends Submonoid M where
  mulSaturated : toSubmonoid.MulSaturated

namespace SaturatedSubmonoid
variable {M : Type*} [MulOneClass M]

attribute [simp] mulSaturated SaturatedAddSubmonoid.addSaturated

@[to_additive]
/--
theorem `toSubmonoid_injective` / 定理 `toSubmonoid_injective`

English:
theorem toSubmonoid_injective
  statement: (toSubmonoid (M := M)).Injective
  proof: fun ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ eq => by congr

@[to_additive (attr := ext)]

中文:
定理 toSubmonoid_injective
  结论: (toSubmonoid (M := M)).单射
  证明: fun ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ eq => by congr

@[to_additive (attr := ext)]

Depends on / 依赖: Injective
-/
theorem toSubmonoid_injective : (toSubmonoid (M := M)).Injective :=
  fun ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ eq => by congr

@[to_additive (attr := ext)]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {s₁ s₂ : SaturatedSubmonoid M} (h : s₁.toSubmonoid = s₂.toSubmonoid)
  statement: s₁ = s₂
  proof: toSubmonoid_injective h

中文:
引理 ext
  条件: {s₁ s₂ : 饱和子幺半群 M} (h : s₁.toSubmonoid = s₂.toSubmonoid)
  结论: s₁ = s₂
  证明: toSubmonoid_injective h

Depends on / 依赖: toSubmonoid_injective
-/
lemma ext {s₁ s₂ : SaturatedSubmonoid M} (h : s₁.toSubmonoid = s₂.toSubmonoid) : s₁ = s₂ :=
  toSubmonoid_injective h

variable (M) in
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (SaturatedSubmonoid M) M
  body: (·.carrier)
coe_injective _ _ h := toSubmonoid_injective SetLike.coe_injective h

@[to_additive]

中文:
实例 :
  签名: 集合状 (饱和子幺半群 M) M
  定义体: (·.carrier)
coe_injective _ _ h := toSubmonoid_injective SetLike.coe_injective h

@[to_additive]

Depends on / 依赖: carrier
-/
instance : SetLike (SaturatedSubmonoid M) M where
  coe := (·.carrier)
coe_injective _ _ h := toSubmonoid_injective SetLike.coe_injective h

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (SaturatedSubmonoid M)
  body: .ofSetLike ..

@[to_additive]

中文:
实例 :
  签名: 偏序 (饱和子幺半群 M)
  定义体: .ofSetLike ..

@[to_additive]

Depends on / 依赖: ofSetLike
-/
instance : PartialOrder (SaturatedSubmonoid M) := .ofSetLike ..

@[to_additive]
/--
lemma `ext'` / 引理 `ext'`

English:
lemma ext'
  given: {s₁ s₂ : SaturatedSubmonoid M} (h : forall x, x in s₁ ↔ x in s₂)
  statement: s₁ = s₂
  proof: SetLike.ext h

中文:
引理 ext'
  条件: {s₁ s₂ : 饱和子幺半群 M} (h : 对任意 x, x in s₁ ↔ x in s₂)
  结论: s₁ = s₂
  证明: SetLike.ext h

Depends on / 依赖: SetLike, SetLike.ext
-/
lemma ext' {s₁ s₂ : SaturatedSubmonoid M} (h : forall x, x in s₁ ↔ x in s₂) : s₁ = s₂ :=
  SetLike.ext h

variable (M) in
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SubmonoidClass (SaturatedSubmonoid M) M
  body: s.mul_mem
  one_mem {s} := s.one_mem

@[to_additive (attr := simp)]

中文:
实例 :
  签名: 子幺半群类 (饱和子幺半群 M) M
  定义体: s.mul_mem
  one_mem {s} := s.one_mem

@[to_additive (attr := simp)]

Depends on / 依赖: mul_mem, s.mul_mem
-/
instance : SubmonoidClass (SaturatedSubmonoid M) M where
  mul_mem {s} := s.mul_mem
  one_mem {s} := s.one_mem

@[to_additive (attr := simp)]
/--
lemma `mem_toSubmonoid` / 引理 `mem_toSubmonoid`

English:
lemma mem_toSubmonoid
  given: {s : SaturatedSubmonoid M} {x : M}
  statement: x in s.toSubmonoid ↔ x in s
  proof: Iff.rfl

@[to_additive]

中文:
引理 mem_toSubmonoid
  条件: {s : 饱和子幺半群 M} {x : M}
  结论: x in s.toSubmonoid ↔ x in s
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
lemma mem_toSubmonoid {s : SaturatedSubmonoid M} {x : M} : x in s.toSubmonoid ↔ x in s :=
  Iff.rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (SaturatedSubmonoid M)
  body: { (⊤ : Submonoid M) with mulSaturated := .top }

@[to_additive (attr := simp)]

中文:
实例 :
  签名: 顶元素 (饱和子幺半群 M)
  定义体: { (⊤ : Submonoid M) with mulSaturated := .top }

@[to_additive (attr := simp)]

Depends on / 依赖: Submonoid, mulSaturated
-/
instance : Top (SaturatedSubmonoid M) where
  top := { (⊤ : Submonoid M) with mulSaturated := .top }

@[to_additive (attr := simp)]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  given: {x : M}
  statement: x in (⊤ : SaturatedSubmonoid M)
  proof: trivial

中文:
定理 mem_top
  条件: {x : M}
  结论: x in (⊤ : 饱和子幺半群 M)
  证明: trivial
-/
theorem mem_top {x : M} : x in (⊤ : SaturatedSubmonoid M) := trivial

variable (M) in
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (SaturatedSubmonoid M)
  body: { s₁.toSubmonoid ⊓ s₂.toSubmonoid with mulSaturated := .inf s₁.2 s₂.2 }

中文:
实例 :
  签名: 最小值 (饱和子幺半群 M)
  定义体: { s₁.toSubmonoid ⊓ s₂.toSubmonoid with mulSaturated := .inf s₁.2 s₂.2 }

Depends on / 依赖: mulSaturated, toSubmonoid
-/
instance : Min (SaturatedSubmonoid M) where
  min s₁ s₂ := { s₁.toSubmonoid ⊓ s₂.toSubmonoid with mulSaturated := .inf s₁.2 s₂.2 }

variable (M) in
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (SaturatedSubmonoid M)
  body: { carrier := ⋂ s in f, s
    mul_mem' hx hy := by rw [Set.mem_iInter₂] at *; exact fun s hs => mul_mem (hx s hs) (hy s hs)
    one_mem' := Set.mem_iInter₂.mpr fun _ _ => one_mem _
    mulSaturated := by
      convert! Submonoid.MulSaturated.sInf (f := toSubmonoid '' f) (by simp)
      ext; simp [Submonoid.mem_sInf] }

@[to_additive]

中文:
实例 :
  签名: 下确界集 (饱和子幺半群 M)
  定义体: { carrier := ⋂ s in f, s
    mul_mem' hx hy := by rw [Set.mem_iInter₂] at *; exact fun s hs => mul_mem (hx s hs) (hy s hs)
    one_mem' := Set.mem_iInter₂.mpr fun _ _ => one_mem _
    mulSaturated := by
      convert! Submonoid.MulSaturated.sInf (f := toSubmonoid '' f) (by simp)
      ext; simp [Submonoid.mem_sInf] }

@[to_additive]

Depends on / 依赖: MulSaturated, Set.mem_iInter, Submonoid, Submonoid.MulSaturated.sInf, Submonoid.mem_sInf, carrier, convert, mem_sInf, mulSaturated, mul_mem, one_mem, toSubmonoid
-/
instance : InfSet (SaturatedSubmonoid M) where
  sInf f :=
  { carrier := ⋂ s in f, s
    mul_mem' hx hy := by rw [Set.mem_iInter₂] at *; exact fun s hs => mul_mem (hx s hs) (hy s hs)
    one_mem' := Set.mem_iInter₂.mpr fun _ _ => one_mem _
    mulSaturated := by
      convert! Submonoid.MulSaturated.sInf (f := toSubmonoid '' f) (by simp)
      ext; simp [Submonoid.mem_sInf] }

@[to_additive]
/--
theorem `mem_sInf` / 定理 `mem_sInf`

English:
theorem mem_sInf
  given: {f : Set (SaturatedSubmonoid M)} {x : M}
  statement: x in sInf f ↔ forall s in f, x in s
  proof: Set.mem_iInter₂

中文:
定理 mem_sInf
  条件: {f : 集合 (饱和子幺半群 M)} {x : M}
  结论: x in sInf f ↔ 对任意 s in f, x in s
  证明: Set.mem_iInter₂

Depends on / 依赖: Set.mem_iInter
-/
theorem mem_sInf {f : Set (SaturatedSubmonoid M)} {x : M} : x in sInf f ↔ forall s in f, x in s :=
  Set.mem_iInter₂

variable (M) in
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSemilatticeInf (SaturatedSubmonoid M)
  body: .of_image SetLike.coe_subset_coe isGLB_biInf

中文:
实例 :
  签名: 余mpleteSemilatticeInf (饱和子幺半群 M)
  定义体: .of_image SetLike.coe_subset_coe isGLB_biInf

Depends on / 依赖: SetLike, SetLike.coe_subset_coe, coe_subset_coe, isGLB_biInf, of_image
-/
instance : CompleteSemilatticeInf (SaturatedSubmonoid M) where
  isGLB_sInf _ := .of_image SetLike.coe_subset_coe isGLB_biInf

end SaturatedSubmonoid

namespace Submonoid

/-- The saturation of a submonoid `s` is the intersection of all saturated submonoids that contain
`s`.

If `M` is a commutative monoid, then this is `{x : M | ∃ y : M, x * y ∈ s}`. -/
@[to_additive
/-- The saturation of an additive submonoid `s` is the intersection of all saturated submonoids
that contain `s`.

If `M` is a commutative additive monoid, then this is `{x : M | ∃ y : M, x + y ∈ s}`. -/]
/--
Definition of `saturation` / `saturation` 的定义

English:
definition saturation
  signature: {M : Type*} [MulOneClass M] (s : Submonoid M)
  body: sInf {t | s <= t.toSubmonoid}

中文:
定义 saturation
  签名: {M : 类型} [MulOne类 M] (s : 子幺半群 M)
  定义体: sInf {t | s <= t.toSubmonoid}

Depends on / 依赖: t.toSubmonoid, toSubmonoid
-/
def saturation {M : Type*} [MulOneClass M] (s : Submonoid M) : SaturatedSubmonoid M :=
  sInf {t | s <= t.toSubmonoid}

variable {M : Type*}

section MulOneClass
variable [MulOneClass M]

variable (M) in
@[to_additive]
/--
theorem `gc_saturation` / 定理 `gc_saturation`

English:
theorem gc_saturation
  statement: GaloisConnection (saturation (M := M)) (·.toSubmonoid)
  proof: fun _ _ =>
⟨fun ih _ hx => ih SaturatedSubmonoid.mem_sInf.mpr fun _ ht => ht hx,
  fun ih _ hx => SaturatedSubmonoid.mem_sInf.mp hx _ ih⟩

中文:
定理 gc_saturation
  结论: GaloisConnection (saturation (M := M)) (·.toSubmonoid)
  证明: fun _ _ =>
⟨fun ih _ hx => ih SaturatedSubmonoid.mem_sInf.mpr fun _ ht => ht hx,
  fun ih _ hx => SaturatedSubmonoid.mem_sInf.mp hx _ ih⟩

Depends on / 依赖: toSubmonoid
-/
theorem gc_saturation : GaloisConnection (saturation (M := M)) (·.toSubmonoid) := fun _ _ =>
⟨fun ih _ hx => ih SaturatedSubmonoid.mem_sInf.mpr fun _ ht => ht hx,
  fun ih _ hx => SaturatedSubmonoid.mem_sInf.mp hx _ ih⟩

variable (M) in
/-- `saturation` forms a `GaloisInsertion` with the forgetful functor
`SaturatedSubmonoid.toSubmonoid`. -/
@[to_additive
/-- `saturation` forms a `GaloisInsertion` with the forgetful functor
`SaturatedAddSubmonoid.toAddSubmonoid`. -/]
/--
Definition of `giSaturation` / `giSaturation` 的定义

English:
definition giSaturation
  signature: : GaloisInsertion (saturation (M := M)) (·.toSubmonoid) where
  body: { s with mulSaturated := le_antisymm ((gc_saturation M).le_u_l s) hs ▸ by simp }
  gc := gc_saturation M
  le_l_u s := (gc_saturation M).le_u_l s.toSubmonoid
  choice_eq s h := le_antisymm ((gc_saturation M).le_u_l s) h

中文:
定义 giSaturation
  签名: : Galois嵌入 (saturation (M := M)) (·.toSubmonoid) where
  定义体: { s with mulSaturated := le_antisymm ((gc_saturation M).le_u_l s) hs ▸ by simp }
  gc := gc_saturation M
  le_l_u s := (gc_saturation M).le_u_l s.toSubmonoid
  choice_eq s h := le_antisymm ((gc_saturation M).le_u_l s) h

Depends on / 依赖: toSubmonoid
-/
def giSaturation : GaloisInsertion (saturation (M := M)) (·.toSubmonoid) where
  choice s hs := { s with mulSaturated := le_antisymm ((gc_saturation M).le_u_l s) hs ▸ by simp }
  gc := gc_saturation M
  le_l_u s := (gc_saturation M).le_u_l s.toSubmonoid
  choice_eq s h := le_antisymm ((gc_saturation M).le_u_l s) h

variable {a : Submonoid M} {b : SaturatedSubmonoid M}

@[to_additive]
/--
theorem `saturation_le_iff_le` / 定理 `saturation_le_iff_le`

English:
theorem saturation_le_iff_le
  statement: a.saturation <= b ↔ a <= b.toSubmonoid
  proof: gc_saturation ..

@[to_additive]
alias ⟨_, saturation_le_of_le⟩ := saturation_le_iff_le

@[to_additive]

中文:
定理 saturation_le_iff_le
  结论: a.saturation <= b ↔ a <= b.toSubmonoid
  证明: gc_saturation ..

@[to_additive]
alias ⟨_, saturation_le_of_le⟩ := saturation_le_iff_le

@[to_additive]

Depends on / 依赖: gc_saturation
-/
theorem saturation_le_iff_le : a.saturation <= b ↔ a <= b.toSubmonoid := gc_saturation ..

@[to_additive]
alias ⟨_, saturation_le_of_le⟩ := saturation_le_iff_le

@[to_additive]
/--
theorem `le_toSubmonoid_saturation` / 定理 `le_toSubmonoid_saturation`

English:
theorem le_toSubmonoid_saturation
  statement: a <= a.saturation.toSubmonoid
  proof: (gc_saturation M).le_u_l a

@[to_additive (attr := simp)]

中文:
定理 le_toSubmonoid_saturation
  结论: a <= a.saturation.toSubmonoid
  证明: (gc_saturation M).le_u_l a

@[to_additive (attr := simp)]

Depends on / 依赖: gc_saturation, le_u_l
-/
theorem le_toSubmonoid_saturation : a <= a.saturation.toSubmonoid := (gc_saturation M).le_u_l a

@[to_additive (attr := simp)]
/--
theorem `saturation_toSubmonoid` / 定理 `saturation_toSubmonoid`

English:
theorem saturation_toSubmonoid
  statement: b.saturation = b
  proof: (giSaturation M).l_u_eq b

@[to_additive (attr := elab_as_elim)]

中文:
定理 saturation_toSubmonoid
  结论: b.saturation = b
  证明: (giSaturation M).l_u_eq b

@[to_additive (attr := elab_as_elim)]

Depends on / 依赖: giSaturation, l_u_eq
-/
theorem saturation_toSubmonoid : b.saturation = b := (giSaturation M).l_u_eq b

@[to_additive (attr := elab_as_elim)]
/--
theorem `saturation_induction` / 定理 `saturation_induction`

English:
theorem saturation_induction
  statement: {s : Submonoid M}
  proof: by
  let s' : SaturatedSubmonoid M :=
  { carrier := { x | exists hx, p x hx }
one_mem' := ⟨_ , mem 1 one_mem s⟩
    mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, mul _ _ _ _ hpx hpy⟩
    mulSaturated := fun x y ⟨_, hpxy⟩ => ⟨⟨_, (of_mul _ _ _ hpxy).1⟩, ⟨_, (of_mul _ _ _ hpxy).2⟩⟩ }
.2 exact SaturatedSubmonoid.mem_sInf.mp hx s' (fun _ h => ⟨_, mem _ h⟩)

中文:
定理 saturation_induction
  结论: {s : 子幺半群 M}
  证明: by
  let s' : SaturatedSubmonoid M :=
  { carrier := { x | exists hx, p x hx }
one_mem' := ⟨_ , mem 1 one_mem s⟩
    mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, mul _ _ _ _ hpx hpy⟩
    mulSaturated := fun x y ⟨_, hpxy⟩ => ⟨⟨_, (of_mul _ _ _ hpxy).1⟩, ⟨_, (of_mul _ _ _ hpxy).2⟩⟩ }
.2 exact SaturatedSubmonoid.mem_sInf.mp hx s' (fun _ h => ⟨_, mem _ h⟩)

Depends on / 依赖: SaturatedSubmonoid, SaturatedSubmonoid.mem_sInf.mp, carrier, mem_sInf, mulSaturated, mul_mem, of_mul, one_mem
-/
theorem saturation_induction {s : Submonoid M}
    {p : (x : M) -> x in s.saturation -> Prop}
    (mem : forall (x) (hx : x in s), p x (le_toSubmonoid_saturation hx))
    (mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy))
    (of_mul : forall (x y) (hxy : x * y in s.saturation),
      p (x * y) hxy -> p x (s.saturation.2 hxy).1 ∧ p y (s.saturation.2 hxy).2)
    {x : M} (hx : x in s.saturation) : p x hx := by
  let s' : SaturatedSubmonoid M :=
  { carrier := { x | exists hx, p x hx }
one_mem' := ⟨_ , mem 1 one_mem s⟩
    mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, mul _ _ _ _ hpx hpy⟩
    mulSaturated := fun x y ⟨_, hpxy⟩ => ⟨⟨_, (of_mul _ _ _ hpxy).1⟩, ⟨_, (of_mul _ _ _ hpxy).2⟩⟩ }
.2 exact SaturatedSubmonoid.mem_sInf.mp hx s' (fun _ h => ⟨_, mem _ h⟩)

end MulOneClass

section CommMonoid
variable [CommMonoid M]

variable {s : Submonoid M} {x : M}

@[to_additive]
/--
theorem `mem_saturation_iff` / 定理 `mem_saturation_iff`

English:
theorem mem_saturation_iff
  statement: x in s.saturation ↔ exists y, x * y in s
  proof: by
  refine ⟨fun h => ?_, fun ⟨y, hxy⟩ => (s.saturation.2 <| le_toSubmonoid_saturation hxy).1⟩
  induction h using saturation_induction with
  | mem _ hx => exact ⟨1, by simpa⟩
  | mul _ _ _ _ ih₁ ih₂ =>
    exact ih₁.elim fun y₁ h₁ => ih₂.elim fun y₂ h₂ =>
      ⟨y₁ * y₂, by rw [mul_mul_mul_comm]; exact mul_mem h₁ h₂⟩
  | of_mul x₁ x₂ _ ih =>
    exact ih.elim fun y h => ⟨⟨x₂ * y, by rwa [← mul_assoc]⟩,
      ⟨x₁ * y, by rwa [mul_left_comm, ← mul_assoc]⟩⟩

@[to_additive]

中文:
定理 mem_saturation_iff
  结论: x in s.saturation ↔ 存在 y, x * y in s
  证明: by
  refine ⟨fun h => ?_, fun ⟨y, hxy⟩ => (s.saturation.2 <| le_toSubmonoid_saturation hxy).1⟩
  induction h using saturation_induction with
  | mem _ hx => exact ⟨1, by simpa⟩
  | mul _ _ _ _ ih₁ ih₂ =>
    exact ih₁.elim fun y₁ h₁ => ih₂.elim fun y₂ h₂ =>
      ⟨y₁ * y₂, by rw [mul_mul_mul_comm]; exact mul_mem h₁ h₂⟩
  | of_mul x₁ x₂ _ ih =>
    exact ih.elim fun y h => ⟨⟨x₂ * y, by rwa [← mul_assoc]⟩,
      ⟨x₁ * y, by rwa [mul_left_comm, ← mul_assoc]⟩⟩

@[to_additive]

Depends on / 依赖: ih.elim, le_toSubmonoid_saturation, mul_assoc, mul_left_comm, mul_mem, mul_mul_mul_comm, of_mul, s.saturation, saturation, saturation_induction
-/
theorem mem_saturation_iff : x in s.saturation ↔ exists y, x * y in s := by
  refine ⟨fun h => ?_, fun ⟨y, hxy⟩ => (s.saturation.2 <| le_toSubmonoid_saturation hxy).1⟩
  induction h using saturation_induction with
  | mem _ hx => exact ⟨1, by simpa⟩
  | mul _ _ _ _ ih₁ ih₂ =>
    exact ih₁.elim fun y₁ h₁ => ih₂.elim fun y₂ h₂ =>
      ⟨y₁ * y₂, by rw [mul_mul_mul_comm]; exact mul_mem h₁ h₂⟩
  | of_mul x₁ x₂ _ ih =>
    exact ih.elim fun y h => ⟨⟨x₂ * y, by rwa [← mul_assoc]⟩,
      ⟨x₁ * y, by rwa [mul_left_comm, ← mul_assoc]⟩⟩

@[to_additive]
/--
theorem `mem_saturation_iff'` / 定理 `mem_saturation_iff'`

English:
theorem mem_saturation_iff'
  statement: x in s.saturation ↔ exists y, y * x in s
  proof: by
  simp_rw [mem_saturation_iff, mul_comm x]

中文:
定理 mem_saturation_iff'
  结论: x in s.saturation ↔ 存在 y, y * x in s
  证明: by
  simp_rw [mem_saturation_iff, mul_comm x]

Depends on / 依赖: mem_saturation_iff, mul_comm, simp_rw
-/
theorem mem_saturation_iff' : x in s.saturation ↔ exists y, y * x in s := by
  simp_rw [mem_saturation_iff, mul_comm x]

/--
theorem `mem_saturation_iff_exists_dvd` / 定理 `mem_saturation_iff_exists_dvd`

English:
theorem mem_saturation_iff_exists_dvd
  statement: x in s.saturation ↔ exists m in s, x ∣ m
  proof: by
  simp_rw [dvd_def, existsAndEq, and_true, mem_saturation_iff]

中文:
定理 mem_saturation_iff_存在_dvd
  结论: x in s.saturation ↔ 存在 m in s, x ∣ m
  证明: by
  simp_rw [dvd_def, existsAndEq, and_true, mem_saturation_iff]

Depends on / 依赖: and_true, dvd_def, existsAndEq, mem_saturation_iff, simp_rw
-/
theorem mem_saturation_iff_exists_dvd : x in s.saturation ↔ exists m in s, x ∣ m := by
  simp_rw [dvd_def, existsAndEq, and_true, mem_saturation_iff]

end CommMonoid

end Submonoid

namespace SaturatedSubmonoid

@[to_additive]
instance (M : Type*) [MulOneClass M] :
    CompleteLattice (SaturatedSubmonoid M) :=
  { (inferInstance : PartialOrder (SaturatedSubmonoid M)),
    (inferInstance : Top (SaturatedSubmonoid M)),
    (inferInstance : Min (SaturatedSubmonoid M)),
    (inferInstance : CompleteSemilatticeInf (SaturatedSubmonoid M)),
    (Submonoid.giSaturation M).liftCompleteLattice with }

variable {M : Type*}

section MulOneClass
variable [MulOneClass M]

@[to_additive]
/--
theorem `bot_def` / 定理 `bot_def`

English:
theorem bot_def
  statement: (⊥ : SaturatedSubmonoid M) = Submonoid.saturation ⊥
  proof: rfl

@[to_additive]

中文:
定理 bot_def
  结论: (⊥ : 饱和子幺半群 M) = 子幺半群.saturation ⊥
  证明: rfl

@[to_additive]
-/
theorem bot_def : (⊥ : SaturatedSubmonoid M) = Submonoid.saturation ⊥ := rfl

@[to_additive]
/--
theorem `sup_def` / 定理 `sup_def`

English:
theorem sup_def
  given: {s₁ s₂ : SaturatedSubmonoid M}
  proof: rfl

@[to_additive]

中文:
定理 sup_def
  条件: {s₁ s₂ : 饱和子幺半群 M}
  证明: rfl

@[to_additive]
-/
theorem sup_def {s₁ s₂ : SaturatedSubmonoid M} :
    s₁ ⊔ s₂ = (s₁.toSubmonoid ⊔ s₂.toSubmonoid).saturation := rfl

@[to_additive]
/--
theorem `sSup_def` / 定理 `sSup_def`

English:
theorem sSup_def
  given: {f : Set (SaturatedSubmonoid M)}
  proof: rfl

@[to_additive]

中文:
定理 sSup_def
  条件: {f : 集合 (饱和子幺半群 M)}
  证明: rfl

@[to_additive]
-/
theorem sSup_def {f : Set (SaturatedSubmonoid M)} :
    sSup f = (sSup (toSubmonoid '' f)).saturation := rfl

@[to_additive]
/--
theorem `iSup_def` / 定理 `iSup_def`

English:
theorem iSup_def
  given: {ι : Sort*} {f : ι -> SaturatedSubmonoid M}
  proof: .symm (Submonoid.giSaturation M).l_iSup_u f

中文:
定理 iSup_def
  条件: {ι : 类型层*} {f : ι -> 饱和子幺半群 M}
  证明: .symm (Submonoid.giSaturation M).l_iSup_u f

Depends on / 依赖: Submonoid, Submonoid.giSaturation, giSaturation, l_iSup_u
-/
theorem iSup_def {ι : Sort*} {f : ι -> SaturatedSubmonoid M} :
    iSup f = (⨆ i, (f i).toSubmonoid).saturation :=
.symm (Submonoid.giSaturation M).l_iSup_u f

end MulOneClass

section CommMonoid
variable [CommMonoid M]

@[to_additive]
/--
theorem `mem_bot_iff` / 定理 `mem_bot_iff`

English:
theorem mem_bot_iff
  given: {x : M}
  statement: x in (⊥ : SaturatedSubmonoid M) ↔ IsUnit x
  proof: by
  simp_rw [bot_def, Submonoid.mem_saturation_iff, Submonoid.mem_bot, isUnit_iff_exists_inv]

中文:
定理 mem_bot_iff
  条件: {x : M}
  结论: x in (⊥ : 饱和子幺半群 M) ↔ 是单位 x
  证明: by
  simp_rw [bot_def, Submonoid.mem_saturation_iff, Submonoid.mem_bot, isUnit_iff_exists_inv]

Depends on / 依赖: Submonoid, Submonoid.mem_bot, Submonoid.mem_saturation_iff, bot_def, isUnit_iff_exists_inv, mem_bot, mem_saturation_iff, simp_rw
-/
theorem mem_bot_iff {x : M} : x in (⊥ : SaturatedSubmonoid M) ↔ IsUnit x := by
  simp_rw [bot_def, Submonoid.mem_saturation_iff, Submonoid.mem_bot, isUnit_iff_exists_inv]

end CommMonoid

end SaturatedSubmonoid

namespace Submonoid
variable {M : Type*} [MulOneClass M]

@[to_additive (attr := simp)]
/--
theorem `saturation_bot` / 定理 `saturation_bot`

English:
theorem saturation_bot
  statement: (⊥ : Submonoid M).saturation = ⊥
  proof: (gc_saturation M).l_bot

@[to_additive (attr := simp)]

中文:
定理 saturation_bot
  结论: (⊥ : 子幺半群 M).saturation = ⊥
  证明: (gc_saturation M).l_bot

@[to_additive (attr := simp)]

Depends on / 依赖: gc_saturation, l_bot
-/
theorem saturation_bot : (⊥ : Submonoid M).saturation = ⊥ := (gc_saturation M).l_bot

@[to_additive (attr := simp)]
/--
theorem `saturation_top` / 定理 `saturation_top`

English:
theorem saturation_top
  statement: (⊤ : Submonoid M).saturation = ⊤
  proof: (giSaturation M).l_top

@[to_additive (attr := simp)]

中文:
定理 saturation_top
  结论: (⊤ : 子幺半群 M).saturation = ⊤
  证明: (giSaturation M).l_top

@[to_additive (attr := simp)]

Depends on / 依赖: giSaturation, l_top
-/
theorem saturation_top : (⊤ : Submonoid M).saturation = ⊤ := (giSaturation M).l_top

@[to_additive (attr := simp)]
/--
theorem `saturation_sup` / 定理 `saturation_sup`

English:
theorem saturation_sup
  given: {s₁ s₂ : Submonoid M}
  proof: (gc_saturation M).l_sup

中文:
定理 saturation_sup
  条件: {s₁ s₂ : 子幺半群 M}
  证明: (gc_saturation M).l_sup

Depends on / 依赖: gc_saturation, l_sup
-/
theorem saturation_sup {s₁ s₂ : Submonoid M} :
    (s₁ ⊔ s₂).saturation = s₁.saturation ⊔ s₂.saturation := (gc_saturation M).l_sup

-- note that it does not preserve inf:
-- if s₁ = {6 ^ n | n : ℕ} and s₂ = {15 ^ n | n : ℕ} then
-- (s₁ ⊓ s₂).saturation = {1} and
-- s₁.saturation ⊓ s₂.saturation = {3 ^ n | n : ℕ}

@[to_additive (attr := simp)]
/--
theorem `saturation_sSup` / 定理 `saturation_sSup`

English:
theorem saturation_sSup
  given: {f : Set (Submonoid M)}
  proof: (gc_saturation M).l_sSup

@[to_additive (attr := simp)]

中文:
定理 saturation_sSup
  条件: {f : 集合 (子幺半群 M)}
  证明: (gc_saturation M).l_sSup

@[to_additive (attr := simp)]

Depends on / 依赖: gc_saturation, l_sSup
-/
theorem saturation_sSup {f : Set (Submonoid M)} :
    (sSup f).saturation = ⨆ s in f, s.saturation := (gc_saturation M).l_sSup

@[to_additive (attr := simp)]
/--
theorem `saturation_iSup` / 定理 `saturation_iSup`

English:
theorem saturation_iSup
  given: {ι : Sort*} {f : ι -> Submonoid M}
  proof: (gc_saturation M).l_iSup

中文:
定理 saturation_iSup
  条件: {ι : 类型层*} {f : ι -> 子幺半群 M}
  证明: (gc_saturation M).l_iSup

Depends on / 依赖: gc_saturation, l_iSup
-/
theorem saturation_iSup {ι : Sort*} {f : ι -> Submonoid M} :
    (iSup f).saturation = ⨆ i, (f i).saturation := (gc_saturation M).l_iSup

end Submonoid
