/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Algebra.Module.Submodule.Finsupp
public import Mathlib.Algebra.Ring.NonZeroDivisors
public import Mathlib.Algebra.Ring.Submonoid.Pointwise
public import Mathlib.Data.Set.Semiring
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Pointwise

/-!
# Multiplication and division of submodules of an algebra.

An interface for multiplication and division of sub-R-modules of an R-algebra A is developed.

## Main definitions

Let `R` be a commutative ring (or semiring) and let `A` be an `R`-algebra.

* `1 : Submodule R A` : the R-submodule R of the R-algebra A
* `Mul (Submodule R A)` : multiplication of two sub-R-modules M and N of A is defined to be
                              the smallest submodule containing all the products `m * n`.
* `Div (Submodule R A)` : `I / J` is defined to be the submodule consisting of all `a : A` such
                              that `a • J ⊆ I`

It is proved that `Submodule R A` is a semiring, and also an algebra over `Set A`.

Additionally, in the `Pointwise` scope we promote `Submodule.pointwiseDistribMulAction` to a
`MulSemiringAction` as `Submodule.pointwiseMulSemiringAction`.

When `R` is not necessarily commutative, and `A` is merely an `R`-module with a ring structure
such that `IsScalarTower R A A` holds (equivalent to the data of a ring homomorphism `R →+* A`
by `ringHomEquivModuleIsScalarTower`), we can still define `1 : Submodule R A` and
`Mul (Submodule R A)`, but `1` is only a left identity, not necessarily a right one.

## Tags

multiplication of submodules, division of submodules, submodule semiring
-/

@[expose] public section


universe uι u v

open Algebra Set MulOpposite

open scoped Pointwise

namespace SubMulAction

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]

/--
theorem `algebraMap_mem` / 定理 `algebraMap_mem`

English:
theorem algebraMap_mem
  given: (r : R)
  statement: algebraMap R A r in (1 : SubMulAction R A)
  proof: ⟨r, (algebraMap_eq_smul_one r).symm⟩

中文:
定理 algebraMap_mem
  条件: (r : R)
  结论: algebraMap R A r in (1 : SubMul作用 R A)
  证明: ⟨r, (algebraMap_eq_smul_one r).symm⟩

Depends on / 依赖: algebraMap_eq_smul_one
-/
theorem algebraMap_mem (r : R) : algebraMap R A r in (1 : SubMulAction R A) :=
  ⟨r, (algebraMap_eq_smul_one r).symm⟩

/--
theorem `mem_one'` / 定理 `mem_one'`

English:
theorem mem_one'
  given: {x : A}
  statement: x in (1 : SubMulAction R A) ↔ exists y, algebraMap R A y = x
  proof: exists_congr fun r => by rw [algebraMap_eq_smul_one]

中文:
定理 mem_one'
  条件: {x : A}
  结论: x in (1 : SubMul作用 R A) ↔ 存在 y, algebraMap R A y = x
  证明: exists_congr fun r => by rw [algebraMap_eq_smul_one]

Depends on / 依赖: algebraMap_eq_smul_one, exists_congr
-/
theorem mem_one' {x : A} : x in (1 : SubMulAction R A) ↔ exists y, algebraMap R A y = x :=
  exists_congr fun r => by rw [algebraMap_eq_smul_one]

end SubMulAction

namespace Submodule

section Module

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

-- TODO: Why is this in a file about `Algebra`?
-- TODO: potentially change this back to `LinearMap.range (Algebra.linearMap R A)`
-- once a version of `Algebra` without the `commutes'` field is introduced.
-- See issue https://github.com/leanprover-community/mathlib4/issues/18110.
/--
Instance `one` / 实例 `one`

English:
instance one
  signature: : One (Submodule R A)
  body: ⟨LinearMap.range (LinearMap.toSpanSingleton R A 1)⟩

中文:
实例 one
  签名: : 幺 (子模 R A)
  定义体: ⟨LinearMap.range (LinearMap.toSpanSingleton R A 1)⟩

Depends on / 依赖: LinearMap, LinearMap.range, LinearMap.toSpanSingleton, toSpanSingleton
-/
instance one : One (Submodule R A) :=
  ⟨LinearMap.range (LinearMap.toSpanSingleton R A 1)⟩

/--
theorem `one_eq_span` / 定理 `one_eq_span`

English:
theorem one_eq_span
  statement: (1 : Submodule R A) = R ∙ 1
  proof: (LinearMap.span_singleton_eq_range _ _ _).symm

中文:
定理 one_eq_span
  结论: (1 : 子模 R A) = R ∙ 1
  证明: (LinearMap.span_singleton_eq_range _ _ _).symm

Depends on / 依赖: LinearMap, LinearMap.span_singleton_eq_range, span_singleton_eq_range
-/
theorem one_eq_span : (1 : Submodule R A) = R ∙ 1 :=
  (LinearMap.span_singleton_eq_range _ _ _).symm

/--
theorem `le_one_toAddSubmonoid` / 定理 `le_one_toAddSubmonoid`

English:
theorem le_one_toAddSubmonoid
  statement: 1 <= (1 : Submodule R A).toAddSubmonoid
  proof: by
  rintro x ⟨n, rfl⟩
  exact ⟨n, show (n : R) • (1 : A) = n by rw [Nat.cast_smul_eq_nsmul, nsmul_one]⟩

@[simp]

中文:
定理 le_one_toAddSubmonoid
  结论: 1 <= (1 : 子模 R A).toAddSubmonoid
  证明: by
  rintro x ⟨n, rfl⟩
  exact ⟨n, show (n : R) • (1 : A) = n by rw [Nat.cast_smul_eq_nsmul, nsmul_one]⟩

@[simp]

Depends on / 依赖: Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul, nsmul_one
-/
theorem le_one_toAddSubmonoid : 1 <= (1 : Submodule R A).toAddSubmonoid := by
  rintro x ⟨n, rfl⟩
  exact ⟨n, show (n : R) • (1 : A) = n by rw [Nat.cast_smul_eq_nsmul, nsmul_one]⟩

@[simp]
/--
theorem `toSubMulAction_one` / 定理 `toSubMulAction_one`

English:
theorem toSubMulAction_one
  statement: (1 : Submodule R A).toSubMulAction = 1
  proof: SetLike.ext fun _ => by rw [one_eq_span, SubMulAction.mem_one]; exact mem_span_singleton

中文:
定理 toSubMulAction_one
  结论: (1 : 子模 R A).toSubMulAction = 1
  证明: SetLike.ext fun _ => by rw [one_eq_span, SubMulAction.mem_one]; exact mem_span_singleton

Depends on / 依赖: SetLike, SetLike.ext, SubMulAction, SubMulAction.mem_one, mem_one, mem_span_singleton, one_eq_span
-/
theorem toSubMulAction_one : (1 : Submodule R A).toSubMulAction = 1 :=
  SetLike.ext fun _ => by rw [one_eq_span, SubMulAction.mem_one]; exact mem_span_singleton

/--
theorem `one_eq_span_one_set` / 定理 `one_eq_span_one_set`

English:
theorem one_eq_span_one_set
  statement: (1 : Submodule R A) = span R 1
  proof: one_eq_span

@[simp]

中文:
定理 one_eq_span_one_set
  结论: (1 : 子模 R A) = span R 1
  证明: one_eq_span

@[simp]

Depends on / 依赖: one_eq_span
-/
theorem one_eq_span_one_set : (1 : Submodule R A) = span R 1 :=
  one_eq_span

@[simp]
/--
theorem `one_le` / 定理 `one_le`

English:
theorem one_le
  given: {P : Submodule R A}
  statement: (1 : Submodule R A) <= P ↔ (1 : A) in P
  proof: by
  simp [one_eq_span]

中文:
定理 one_le
  条件: {P : 子模 R A}
  结论: (1 : 子模 R A) <= P ↔ (1 : A) in P
  证明: by
  simp [one_eq_span]

Depends on / 依赖: one_eq_span
-/
theorem one_le {P : Submodule R A} : (1 : Submodule R A) <= P ↔ (1 : A) in P := by
  simp [one_eq_span]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoidWithOne (Submodule R A)
  body: sup_comm

中文:
实例 :
  签名: 加法交换带幺幺半群 (子模 R A)
  定义体: sup_comm

Depends on / 依赖: sup_comm
-/
instance : AddCommMonoidWithOne (Submodule R A) where
  add_comm := sup_comm

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul (Submodule R A) (Submodule R M)
  body: { __ := A'.toAddSubmonoid • M'.toAddSubmonoid
    smul_mem' := fun r m hm => AddSubmonoid.smul_induction_on hm
      (fun a ha m hm => by rw [← smul_assoc]; exact AddSubmonoid.smul_mem_smul (A'.smul_mem r ha) hm)
      fun m₁ m₂ h₁ h₂ => by rw [smul_add]; exact (A'.1 • M'.1).add_mem h₁ h₂ }

中文:
实例 :
  签名: 标量乘法 (子模 R A) (子模 R M)
  定义体: { __ := A'.toAddSubmonoid • M'.toAddSubmonoid
    smul_mem' := fun r m hm => AddSubmonoid.smul_induction_on hm
      (fun a ha m hm => by rw [← smul_assoc]; exact AddSubmonoid.smul_mem_smul (A'.smul_mem r ha) hm)
      fun m₁ m₂ h₁ h₂ => by rw [smul_add]; exact (A'.1 • M'.1).add_mem h₁ h₂ }

Depends on / 依赖: AddSubmonoid, AddSubmonoid.smul_induction_on, AddSubmonoid.smul_mem_smul, add_mem, smul_add, smul_assoc, smul_induction_on, smul_mem, smul_mem_smul, toAddSubmonoid
-/
instance : SMul (Submodule R A) (Submodule R M) where
  smul A' M' :=
  { __ := A'.toAddSubmonoid • M'.toAddSubmonoid
    smul_mem' := fun r m hm => AddSubmonoid.smul_induction_on hm
      (fun a ha m hm => by rw [← smul_assoc]; exact AddSubmonoid.smul_mem_smul (A'.smul_mem r ha) hm)
      fun m₁ m₂ h₁ h₂ => by rw [smul_add]; exact (A'.1 • M'.1).add_mem h₁ h₂ }

section

variable {I J : Submodule R A} {N P : Submodule R M}

/--
theorem `smul_toAddSubmonoid` / 定理 `smul_toAddSubmonoid`

English:
theorem smul_toAddSubmonoid
  statement: (I • N).toAddSubmonoid = I.toAddSubmonoid • N.toAddSubmonoid
  proof: rfl

中文:
定理 smul_toAddSubmonoid
  结论: (I • N).toAddSubmonoid = I.toAddSubmonoid • N.toAddSubmonoid
  证明: rfl
-/
theorem smul_toAddSubmonoid : (I • N).toAddSubmonoid = I.toAddSubmonoid • N.toAddSubmonoid := rfl

/--
theorem `smul_mem_smul` / 定理 `smul_mem_smul`

English:
theorem smul_mem_smul
  given: {r} {n} (hr : r in I) (hn : n in N)
  statement: r • n in I • N
  proof: AddSubmonoid.smul_mem_smul hr hn

中文:
定理 smul_mem_smul
  条件: {r} {n} (hr : r in I) (hn : n in N)
  结论: r • n in I • N
  证明: AddSubmonoid.smul_mem_smul hr hn

Depends on / 依赖: AddSubmonoid, AddSubmonoid.smul_mem_smul, smul_mem_smul
-/
theorem smul_mem_smul {r} {n} (hr : r in I) (hn : n in N) : r • n in I • N :=
  AddSubmonoid.smul_mem_smul hr hn

/--
theorem `smul_le` / 定理 `smul_le`

English:
theorem smul_le
  statement: I • N <= P ↔ forall r in I, forall n in N, r • n in P
  proof: AddSubmonoid.smul_le

@[simp, norm_cast]

中文:
定理 smul_le
  结论: I • N <= P ↔ 对任意 r in I, 对任意 n in N, r • n in P
  证明: AddSubmonoid.smul_le

@[simp, norm_cast]

Depends on / 依赖: AddSubmonoid, AddSubmonoid.smul_le, smul_le
-/
theorem smul_le : I • N <= P ↔ forall r in I, forall n in N, r • n in P :=
  AddSubmonoid.smul_le

@[simp, norm_cast]
/--
lemma `coe_set_smul` / 引理 `coe_set_smul`

English:
lemma coe_set_smul
  statement: (I : Set A) • N = I • N
  proof: set_smul_eq_of_le _ _ _
    (fun _ _ hr hx => smul_mem_smul hr hx)
    (smul_le.mpr fun _ hr _ hx => mem_set_smul_of_mem_mem hr hx)

@[elab_as_elim]

中文:
引理 coe_set_smul
  结论: (I : 集合 A) • N = I • N
  证明: set_smul_eq_of_le _ _ _
    (fun _ _ hr hx => smul_mem_smul hr hx)
    (smul_le.mpr fun _ hr _ hx => mem_set_smul_of_mem_mem hr hx)

@[elab_as_elim]

Depends on / 依赖: mem_set_smul_of_mem_mem, set_smul_eq_of_le, smul_le, smul_le.mpr, smul_mem_smul
-/
lemma coe_set_smul : (I : Set A) • N = I • N :=
  set_smul_eq_of_le _ _ _
    (fun _ _ hr hx => smul_mem_smul hr hx)
    (smul_le.mpr fun _ hr _ hx => mem_set_smul_of_mem_mem hr hx)

@[elab_as_elim]
/--
theorem `smul_induction_on` / 定理 `smul_induction_on`

English:
theorem smul_induction_on
  statement: {p : M -> Prop} {x} (H : x in I • N) (smul : forall r in I, forall n in N, p (r • n))
  proof: AddSubmonoid.smul_induction_on H smul add

中文:
定理 smul_induction_on
  结论: {p : M -> 命题} {x} (H : x in I • N) (smul : 对任意 r in I, 对任意 n in N, p (r • n))
  证明: AddSubmonoid.smul_induction_on H smul add

Depends on / 依赖: AddSubmonoid, AddSubmonoid.smul_induction_on, smul_induction_on
-/
theorem smul_induction_on {p : M -> Prop} {x} (H : x in I • N) (smul : forall r in I, forall n in N, p (r • n))
    (add : forall x y, p x -> p y -> p (x + y)) : p x :=
  AddSubmonoid.smul_induction_on H smul add

/-- Dependent version of `Submodule.smul_induction_on`. -/
@[elab_as_elim]
/--
theorem `smul_induction_on'` / 定理 `smul_induction_on'`

English:
theorem smul_induction_on'
  statement: {x : M} (hx : x in I • N) {p : forall x, x in I • N -> Prop}
  proof: by
  refine Exists.elim ?_ fun (h : x in I • N) (H : p x h) => H
  exact smul_induction_on hx (fun a ha x hx => ⟨_, smul _ ha _ hx⟩)
    fun x y ⟨_, hx⟩ ⟨_, hy⟩ => ⟨_, add _ _ _ _ hx hy⟩

中文:
定理 smul_induction_on'
  结论: {x : M} (hx : x in I • N) {p : 对任意 x, x in I • N -> 命题}
  证明: by
  refine Exists.elim ?_ fun (h : x in I • N) (H : p x h) => H
  exact smul_induction_on hx (fun a ha x hx => ⟨_, smul _ ha _ hx⟩)
    fun x y ⟨_, hx⟩ ⟨_, hy⟩ => ⟨_, add _ _ _ _ hx hy⟩

Depends on / 依赖: Exists, Exists.elim, smul_induction_on
-/
theorem smul_induction_on' {x : M} (hx : x in I • N) {p : forall x, x in I • N -> Prop}
    (smul : forall (r : A) (hr : r in I) (n : M) (hn : n in N), p (r • n) (smul_mem_smul hr hn))
    (add : forall x hx y hy, p x hx -> p y hy -> p (x + y) (add_mem ‹_› ‹_›)) : p x hx := by
  refine Exists.elim ?_ fun (h : x in I • N) (H : p x h) => H
  exact smul_induction_on hx (fun a ha x hx => ⟨_, smul _ ha _ hx⟩)
    fun x y ⟨_, hx⟩ ⟨_, hy⟩ => ⟨_, add _ _ _ _ hx hy⟩

/--
theorem `smul_mono` / 定理 `smul_mono`

English:
theorem smul_mono
  given: (hij : I <= J) (hnp : N <= P)
  statement: I • N <= J • P
  proof: AddSubmonoid.smul_le_smul hij hnp

中文:
定理 smul_mono
  条件: (hij : I <= J) (hnp : N <= P)
  结论: I • N <= J • P
  证明: AddSubmonoid.smul_le_smul hij hnp

Depends on / 依赖: AddSubmonoid, AddSubmonoid.smul_le_smul, smul_le_smul
-/
theorem smul_mono (hij : I <= J) (hnp : N <= P) : I • N <= J • P :=
  AddSubmonoid.smul_le_smul hij hnp

/--
theorem `smul_mono_left` / 定理 `smul_mono_left`

English:
theorem smul_mono_left
  given: (h : I <= J)
  statement: I • N <= J • N
  proof: smul_mono h le_rfl

中文:
定理 smul_mono_left
  条件: (h : I <= J)
  结论: I • N <= J • N
  证明: smul_mono h le_rfl

Depends on / 依赖: le_rfl, smul_mono
-/
theorem smul_mono_left (h : I <= J) : I • N <= J • N :=
  smul_mono h le_rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CovariantClass (Submodule R A) (Submodule R M) HSMul.hSMul LE.le
  body: ⟨fun _ _ => smul_mono le_rfl⟩

中文:
实例 :
  签名: 协变类 (子模 R A) (子模 R M) 异质标量乘法.hSMul LE.le
  定义体: ⟨fun _ _ => smul_mono le_rfl⟩

Depends on / 依赖: le_rfl, smul_mono
-/
instance : CovariantClass (Submodule R A) (Submodule R M) HSMul.hSMul LE.le :=
  ⟨fun _ _ => smul_mono le_rfl⟩

variable (I J N P)

@[simp]
/--
theorem `smul_bot` / 定理 `smul_bot`

English:
theorem smul_bot
  statement: I • (⊥ : Submodule R M) = ⊥
  proof: toAddSubmonoid_injective AddSubmonoid.addSubmonoid_smul_bot _

@[simp]

中文:
定理 smul_bot
  结论: I • (⊥ : 子模 R M) = ⊥
  证明: toAddSubmonoid_injective AddSubmonoid.addSubmonoid_smul_bot _

@[simp]

Depends on / 依赖: AddSubmonoid, AddSubmonoid.addSubmonoid_smul_bot, addSubmonoid_smul_bot, toAddSubmonoid_injective
-/
theorem smul_bot : I • (⊥ : Submodule R M) = ⊥ :=
toAddSubmonoid_injective AddSubmonoid.addSubmonoid_smul_bot _

@[simp]
/--
theorem `bot_smul` / 定理 `bot_smul`

English:
theorem bot_smul
  statement: (⊥ : Submodule R A) • N = ⊥
  proof: le_bot_iff.mp smul_le.mpr by rintro _ rfl _ _; rw [zero_smul]; exact zero_mem _

中文:
定理 bot_smul
  结论: (⊥ : 子模 R A) • N = ⊥
  证明: le_bot_iff.mp smul_le.mpr by rintro _ rfl _ _; rw [zero_smul]; exact zero_mem _

Depends on / 依赖: le_bot_iff, le_bot_iff.mp, smul_le, smul_le.mpr, zero_mem, zero_smul
-/
theorem bot_smul : (⊥ : Submodule R A) • N = ⊥ :=
le_bot_iff.mp smul_le.mpr by rintro _ rfl _ _; rw [zero_smul]; exact zero_mem _

/--
theorem `smul_sup` / 定理 `smul_sup`

English:
theorem smul_sup
  statement: I • (N ⊔ P) = I • N ⊔ I • P
  proof: toAddSubmonoid_injective by
    simp only [smul_toAddSubmonoid, sup_toAddSubmonoid, AddSubmonoid.addSubmonoid_smul_sup]

中文:
定理 smul_sup
  结论: I • (N ⊔ P) = I • N ⊔ I • P
  证明: toAddSubmonoid_injective by
    simp only [smul_toAddSubmonoid, sup_toAddSubmonoid, AddSubmonoid.addSubmonoid_smul_sup]

Depends on / 依赖: AddSubmonoid, AddSubmonoid.addSubmonoid_smul_sup, addSubmonoid_smul_sup, smul_toAddSubmonoid, sup_toAddSubmonoid, toAddSubmonoid_injective
-/
theorem smul_sup : I • (N ⊔ P) = I • N ⊔ I • P :=
toAddSubmonoid_injective by
    simp only [smul_toAddSubmonoid, sup_toAddSubmonoid, AddSubmonoid.addSubmonoid_smul_sup]

/--
theorem `sup_smul` / 定理 `sup_smul`

English:
theorem sup_smul
  statement: (I ⊔ J) • N = I • N ⊔ J • N
  proof: le_antisymm (smul_le.mpr fun mn hmn p hp => by
    obtain ⟨m, hm, n, hn, rfl⟩ := mem_sup.mp hmn
rw [add_smul]; exact add_mem_sup (smul_mem_smul hm hp) smul_mem_smul hn hp)
    (sup_le (smul_mono_left le_sup_left) <| smul_mono_left le_sup_right)

中文:
定理 sup_smul
  结论: (I ⊔ J) • N = I • N ⊔ J • N
  证明: le_antisymm (smul_le.mpr fun mn hmn p hp => by
    obtain ⟨m, hm, n, hn, rfl⟩ := mem_sup.mp hmn
rw [add_smul]; exact add_mem_sup (smul_mem_smul hm hp) smul_mem_smul hn hp)
    (sup_le (smul_mono_left le_sup_left) <| smul_mono_left le_sup_right)

Depends on / 依赖: add_mem_sup, add_smul, le_antisymm, le_sup_left, le_sup_right, mem_sup, mem_sup.mp, smul_le, smul_le.mpr, smul_mem_smul, smul_mono_left, sup_le
-/
theorem sup_smul : (I ⊔ J) • N = I • N ⊔ J • N :=
  le_antisymm (smul_le.mpr fun mn hmn p hp => by
    obtain ⟨m, hm, n, hn, rfl⟩ := mem_sup.mp hmn
rw [add_smul]; exact add_mem_sup (smul_mem_smul hm hp) smul_mem_smul hn hp)
    (sup_le (smul_mono_left le_sup_left) <| smul_mono_left le_sup_right)

/--
theorem `smul_assoc` / 定理 `smul_assoc`

English:
theorem smul_assoc
  statement: {B} [Semiring B] [Module R B] [Module A B] [Module B M]
  proof: le_antisymm
    (smul_le.2 fun _ hrsij t htn => smul_induction_on hrsij
      (fun r hr s hs => smul_assoc r s t ▸ smul_mem_smul hr (smul_mem_smul hs htn))
      fun x y => (add_smul x y t).symm ▸ add_mem)
    (smul_le.2 fun r hr _ hsn => smul_induction_on hsn
      (fun j hj n hn => (smul_assoc r j n).symm ▸ smul_mem_smul (smul_mem_smul hr hj) hn)
      fun m₁ m₂ => (smul_add r m₁ m₂) ▸ add_mem)

中文:
定理 smul_assoc
  结论: {B} [半环 B] [模 R B] [模 A B] [模 B M]
  证明: le_antisymm
    (smul_le.2 fun _ hrsij t htn => smul_induction_on hrsij
      (fun r hr s hs => smul_assoc r s t ▸ smul_mem_smul hr (smul_mem_smul hs htn))
      fun x y => (add_smul x y t).symm ▸ add_mem)
    (smul_le.2 fun r hr _ hsn => smul_induction_on hsn
      (fun j hj n hn => (smul_assoc r j n).symm ▸ smul_mem_smul (smul_mem_smul hr hj) hn)
      fun m₁ m₂ => (smul_add r m₁ m₂) ▸ add_mem)
-/
protected theorem smul_assoc {B} [Semiring B] [Module R B] [Module A B] [Module B M]
    [IsScalarTower R A B] [IsScalarTower R B M] [IsScalarTower A B M]
    (I : Submodule R A) (J : Submodule R B) (N : Submodule R M) :
    (I • J) • N = I • J • N :=
  le_antisymm
    (smul_le.2 fun _ hrsij t htn => smul_induction_on hrsij
      (fun r hr s hs => smul_assoc r s t ▸ smul_mem_smul hr (smul_mem_smul hs htn))
      fun x y => (add_smul x y t).symm ▸ add_mem)
    (smul_le.2 fun r hr _ hsn => smul_induction_on hsn
      (fun j hj n hn => (smul_assoc r j n).symm ▸ smul_mem_smul (smul_mem_smul hr hj) hn)
      fun m₁ m₂ => (smul_add r m₁ m₂) ▸ add_mem)

/--
theorem `smul_iSup` / 定理 `smul_iSup`

English:
theorem smul_iSup
  given: {ι : Sort*} {I : Submodule R A} {t : ι -> Submodule R M}
  proof: toAddSubmonoid_injective by
    simp only [smul_toAddSubmonoid, iSup_toAddSubmonoid, AddSubmonoid.smul_iSup]

中文:
定理 smul_iSup
  条件: {ι : 类型层*} {I : 子模 R A} {t : ι -> 子模 R M}
  证明: toAddSubmonoid_injective by
    simp only [smul_toAddSubmonoid, iSup_toAddSubmonoid, AddSubmonoid.smul_iSup]

Depends on / 依赖: AddSubmonoid, AddSubmonoid.smul_iSup, iSup_toAddSubmonoid, smul_iSup, smul_toAddSubmonoid, toAddSubmonoid_injective
-/
theorem smul_iSup {ι : Sort*} {I : Submodule R A} {t : ι -> Submodule R M} :
    I • (⨆ i, t i) = ⨆ i, I • t i :=
toAddSubmonoid_injective by
    simp only [smul_toAddSubmonoid, iSup_toAddSubmonoid, AddSubmonoid.smul_iSup]

/--
theorem `iSup_smul` / 定理 `iSup_smul`

English:
theorem iSup_smul
  given: {ι : Sort*} {t : ι -> Submodule R A} {N : Submodule R M}
  proof: le_antisymm (smul_le.mpr fun t ht s hs => iSup_induction _ (motive := (· • s in _)) ht
    (fun i t ht => mem_iSup_of_mem i <| smul_mem_smul ht hs)
    (by simp_rw [zero_smul]; apply zero_mem) fun x y => by simp_rw [add_smul]; apply add_mem)
    (iSup_le fun i => Submodule.smul_mono_left <| le_iSup _ i)

中文:
定理 iSup_smul
  条件: {ι : 类型层*} {t : ι -> 子模 R A} {N : 子模 R M}
  证明: le_antisymm (smul_le.mpr fun t ht s hs => iSup_induction _ (motive := (· • s in _)) ht
    (fun i t ht => mem_iSup_of_mem i <| smul_mem_smul ht hs)
    (by simp_rw [zero_smul]; apply zero_mem) fun x y => by simp_rw [add_smul]; apply add_mem)
    (iSup_le fun i => Submodule.smul_mono_left <| le_iSup _ i)

Depends on / 依赖: Submodule, Submodule.smul_mono_left, add_mem, add_smul, iSup_induction, iSup_le, le_antisymm, le_iSup, mem_iSup_of_mem, motive, simp_rw, smul_le, smul_le.mpr, smul_mem_smul, smul_mono_left, zero_mem, zero_smul
-/
theorem iSup_smul {ι : Sort*} {t : ι -> Submodule R A} {N : Submodule R M} :
    (⨆ i, t i) • N = ⨆ i, t i • N :=
  le_antisymm (smul_le.mpr fun t ht s hs => iSup_induction _ (motive := (· • s in _)) ht
    (fun i t ht => mem_iSup_of_mem i <| smul_mem_smul ht hs)
    (by simp_rw [zero_smul]; apply zero_mem) fun x y => by simp_rw [add_smul]; apply add_mem)
    (iSup_le fun i => Submodule.smul_mono_left <| le_iSup _ i)

/--
theorem `one_smul` / 定理 `one_smul`

English:
theorem one_smul
  statement: (1 : Submodule R A) • N = N
  proof: by
  refine le_antisymm (smul_le.mpr fun r hr m hm => ?_) fun m hm => ?_
  · obtain ⟨r, rfl⟩ := hr
    rw [LinearMap.toSpanSingleton_apply]; rw [smul_one_smul]; exact N.smul_mem r hm
  · rw [← one_smul A m]; exact smul_mem_smul (one_le.mp le_rfl) hm

中文:
定理 one_smul
  结论: (1 : 子模 R A) • N = N
  证明: by
  refine le_antisymm (smul_le.mpr fun r hr m hm => ?_) fun m hm => ?_
  · obtain ⟨r, rfl⟩ := hr
    rw [LinearMap.toSpanSingleton_apply]; rw [smul_one_smul]; exact N.smul_mem r hm
  · rw [← one_smul A m]; exact smul_mem_smul (one_le.mp le_rfl) hm
-/
protected theorem one_smul : (1 : Submodule R A) • N = N := by
  refine le_antisymm (smul_le.mpr fun r hr m hm => ?_) fun m hm => ?_
  · obtain ⟨r, rfl⟩ := hr
    rw [LinearMap.toSpanSingleton_apply]; rw [smul_one_smul]; exact N.smul_mem r hm
  · rw [← one_smul A m]; exact smul_mem_smul (one_le.mp le_rfl) hm

/--
theorem `smul_subset_smul` / 定理 `smul_subset_smul`

English:
theorem smul_subset_smul
  statement: (↑I : Set A) • (↑N : Set M) subseteq (↑(I • N) : Set M)
  proof: AddSubmonoid.smul_subset_smul

中文:
定理 smul_subset_smul
  结论: (↑I : 集合 A) • (↑N : 集合 M) subseteq (↑(I • N) : 集合 M)
  证明: AddSubmonoid.smul_subset_smul

Depends on / 依赖: AddSubmonoid, AddSubmonoid.smul_subset_smul, smul_subset_smul
-/
theorem smul_subset_smul : (↑I : Set A) • (↑N : Set M) subseteq (↑(I • N) : Set M) :=
  AddSubmonoid.smul_subset_smul

end

variable [IsScalarTower R A A]

/--
Instance `mul` / 实例 `mul`

English:
instance mul
  signature: : Mul (Submodule R A) where
  body: (· • ·)

中文:
实例 mul
  签名: : 乘法 (子模 R A) where
  定义体: (· • ·)
-/
instance mul : Mul (Submodule R A) where
  mul := (· • ·)

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

/--
theorem `mul_mem_mul` / 定理 `mul_mem_mul`

English:
theorem mul_mem_mul
  given: (hm : m in M) (hn : n in N)
  statement: m * n in M * N
  proof: smul_mem_smul hm hn

中文:
定理 mul_mem_mul
  条件: (hm : m in M) (hn : n in N)
  结论: m * n in M * N
  证明: smul_mem_smul hm hn

Depends on / 依赖: smul_mem_smul
-/
theorem mul_mem_mul (hm : m in M) (hn : n in N) : m * n in M * N :=
  smul_mem_smul hm hn

/--
theorem `mul_le` / 定理 `mul_le`

English:
theorem mul_le
  statement: M * N <= P ↔ forall m in M, forall n in N, m * n in P
  proof: smul_le

中文:
定理 mul_le
  结论: M * N <= P ↔ 对任意 m in M, 对任意 n in N, m * n in P
  证明: smul_le

Depends on / 依赖: smul_le
-/
theorem mul_le : M * N <= P ↔ forall m in M, forall n in N, m * n in P :=
  smul_le

/--
theorem `mul_toAddSubmonoid` / 定理 `mul_toAddSubmonoid`

English:
theorem mul_toAddSubmonoid
  given: (M N : Submodule R A)
  proof: rfl

@[elab_as_elim]

中文:
定理 mul_toAddSubmonoid
  条件: (M N : 子模 R A)
  证明: rfl

@[elab_as_elim]
-/
theorem mul_toAddSubmonoid (M N : Submodule R A) :
    (M * N).toAddSubmonoid = M.toAddSubmonoid * N.toAddSubmonoid := rfl

@[elab_as_elim]
/--
theorem `mul_induction_on` / 定理 `mul_induction_on`

English:
theorem mul_induction_on
  statement: {C : A -> Prop} {r : A} (hr : r in M * N)
  proof: smul_induction_on hr hm ha

中文:
定理 mul_induction_on
  结论: {C : A -> 命题} {r : A} (hr : r in M * N)
  证明: smul_induction_on hr hm ha

Depends on / 依赖: RingQuot, RingQuot.instCommSemiring, RingQuot.instRing, instCommSemiring, instRing
-/
protected theorem mul_induction_on {C : A -> Prop} {r : A} (hr : r in M * N)
    (hm : forall m in M, forall n in N, C (m * n)) (ha : forall x y, C x -> C y -> C (x + y)) : C r :=
  smul_induction_on hr hm ha

/-- A dependent version of `mul_induction_on`. -/
@[elab_as_elim]
/--
theorem `mul_induction_on'` / 定理 `mul_induction_on'`

English:
theorem mul_induction_on'
  statement: {C : forall r, r in M * N -> Prop}
  proof: smul_induction_on' hr mem_mul_mem add

中文:
定理 mul_induction_on'
  结论: {C : 对任意 r, r in M * N -> 命题}
  证明: smul_induction_on' hr mem_mul_mem add
-/
protected theorem mul_induction_on' {C : forall r, r in M * N -> Prop}
    (mem_mul_mem : forall m (hm : m in M) n (hn : n in N), C (m * n) (mul_mem_mul hm hn))
    (add : forall x hx y hy, C x hx -> C y hy -> C (x + y) (add_mem hx hy)) {r : A} (hr : r in M * N) :
    C r hr :=
  smul_induction_on' hr mem_mul_mem add

variable (M)

@[simp]
/--
theorem `mul_bot` / 定理 `mul_bot`

English:
theorem mul_bot
  statement: M * ⊥ = ⊥
  proof: smul_bot _

@[simp]

中文:
定理 mul_bot
  结论: M * ⊥ = ⊥
  证明: smul_bot _

@[simp]

Depends on / 依赖: smul_bot
-/
theorem mul_bot : M * ⊥ = ⊥ :=
  smul_bot _

@[simp]
/--
theorem `bot_mul` / 定理 `bot_mul`

English:
theorem bot_mul
  statement: ⊥ * M = ⊥
  proof: bot_smul _

@[simp]

中文:
定理 bot_mul
  结论: ⊥ * M = ⊥
  证明: bot_smul _

@[simp]

Depends on / 依赖: bot_smul
-/
theorem bot_mul : ⊥ * M = ⊥ :=
  bot_smul _

@[simp]
/--
theorem `mul_eq_bot` / 定理 `mul_eq_bot`

English:
theorem mul_eq_bot
  given: [NoZeroDivisors A] {M N : Submodule R A}
  proof: ⟨fun hmn =>
    or_iff_not_imp_left.mpr fun M_ne_bot =>
      N.eq_bot_iff.mpr fun n hn =>
        let ⟨m, hm, ne0⟩ := M.ne_bot_iff.mp M_ne_bot
        Or.resolve_left (mul_eq_zero.mp ((M * N).eq_bot_iff.mp hmn _ (mul_mem_mul hm hn))) ne0,
    fun h => by obtain rfl | rfl := h; exacts [bot_mul _, mul_bot _]⟩

中文:
定理 mul_eq_bot
  条件: [无零因子 A] {M N : 子模 R A}
  证明: ⟨fun hmn =>
    or_iff_not_imp_left.mpr fun M_ne_bot =>
      N.eq_bot_iff.mpr fun n hn =>
        let ⟨m, hm, ne0⟩ := M.ne_bot_iff.mp M_ne_bot
        Or.resolve_left (mul_eq_zero.mp ((M * N).eq_bot_iff.mp hmn _ (mul_mem_mul hm hn))) ne0,
    fun h => by obtain rfl | rfl := h; exacts [bot_mul _, mul_bot _]⟩

Depends on / 依赖: M.ne_bot_iff.mp, M_ne_bot, N.eq_bot_iff.mpr, Or.resolve_left, bot_mul, eq_bot_iff, eq_bot_iff.mp, exacts, mul_bot, mul_eq_zero, mul_eq_zero.mp, mul_mem_mul, ne_bot_iff, or_iff_not_imp_left, or_iff_not_imp_left.mpr, resolve_left
-/
theorem mul_eq_bot [NoZeroDivisors A] {M N : Submodule R A} :
    M * N = ⊥ ↔ M = ⊥ ∨ N = ⊥ :=
  ⟨fun hmn =>
    or_iff_not_imp_left.mpr fun M_ne_bot =>
      N.eq_bot_iff.mpr fun n hn =>
        let ⟨m, hm, ne0⟩ := M.ne_bot_iff.mp M_ne_bot
        Or.resolve_left (mul_eq_zero.mp ((M * N).eq_bot_iff.mp hmn _ (mul_mem_mul hm hn))) ne0,
    fun h => by obtain rfl | rfl := h; exacts [bot_mul _, mul_bot _]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NoZeroDivisors
  signature: A] : NoZeroDivisors (Submodule R A) where
  body: mul_eq_bot.1

中文:
实例 [无零因子
  签名: A] : 无零因子 (子模 R A) where
  定义体: mul_eq_bot.1

Depends on / 依赖: mul_eq_bot
-/
instance [NoZeroDivisors A] : NoZeroDivisors (Submodule R A) where
  eq_zero_or_eq_zero_of_mul_eq_zero := mul_eq_bot.1

/--
theorem `one_mul` / 定理 `one_mul`

English:
theorem one_mul
  statement: (1 : Submodule R A) * M = M
  proof: Submodule.one_smul _

中文:
定理 one_mul
  结论: (1 : 子模 R A) * M = M
  证明: Submodule.one_smul _
-/
protected theorem one_mul : (1 : Submodule R A) * M = M :=
  Submodule.one_smul _

variable {M}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulLeftMono (Submodule R A)
  body: smul_mono_right _ hNP

中文:
实例 :
  签名: MulLeftMono (子模 R A)
  定义体: smul_mono_right _ hNP

Depends on / 依赖: smul_mono_right
-/
instance : MulLeftMono (Submodule R A) where
  elim _M _N _P hNP := smul_mono_right _ hNP

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulRightMono (Submodule R A)
  body: smul_mono_left

中文:
实例 :
  签名: MulRightMono (子模 R A)
  定义体: smul_mono_left

Depends on / 依赖: smul_mono_left
-/
instance : MulRightMono (Submodule R A) where
  elim _ _ _ := smul_mono_left

/--
theorem `mul_comm_of_commute` / 定理 `mul_comm_of_commute`

English:
theorem mul_comm_of_commute
  given: (h : forall m in M, forall n in N, Commute m n)
  statement: M * N = N * M
  proof: toAddSubmonoid_injective AddSubmonoid.mul_comm_of_commute h

中文:
定理 mul_comm_of_commute
  条件: (h : 对任意 m in M, 对任意 n in N, Commute m n)
  结论: M * N = N * M
  证明: toAddSubmonoid_injective AddSubmonoid.mul_comm_of_commute h

Depends on / 依赖: AddSubmonoid, AddSubmonoid.mul_comm_of_commute, mul_comm_of_commute, toAddSubmonoid_injective
-/
theorem mul_comm_of_commute (h : forall m in M, forall n in N, Commute m n) : M * N = N * M :=
toAddSubmonoid_injective AddSubmonoid.mul_comm_of_commute h

variable (M N P)

/--
theorem `mul_sup` / 定理 `mul_sup`

English:
theorem mul_sup
  statement: M * (N ⊔ P) = M * N ⊔ M * P
  proof: smul_sup _ _ _

中文:
定理 mul_sup
  结论: M * (N ⊔ P) = M * N ⊔ M * P
  证明: smul_sup _ _ _

Depends on / 依赖: smul_sup
-/
theorem mul_sup : M * (N ⊔ P) = M * N ⊔ M * P :=
  smul_sup _ _ _

/--
theorem `sup_mul` / 定理 `sup_mul`

English:
theorem sup_mul
  statement: (M ⊔ N) * P = M * P ⊔ N * P
  proof: sup_smul _ _ _

中文:
定理 sup_mul
  结论: (M ⊔ N) * P = M * P ⊔ N * P
  证明: sup_smul _ _ _

Depends on / 依赖: sup_smul
-/
theorem sup_mul : (M ⊔ N) * P = M * P ⊔ N * P :=
  sup_smul _ _ _

/--
theorem `mul_subset_mul` / 定理 `mul_subset_mul`

English:
theorem mul_subset_mul
  statement: (↑M : Set A) * (↑N : Set A) subseteq (↑(M * N) : Set A)
  proof: smul_subset_smul _ _

中文:
定理 mul_subset_mul
  结论: (↑M : 集合 A) * (↑N : 集合 A) subseteq (↑(M * N) : 集合 A)
  证明: smul_subset_smul _ _

Depends on / 依赖: smul_subset_smul
-/
theorem mul_subset_mul : (↑M : Set A) * (↑N : Set A) subseteq (↑(M * N) : Set A) :=
  smul_subset_smul _ _

/--
lemma `restrictScalars_mul` / 引理 `restrictScalars_mul`

English:
lemma restrictScalars_mul
  statement: {A B C} [Semiring A] [Semiring B] [Semiring C]
  proof: rfl

中文:
引理 restrictScalars_mul
  结论: {A B C} [半环 A] [半环 B] [半环 C]
  证明: rfl
-/
lemma restrictScalars_mul {A B C} [Semiring A] [Semiring B] [Semiring C]
    [SMul A B] [Module A C] [Module B C] [IsScalarTower A C C] [IsScalarTower B C C]
    [IsScalarTower A B C] {I J : Submodule B C} :
    (I * J).restrictScalars A = I.restrictScalars A * J.restrictScalars A :=
  rfl

variable {ι : Sort uι}

/--
theorem `iSup_mul` / 定理 `iSup_mul`

English:
theorem iSup_mul
  given: (s : ι -> Submodule R A) (t : Submodule R A)
  statement: (⨆ i, s i) * t = ⨆ i, s i * t
  proof: iSup_smul

中文:
定理 iSup_mul
  条件: (s : ι -> 子模 R A) (t : 子模 R A)
  结论: (⨆ i, s i) * t = ⨆ i, s i * t
  证明: iSup_smul

Depends on / 依赖: iSup_smul
-/
theorem iSup_mul (s : ι -> Submodule R A) (t : Submodule R A) : (⨆ i, s i) * t = ⨆ i, s i * t :=
  iSup_smul

/--
theorem `mul_iSup` / 定理 `mul_iSup`

English:
theorem mul_iSup
  given: (t : Submodule R A) (s : ι -> Submodule R A)
  statement: (t * ⨆ i, s i) = ⨆ i, t * s i
  proof: smul_iSup

中文:
定理 mul_iSup
  条件: (t : 子模 R A) (s : ι -> 子模 R A)
  结论: (t * ⨆ i, s i) = ⨆ i, t * s i
  证明: smul_iSup

Depends on / 依赖: smul_iSup
-/
theorem mul_iSup (t : Submodule R A) (s : ι -> Submodule R A) : (t * ⨆ i, s i) = ⨆ i, t * s i :=
  smul_iSup

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NonUnitalSemiring (Submodule R A)
  body: toAddSubmonoid_injective.semigroup _ mul_toAddSubmonoid
  zero_mul := bot_mul
  mul_zero := mul_bot
  left_distrib := mul_sup
  right_distrib := sup_mul

中文:
实例 :
  签名: 非幺半环 (子模 R A)
  定义体: toAddSubmonoid_injective.semigroup _ mul_toAddSubmonoid
  zero_mul := bot_mul
  mul_zero := mul_bot
  left_distrib := mul_sup
  right_distrib := sup_mul

Depends on / 依赖: mul_toAddSubmonoid, semigroup, toAddSubmonoid_injective, toAddSubmonoid_injective.semigroup
-/
instance : NonUnitalSemiring (Submodule R A) where
  __ := toAddSubmonoid_injective.semigroup _ mul_toAddSubmonoid
  zero_mul := bot_mul
  mul_zero := mul_bot
  left_distrib := mul_sup
  right_distrib := sup_mul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (Submodule R A) Nat
  body: npowRec n s

中文:
实例 :
  签名: 幂 (子模 R A) 自然数
  定义体: npowRec n s

Depends on / 依赖: npowRec
-/
instance : Pow (Submodule R A) Nat where
  pow s n := npowRec n s

/--
theorem `mul_top_eq_top_of_mul_eq_one` / 定理 `mul_top_eq_top_of_mul_eq_one`

English:
theorem mul_top_eq_top_of_mul_eq_one
  given: (h : N * P = 1)
  statement: N * ⊤ = ⊤
  proof: top_unique by
    conv_lhs => rw [← Submodule.one_mul ⊤, ← h, mul_assoc]
    exact smul_mono le_rfl le_top

中文:
定理 mul_top_eq_top_of_mul_eq_one
  条件: (h : N * P = 1)
  结论: N * ⊤ = ⊤
  证明: top_unique by
    conv_lhs => rw [← Submodule.one_mul ⊤, ← h, mul_assoc]
    exact smul_mono le_rfl le_top

Depends on / 依赖: Submodule, Submodule.one_mul, conv_lhs, le_rfl, le_top, mul_assoc, one_mul, smul_mono, top_unique
-/
theorem mul_top_eq_top_of_mul_eq_one (h : N * P = 1) : N * ⊤ = ⊤ :=
top_unique by
    conv_lhs => rw [← Submodule.one_mul ⊤, ← h, mul_assoc]
    exact smul_mono le_rfl le_top

/--
theorem `pow_eq_npowRec` / 定理 `pow_eq_npowRec`

English:
theorem pow_eq_npowRec
  given: {n : Nat}
  statement: M ^ n = npowRec n M
  proof: rfl

中文:
定理 pow_eq_npowRec
  条件: {n : 自然数}
  结论: M ^ n = npowRec n M
  证明: rfl
-/
theorem pow_eq_npowRec {n : Nat} : M ^ n = npowRec n M := rfl

/--
theorem `pow_zero` / 定理 `pow_zero`

English:
theorem pow_zero
  statement: M ^ 0 = 1
  proof: rfl

中文:
定理 pow_zero
  结论: M ^ 0 = 1
  证明: rfl
-/
protected theorem pow_zero : M ^ 0 = 1 := rfl

/--
theorem `pow_succ` / 定理 `pow_succ`

English:
theorem pow_succ
  given: {n : Nat}
  statement: M ^ (n + 1) = M ^ n * M
  proof: rfl

中文:
定理 pow_succ
  条件: {n : 自然数}
  结论: M ^ (n + 1) = M ^ n * M
  证明: rfl
-/
protected theorem pow_succ {n : Nat} : M ^ (n + 1) = M ^ n * M := rfl

/--
theorem `pow_add` / 定理 `pow_add`

English:
theorem pow_add
  given: {m n : Nat} (h : n != 0)
  statement: M ^ (m + n) = M ^ m * M ^ n
  proof: npowRec_add m n h _ M.one_mul

中文:
定理 pow_add
  条件: {m n : 自然数} (h : n != 0)
  结论: M ^ (m + n) = M ^ m * M ^ n
  证明: npowRec_add m n h _ M.one_mul
-/
protected theorem pow_add {m n : Nat} (h : n != 0) : M ^ (m + n) = M ^ m * M ^ n :=
  npowRec_add m n h _ M.one_mul

/--
theorem `pow_one` / 定理 `pow_one`

English:
theorem pow_one
  statement: M ^ 1 = M
  proof: by
  rw [Submodule.pow_succ]; rw [Submodule.pow_zero]; rw [Submodule.one_mul]

中文:
定理 pow_one
  结论: M ^ 1 = M
  证明: by
  rw [Submodule.pow_succ]; rw [Submodule.pow_zero]; rw [Submodule.one_mul]
-/
protected theorem pow_one : M ^ 1 = M := by
  rw [Submodule.pow_succ]; rw [Submodule.pow_zero]; rw [Submodule.one_mul]

/--
theorem `pow_succ'` / 定理 `pow_succ'`

English:
theorem pow_succ'
  given: {n : Nat} (h : n != 0)
  statement: M ^ (n + 1) = M * M ^ n
  proof: by
  rw [add_comm]; rw [M.pow_add h]; rw [Submodule.pow_one]

@[simp]

中文:
定理 pow_succ'
  条件: {n : 自然数} (h : n != 0)
  结论: M ^ (n + 1) = M * M ^ n
  证明: by
  rw [add_comm]; rw [M.pow_add h]; rw [Submodule.pow_one]

@[simp]
-/
protected theorem pow_succ' {n : Nat} (h : n != 0) : M ^ (n + 1) = M * M ^ n := by
  rw [add_comm]; rw [M.pow_add h]; rw [Submodule.pow_one]

@[simp]
/--
theorem `bot_pow` / 定理 `bot_pow`

English:
theorem bot_pow
  statement: forall {n : Nat}, n != 0 -> (⊥ : Submodule R A) ^ n = ⊥

中文:
定理 bot_pow
  结论: 对任意 {n : 自然数}, n != 0 -> (⊥ : 子模 R A) ^ n = ⊥
-/
theorem bot_pow : forall {n : Nat}, n != 0 -> (⊥ : Submodule R A) ^ n = ⊥
  | 1, _ => Submodule.pow_one _
  | n + 2, _ => by rw [Submodule.pow_succ, bot_pow n.succ_ne_zero, bot_mul]

/--
theorem `pow_toAddSubmonoid` / 定理 `pow_toAddSubmonoid`

English:
theorem pow_toAddSubmonoid
  given: {n : Nat} (h : n != 0)
  statement: (M ^ n).toAddSubmonoid = M.toAddSubmonoid ^ n
  proof: by
  induction n with
  | zero => exact (h rfl).elim
  | succ n ih =>
    rw [Submodule.pow_succ]; rw [pow_succ]; rw [mul_toAddSubmonoid]
    cases n with
    | zero => rw [Submodule.pow_zero, pow_zero, one_mul, ← mul_toAddSubmonoid, Submodule.one_mul]
    | succ n => rw [ih n.succ_ne_zero]

中文:
定理 pow_toAddSubmonoid
  条件: {n : 自然数} (h : n != 0)
  结论: (M ^ n).toAddSubmonoid = M.toAddSubmonoid ^ n
  证明: by
  induction n with
  | zero => exact (h rfl).elim
  | succ n ih =>
    rw [Submodule.pow_succ]; rw [pow_succ]; rw [mul_toAddSubmonoid]
    cases n with
    | zero => rw [Submodule.pow_zero, pow_zero, one_mul, ← mul_toAddSubmonoid, Submodule.one_mul]
    | succ n => rw [ih n.succ_ne_zero]

Depends on / 依赖: Submodule, Submodule.one_mul, Submodule.pow_succ, Submodule.pow_zero, mul_toAddSubmonoid, n.succ_ne_zero, one_mul, pow_succ, pow_zero, succ_ne_zero
-/
theorem pow_toAddSubmonoid {n : Nat} (h : n != 0) : (M ^ n).toAddSubmonoid = M.toAddSubmonoid ^ n := by
  induction n with
  | zero => exact (h rfl).elim
  | succ n ih =>
    rw [Submodule.pow_succ]; rw [pow_succ]; rw [mul_toAddSubmonoid]
    cases n with
    | zero => rw [Submodule.pow_zero, pow_zero, one_mul, ← mul_toAddSubmonoid, Submodule.one_mul]
    | succ n => rw [ih n.succ_ne_zero]

/--
theorem `le_pow_toAddSubmonoid` / 定理 `le_pow_toAddSubmonoid`

English:
theorem le_pow_toAddSubmonoid
  given: {n : Nat}
  statement: M.toAddSubmonoid ^ n <= (M ^ n).toAddSubmonoid
  proof: by
  obtain rfl | hn := Decidable.eq_or_ne n 0
  · rw [Submodule.pow_zero, pow_zero]
    exact le_one_toAddSubmonoid
  · exact (pow_toAddSubmonoid M hn).ge

中文:
定理 le_pow_toAddSubmonoid
  条件: {n : 自然数}
  结论: M.toAddSubmonoid ^ n <= (M ^ n).toAddSubmonoid
  证明: by
  obtain rfl | hn := Decidable.eq_or_ne n 0
  · rw [Submodule.pow_zero, pow_zero]
    exact le_one_toAddSubmonoid
  · exact (pow_toAddSubmonoid M hn).ge

Depends on / 依赖: Decidable, Decidable.eq_or_ne, Submodule, Submodule.pow_zero, eq_or_ne, le_one_toAddSubmonoid, pow_toAddSubmonoid, pow_zero
-/
theorem le_pow_toAddSubmonoid {n : Nat} : M.toAddSubmonoid ^ n <= (M ^ n).toAddSubmonoid := by
  obtain rfl | hn := Decidable.eq_or_ne n 0
  · rw [Submodule.pow_zero, pow_zero]
    exact le_one_toAddSubmonoid
  · exact (pow_toAddSubmonoid M hn).ge

/--
theorem `pow_subset_pow` / 定理 `pow_subset_pow`

English:
theorem pow_subset_pow
  given: {n : Nat}
  statement: (↑M : Set A) ^ n subseteq ↑(M ^ n : Submodule R A)
  proof: trans AddSubmonoid.pow_subset_pow (le_pow_toAddSubmonoid M)

中文:
定理 pow_subset_pow
  条件: {n : 自然数}
  结论: (↑M : 集合 A) ^ n subseteq ↑(M ^ n : 子模 R A)
  证明: trans AddSubmonoid.pow_subset_pow (le_pow_toAddSubmonoid M)

Depends on / 依赖: AddSubmonoid, AddSubmonoid.pow_subset_pow, le_pow_toAddSubmonoid, pow_subset_pow
-/
theorem pow_subset_pow {n : Nat} : (↑M : Set A) ^ n subseteq ↑(M ^ n : Submodule R A) :=
  trans AddSubmonoid.pow_subset_pow (le_pow_toAddSubmonoid M)

/--
theorem `pow_mem_pow` / 定理 `pow_mem_pow`

English:
theorem pow_mem_pow
  given: {x : A} (hx : x in M) (n : Nat)
  statement: x ^ n in M ^ n
  proof: pow_subset_pow _ Set.pow_mem_pow hx

中文:
定理 pow_mem_pow
  条件: {x : A} (hx : x in M) (n : 自然数)
  结论: x ^ n in M ^ n
  证明: pow_subset_pow _ Set.pow_mem_pow hx

Depends on / 依赖: Set.pow_mem_pow, pow_mem_pow, pow_subset_pow
-/
theorem pow_mem_pow {x : A} (hx : x in M) (n : Nat) : x ^ n in M ^ n :=
pow_subset_pow _ Set.pow_mem_pow hx

/--
lemma `restrictScalars_pow` / 引理 `restrictScalars_pow`

English:
lemma restrictScalars_pow
  statement: {A B C : Type*} [Semiring A] [Semiring B]

中文:
引理 restrictScalars_pow
  结论: {A B C : 类型} [半环 A] [半环 B]

Depends on / 依赖: n.succ_ne_zero, restrictScalars_mul, restrictScalars_pow, succ_ne_zero
-/
lemma restrictScalars_pow {A B C : Type*} [Semiring A] [Semiring B]
    [Semiring C] [SMul A B] [Module A C] [Module B C]
    [IsScalarTower A C C] [IsScalarTower B C C] [IsScalarTower A B C]
    {I : Submodule B C} :
    forall {n : Nat}, (hn : n != 0) -> (I ^ n).restrictScalars A = I.restrictScalars A ^ n
  | 1, _ => by simp [Submodule.pow_one]
  | n + 2, _ => by
    simp [Submodule.pow_succ (n := n + 1), restrictScalars_mul, restrictScalars_pow n.succ_ne_zero]

/--
Instance `instIsReduced` / 实例 `instIsReduced`

English:
instance instIsReduced
  signature: [IsReduced A]
  body: by
    rw [Submodule.zero_eq_bot]; rw [Submodule.eq_bot_iff]
    rintro m hm
    obtain ⟨n, hn⟩ := hM
exact eq_zero_of_pow_eq_zero (M ^ n).eq_bot_iff.mp hn _ (pow_mem_pow M hm n)

中文:
实例 instIsReduced
  签名: [是既约 A]
  定义体: by
    rw [Submodule.zero_eq_bot]; rw [Submodule.eq_bot_iff]
    rintro m hm
    obtain ⟨n, hn⟩ := hM
exact eq_zero_of_pow_eq_zero (M ^ n).eq_bot_iff.mp hn _ (pow_mem_pow M hm n)

Depends on / 依赖: Submodule, Submodule.eq_bot_iff, Submodule.zero_eq_bot, eq_bot_iff, eq_bot_iff.mp, eq_zero_of_pow_eq_zero, pow_mem_pow, zero_eq_bot
-/
instance instIsReduced [IsReduced A] : IsReduced (Submodule R A) where
  eq_zero M hM := by
    rw [Submodule.zero_eq_bot]; rw [Submodule.eq_bot_iff]
    rintro m hm
    obtain ⟨n, hn⟩ := hM
exact eq_zero_of_pow_eq_zero (M ^ n).eq_bot_iff.mp hn _ (pow_mem_pow M hm n)

/--
theorem `pow_eq_bot` / 定理 `pow_eq_bot`

English:
theorem pow_eq_bot
  given: [IsReduced A] {M : Submodule R A} {n : Nat} (hn : n != 0)
  proof: by refine ⟨eq_zero_of_pow_eq_zero, by aesop⟩

中文:
定理 pow_eq_bot
  条件: [是既约 A] {M : 子模 R A} {n : 自然数} (hn : n != 0)
  证明: by refine ⟨eq_zero_of_pow_eq_zero, by aesop⟩

Depends on / 依赖: eq_zero_of_pow_eq_zero
-/
theorem pow_eq_bot [IsReduced A] {M : Submodule R A} {n : Nat} (hn : n != 0) :
    M ^ n = ⊥ ↔ M = ⊥ := by refine ⟨eq_zero_of_pow_eq_zero, by aesop⟩

end Module

variable {ι : Sort uι}
variable {R : Type u} [CommSemiring R]

section AlgebraSemiring

variable {A : Type v} [Semiring A] [Algebra R A]
variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

/--
theorem `one_eq_range` / 定理 `one_eq_range`

English:
theorem one_eq_range
  statement: (1 : Submodule R A) = LinearMap.range (Algebra.linearMap R A)
  proof: by
  rw [one_eq_span]; rw [LinearMap.span_singleton_eq_range]; rw [LinearMap.toSpanSingleton_one_eq_algebraLinearMap]

中文:
定理 one_eq_range
  结论: (1 : 子模 R A) = 线性映射.range (代数.linearMap R A)
  证明: by
  rw [one_eq_span]; rw [LinearMap.span_singleton_eq_range]; rw [LinearMap.toSpanSingleton_one_eq_algebraLinearMap]

Depends on / 依赖: LinearMap, LinearMap.span_singleton_eq_range, LinearMap.toSpanSingleton_one_eq_algebraLinearMap, one_eq_span, span_singleton_eq_range, toSpanSingleton_one_eq_algebraLinearMap
-/
theorem one_eq_range : (1 : Submodule R A) = LinearMap.range (Algebra.linearMap R A) := by
  rw [one_eq_span]; rw [LinearMap.span_singleton_eq_range]; rw [LinearMap.toSpanSingleton_one_eq_algebraLinearMap]

/--
theorem `algebraMap_mem` / 定理 `algebraMap_mem`

English:
theorem algebraMap_mem
  given: (r : R)
  statement: algebraMap R A r in (1 : Submodule R A)
  proof: by
  simp [one_eq_range]

@[simp]

中文:
定理 algebraMap_mem
  条件: (r : R)
  结论: algebraMap R A r in (1 : 子模 R A)
  证明: by
  simp [one_eq_range]

@[simp]

Depends on / 依赖: one_eq_range
-/
theorem algebraMap_mem (r : R) : algebraMap R A r in (1 : Submodule R A) := by
  simp [one_eq_range]

@[simp]
/--
theorem `mem_one` / 定理 `mem_one`

English:
theorem mem_one
  given: {x : A}
  statement: x in (1 : Submodule R A) ↔ exists y, algebraMap R A y = x
  proof: by
  simp [one_eq_range]

中文:
定理 mem_one
  条件: {x : A}
  结论: x in (1 : 子模 R A) ↔ 存在 y, algebraMap R A y = x
  证明: by
  simp [one_eq_range]

Depends on / 依赖: one_eq_range
-/
theorem mem_one {x : A} : x in (1 : Submodule R A) ↔ exists y, algebraMap R A y = x := by
  simp [one_eq_range]

/--
theorem `smul_one_eq_span` / 定理 `smul_one_eq_span`

English:
theorem smul_one_eq_span
  given: (x : A)
  statement: x • (1 : Submodule R A) = span R {x}
  proof: by
  rw [one_eq_span]; rw [smul_span]; rw [smul_set_singleton]; rw [smul_eq_mul]; rw [mul_one]

中文:
定理 smul_one_eq_span
  条件: (x : A)
  结论: x • (1 : 子模 R A) = span R {x}
  证明: by
  rw [one_eq_span]; rw [smul_span]; rw [smul_set_singleton]; rw [smul_eq_mul]; rw [mul_one]

Depends on / 依赖: mul_one, one_eq_span, smul_eq_mul, smul_set_singleton, smul_span
-/
theorem smul_one_eq_span (x : A) : x • (1 : Submodule R A) = span R {x} := by
  rw [one_eq_span]; rw [smul_span]; rw [smul_set_singleton]; rw [smul_eq_mul]; rw [mul_one]

/--
theorem `span_singleton_algebraMap_of_isUnit` / 定理 `span_singleton_algebraMap_of_isUnit`

English:
theorem span_singleton_algebraMap_of_isUnit
  given: {r : R} (h : IsUnit r)
  proof: by
  conv_rhs => rw [one_eq_span, ← span_singleton_smul_eq h, ← algebraMap_eq_smul_one]

中文:
定理 span_singleton_algebraMap_of_isUnit
  条件: {r : R} (h : 是单位 r)
  证明: by
  conv_rhs => rw [one_eq_span, ← span_singleton_smul_eq h, ← algebraMap_eq_smul_one]

Depends on / 依赖: algebraMap_eq_smul_one, conv_rhs, one_eq_span, span_singleton_smul_eq
-/
theorem span_singleton_algebraMap_of_isUnit {r : R} (h : IsUnit r) :
    span R {algebraMap R A r} = 1 := by
  conv_rhs => rw [one_eq_span, ← span_singleton_smul_eq h, ← algebraMap_eq_smul_one]

/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  given: {A'} [Semiring A'] [Algebra R A'] (f : A ->ₐ[R] A')
  proof: by
  ext
  simp

@[simp]

中文:
定理 map_one
  条件: {A'} [半环 A'] [代数 R A'] (f : A ->ₐ[R] A')
  证明: by
  ext
  simp

@[simp]
-/
protected theorem map_one {A'} [Semiring A'] [Algebra R A'] (f : A ->ₐ[R] A') :
    map f.toLinearMap (1 : Submodule R A) = 1 := by
  ext
  simp

@[simp]
/--
theorem `map_op_one` / 定理 `map_op_one`

English:
theorem map_op_one
  proof: by
  ext x
  induction x
  simp

@[simp]

中文:
定理 map_op_one
  证明: by
  ext x
  induction x
  simp

@[simp]
-/
theorem map_op_one :
    map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) (1 : Submodule R A) = 1 := by
  ext x
  induction x
  simp

@[simp]
/--
theorem `comap_op_one` / 定理 `comap_op_one`

English:
theorem comap_op_one
  proof: by
  ext
  simp

@[simp]

中文:
定理 comap_op_one
  证明: by
  ext
  simp

@[simp]
-/
theorem comap_op_one :
    comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) (1 : Submodule R Aᵐᵒᵖ) = 1 := by
  ext
  simp

@[simp]
/--
theorem `map_unop_one` / 定理 `map_unop_one`

English:
theorem map_unop_one
  proof: by
  rw [← comap_equiv_eq_map_symm]; rw [comap_op_one]

@[simp]

中文:
定理 map_unop_one
  证明: by
  rw [← comap_equiv_eq_map_symm]; rw [comap_op_one]

@[simp]

Depends on / 依赖: comap_equiv_eq_map_symm, comap_op_one
-/
theorem map_unop_one :
    map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A) (1 : Submodule R Aᵐᵒᵖ) = 1 := by
  rw [← comap_equiv_eq_map_symm]; rw [comap_op_one]

@[simp]
/--
theorem `comap_unop_one` / 定理 `comap_unop_one`

English:
theorem comap_unop_one
  proof: by
  rw [← map_equiv_eq_comap_symm]; rw [map_op_one]

中文:
定理 comap_unop_one
  证明: by
  rw [← map_equiv_eq_comap_symm]; rw [map_op_one]

Depends on / 依赖: map_equiv_eq_comap_symm, map_op_one
-/
theorem comap_unop_one :
    comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A) (1 : Submodule R A) = 1 := by
  rw [← map_equiv_eq_comap_symm]; rw [map_op_one]

/--
theorem `mul_eq_map₂` / 定理 `mul_eq_map₂`

English:
theorem mul_eq_map₂
  statement: M * N = map₂ (LinearMap.mul R A) M N
  proof: le_antisymm (mul_le.mpr fun _m hm _n => apply_mem_map₂ _ hm)
    (map₂_le.mpr fun _m hm _n => mul_mem_mul hm)

中文:
定理 mul_eq_map₂
  结论: M * N = map₂ (线性映射.mul R A) M N
  证明: le_antisymm (mul_le.mpr fun _m hm _n => apply_mem_map₂ _ hm)
    (map₂_le.mpr fun _m hm _n => mul_mem_mul hm)

Depends on / 依赖: _le.mpr, le_antisymm, mul_le, mul_le.mpr, mul_mem_mul
-/
theorem mul_eq_map₂ : M * N = map₂ (LinearMap.mul R A) M N :=
  le_antisymm (mul_le.mpr fun _m hm _n => apply_mem_map₂ _ hm)
    (map₂_le.mpr fun _m hm _n => mul_mem_mul hm)

variable (R M N)

/--
theorem `span_mul_span` / 定理 `span_mul_span`

English:
theorem span_mul_span
  statement: span R S * span R T = span R (S * T)
  proof: by
  rw [mul_eq_map₂]; apply map₂_span_span

中文:
定理 span_mul_span
  结论: span R S * span R T = span R (S * T)
  证明: by
  rw [mul_eq_map₂]; apply map₂_span_span
-/
theorem span_mul_span : span R S * span R T = span R (S * T) := by
  rw [mul_eq_map₂]; apply map₂_span_span

/--
lemma `mul_def` / 引理 `mul_def`

English:
lemma mul_def
  statement: M * N = span R (M * N : Set A)
  proof: by simp [← span_mul_span]

中文:
引理 mul_def
  结论: M * N = span R (M * N : 集合 A)
  证明: by simp [← span_mul_span]

Depends on / 依赖: span_mul_span
-/
lemma mul_def : M * N = span R (M * N : Set A) := by simp [← span_mul_span]

variable {R} (P Q)

/--
theorem `mul_one` / 定理 `mul_one`

English:
theorem mul_one
  statement: M * 1 = M
  proof: by
  conv_lhs => rw [one_eq_span, ← span_eq M]
  rw [span_mul_span]
  simp

中文:
定理 mul_one
  结论: M * 1 = M
  证明: by
  conv_lhs => rw [one_eq_span, ← span_eq M]
  rw [span_mul_span]
  simp
-/
protected theorem mul_one : M * 1 = M := by
  conv_lhs => rw [one_eq_span, ← span_eq M]
  rw [span_mul_span]
  simp

/--
theorem `map_mul` / 定理 `map_mul`

English:
theorem map_mul
  given: {A'} [Semiring A'] [Algebra R A'] (f : A ->ₐ[R] A')
  proof: calc
    map f.toLinearMap (M * N) = ⨆ i : M, (N.map (LinearMap.mul R A i)).map f.toLinearMap := by
      rw [mul_eq_map₂]; apply map_iSup
    _ = map f.toLinearMap M * map f.toLinearMap N := by
      rw [mul_eq_map₂]
      apply congr_arg sSup
      ext S
      constructor <;> rintro ⟨y, hy⟩
      · use ⟨f y, mem_map.mpr ⟨y.1, y.2, rfl⟩⟩
        refine Eq.trans ?_ hy
        ext
        simp
      · obtain ⟨y', hy', fy_eq⟩ := mem_map.mp y.2
        use ⟨y', hy'⟩
        refine Eq.trans ?_ hy
        rw [f.toLinearMap_apply] at fy_eq
        ext
        simp [fy_eq]

中文:
定理 map_mul
  条件: {A'} [半环 A'] [代数 R A'] (f : A ->ₐ[R] A')
  证明: calc
    map f.toLinearMap (M * N) = ⨆ i : M, (N.map (LinearMap.mul R A i)).map f.toLinearMap := by
      rw [mul_eq_map₂]; apply map_iSup
    _ = map f.toLinearMap M * map f.toLinearMap N := by
      rw [mul_eq_map₂]
      apply congr_arg sSup
      ext S
      constructor <;> rintro ⟨y, hy⟩
      · use ⟨f y, mem_map.mpr ⟨y.1, y.2, rfl⟩⟩
        refine Eq.trans ?_ hy
        ext
        simp
      · obtain ⟨y', hy', fy_eq⟩ := mem_map.mp y.2
        use ⟨y', hy'⟩
        refine Eq.trans ?_ hy
        rw [f.toLinearMap_apply] at fy_eq
        ext
        simp [fy_eq]
-/
protected theorem map_mul {A'} [Semiring A'] [Algebra R A'] (f : A ->ₐ[R] A') :
    map f.toLinearMap (M * N) = map f.toLinearMap M * map f.toLinearMap N :=
  calc
    map f.toLinearMap (M * N) = ⨆ i : M, (N.map (LinearMap.mul R A i)).map f.toLinearMap := by
      rw [mul_eq_map₂]; apply map_iSup
    _ = map f.toLinearMap M * map f.toLinearMap N := by
      rw [mul_eq_map₂]
      apply congr_arg sSup
      ext S
      constructor <;> rintro ⟨y, hy⟩
      · use ⟨f y, mem_map.mpr ⟨y.1, y.2, rfl⟩⟩
        refine Eq.trans ?_ hy
        ext
        simp
      · obtain ⟨y', hy', fy_eq⟩ := mem_map.mp y.2
        use ⟨y', hy'⟩
        refine Eq.trans ?_ hy
        rw [f.toLinearMap_apply] at fy_eq
        ext
        simp [fy_eq]

/--
theorem `map_op_mul` / 定理 `map_op_mul`

English:
theorem map_op_mul
  proof: by
  apply le_antisymm
  · simp_rw [map_le_iff_le_comap]
    refine mul_le.2 fun m hm n hn => ?_
    rw [mem_comap]; rw [map_equiv_eq_comap_symm]; rw [map_equiv_eq_comap_symm]
    change op n * op m in _
    exact mul_mem_mul hn hm
  · refine mul_le.2 (MulOpposite.rec' fun m hm => MulOpposite.rec' fun n hn => ?_)
    rw [Submodule.mem_map_equiv] at hm hn ⊢
    exact mul_mem_mul hn hm

中文:
定理 map_op_mul
  证明: by
  apply le_antisymm
  · simp_rw [map_le_iff_le_comap]
    refine mul_le.2 fun m hm n hn => ?_
    rw [mem_comap]; rw [map_equiv_eq_comap_symm]; rw [map_equiv_eq_comap_symm]
    change op n * op m in _
    exact mul_mem_mul hn hm
  · refine mul_le.2 (MulOpposite.rec' fun m hm => MulOpposite.rec' fun n hn => ?_)
    rw [Submodule.mem_map_equiv] at hm hn ⊢
    exact mul_mem_mul hn hm

Depends on / 依赖: MulOpposite, MulOpposite.rec, Submodule, Submodule.mem_map_equiv, le_antisymm, map_equiv_eq_comap_symm, map_le_iff_le_comap, mem_comap, mem_map_equiv, mul_le, mul_mem_mul, simp_rw
-/
theorem map_op_mul :
    map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) (M * N) =
      map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) N *
        map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) M := by
  apply le_antisymm
  · simp_rw [map_le_iff_le_comap]
    refine mul_le.2 fun m hm n hn => ?_
    rw [mem_comap]; rw [map_equiv_eq_comap_symm]; rw [map_equiv_eq_comap_symm]
    change op n * op m in _
    exact mul_mem_mul hn hm
  · refine mul_le.2 (MulOpposite.rec' fun m hm => MulOpposite.rec' fun n hn => ?_)
    rw [Submodule.mem_map_equiv] at hm hn ⊢
    exact mul_mem_mul hn hm

/--
theorem `comap_unop_mul` / 定理 `comap_unop_mul`

English:
theorem comap_unop_mul
  proof: by
  simp_rw [← map_equiv_eq_comap_symm, map_op_mul]

中文:
定理 comap_unop_mul
  证明: by
  simp_rw [← map_equiv_eq_comap_symm, map_op_mul]

Depends on / 依赖: map_equiv_eq_comap_symm, map_op_mul, simp_rw
-/
theorem comap_unop_mul :
    comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A) (M * N) =
      comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A) N *
        comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A) M := by
  simp_rw [← map_equiv_eq_comap_symm, map_op_mul]

/--
theorem `map_unop_mul` / 定理 `map_unop_mul`

English:
theorem map_unop_mul
  given: (M N : Submodule R Aᵐᵒᵖ)
  proof: have : Function.Injective (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) :=
    LinearEquiv.injective _
map_injective_of_injective this by
    rw [← map_comp]; rw [map_op_mul]; rw [← map_comp]; rw [← map_comp]; rw [LinearEquiv.comp_coe]; rw [LinearEquiv.symm_trans_self]; rw [LinearEquiv.refl_toLinearMap]; rw [map_id]; rw [map_id]; rw [map_id]

中文:
定理 map_unop_mul
  条件: (M N : 子模 R Aᵐᵒᵖ)
  证明: have : Function.Injective (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) :=
    LinearEquiv.injective _
map_injective_of_injective this by
    rw [← map_comp]; rw [map_op_mul]; rw [← map_comp]; rw [← map_comp]; rw [LinearEquiv.comp_coe]; rw [LinearEquiv.symm_trans_self]; rw [LinearEquiv.refl_toLinearMap]; rw [map_id]; rw [map_id]; rw [map_id]

Depends on / 依赖: Function, Function.Injective, Injective, LinearEquiv, LinearEquiv.comp_coe, LinearEquiv.injective, LinearEquiv.refl_toLinearMap, LinearEquiv.symm_trans_self, comp_coe, injective, map_comp, map_id, map_injective_of_injective, map_op_mul, opLinearEquiv, refl_toLinearMap, symm_trans_self
-/
theorem map_unop_mul (M N : Submodule R Aᵐᵒᵖ) :
    map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A) (M * N) =
      map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A) N *
        map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A) M :=
  have : Function.Injective (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) :=
    LinearEquiv.injective _
map_injective_of_injective this by
    rw [← map_comp]; rw [map_op_mul]; rw [← map_comp]; rw [← map_comp]; rw [LinearEquiv.comp_coe]; rw [LinearEquiv.symm_trans_self]; rw [LinearEquiv.refl_toLinearMap]; rw [map_id]; rw [map_id]; rw [map_id]

/--
theorem `comap_op_mul` / 定理 `comap_op_mul`

English:
theorem comap_op_mul
  given: (M N : Submodule R Aᵐᵒᵖ)
  proof: by
  simp_rw [comap_equiv_eq_map_symm, map_unop_mul]

中文:
定理 comap_op_mul
  条件: (M N : 子模 R Aᵐᵒᵖ)
  证明: by
  simp_rw [comap_equiv_eq_map_symm, map_unop_mul]

Depends on / 依赖: comap_equiv_eq_map_symm, map_unop_mul, simp_rw
-/
theorem comap_op_mul (M N : Submodule R Aᵐᵒᵖ) :
    comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) (M * N) =
      comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) N *
        comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) M := by
  simp_rw [comap_equiv_eq_map_symm, map_unop_mul]

section
variable {α : Type*} [Monoid α] [DistribMulAction α A] [SMulCommClass α R A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsScalarTower
  signature: α A A] : IsScalarTower α (Submodule R A) (Submodule R A) where
  body: by
    rw [← S.span_eq]; rw [← T.span_eq]; rw [smul_span]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [span_mul_span]; rw [span_mul_span]; rw [smul_span]; rw [smul_mul_assoc]

中文:
实例 [标量塔
  签名: α A A] : 标量塔 α (子模 R A) (子模 R A) where
  定义体: by
    rw [← S.span_eq]; rw [← T.span_eq]; rw [smul_span]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [span_mul_span]; rw [span_mul_span]; rw [smul_span]; rw [smul_mul_assoc]

Depends on / 依赖: S.span_eq, T.span_eq, smul_eq_mul, smul_mul_assoc, smul_span, span_eq, span_mul_span
-/
instance [IsScalarTower α A A] : IsScalarTower α (Submodule R A) (Submodule R A) where
  smul_assoc a S T := by
    rw [← S.span_eq]; rw [← T.span_eq]; rw [smul_span]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [span_mul_span]; rw [span_mul_span]; rw [smul_span]; rw [smul_mul_assoc]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: α A A] : SMulCommClass α (Submodule R A) (Submodule R A) where
  body: by
    rw [← S.span_eq]; rw [← T.span_eq]; rw [smul_span]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [span_mul_span]; rw [span_mul_span]; rw [smul_span]; rw [mul_smul_comm]

中文:
实例 [标量交换类
  签名: α A A] : 标量交换类 α (子模 R A) (子模 R A) where
  定义体: by
    rw [← S.span_eq]; rw [← T.span_eq]; rw [smul_span]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [span_mul_span]; rw [span_mul_span]; rw [smul_span]; rw [mul_smul_comm]

Depends on / 依赖: S.span_eq, T.span_eq, mul_smul_comm, smul_eq_mul, smul_span, span_eq, span_mul_span
-/
instance [SMulCommClass α A A] : SMulCommClass α (Submodule R A) (Submodule R A) where
  smul_comm a S T := by
    rw [← S.span_eq]; rw [← T.span_eq]; rw [smul_span]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [span_mul_span]; rw [span_mul_span]; rw [smul_span]; rw [mul_smul_comm]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: A α A] : SMulCommClass (Submodule R A) α (Submodule R A)
  body: have := SMulCommClass.symm A α A; .symm ..

中文:
实例 [标量交换类
  签名: A α A] : 标量交换类 (子模 R A) α (子模 R A)
  定义体: have := SMulCommClass.symm A α A; .symm ..

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance [SMulCommClass A α A] : SMulCommClass (Submodule R A) α (Submodule R A) :=
  have := SMulCommClass.symm A α A; .symm ..

end

section

open scoped Pointwise

/-- `Submodule.pointwiseNeg` distributes over multiplication.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/--
Definition of `hasDistribPointwiseNeg` / `hasDistribPointwiseNeg` 的定义

English:
definition hasDistribPointwiseNeg
  signature: {A} [Ring A] [Algebra R A]
  body: toAddSubmonoid_injective.hasDistribNeg _ neg_toAddSubmonoid mul_toAddSubmonoid

scoped[Pointwise] attribute [instance] Submodule.hasDistribPointwiseNeg

中文:
定义 hasDistribPointwiseNeg
  签名: {A} [环 A] [代数 R A]
  定义体: toAddSubmonoid_injective.hasDistribNeg _ neg_toAddSubmonoid mul_toAddSubmonoid

scoped[Pointwise] attribute [instance] Submodule.hasDistribPointwiseNeg
-/
protected def hasDistribPointwiseNeg {A} [Ring A] [Algebra R A] : HasDistribNeg (Submodule R A) :=
  toAddSubmonoid_injective.hasDistribNeg _ neg_toAddSubmonoid mul_toAddSubmonoid

scoped[Pointwise] attribute [instance] Submodule.hasDistribPointwiseNeg

end

section DecidableEq

/--
theorem `mem_span_mul_finite_of_mem_span_mul` / 定理 `mem_span_mul_finite_of_mem_span_mul`

English:
theorem mem_span_mul_finite_of_mem_span_mul
  statement: {R A} [Semiring R] [AddCommMonoid A] [Mul A]
  proof: by
  classical
  obtain ⟨U, h, hU⟩ := mem_span_finite_of_mem_span hx
  obtain ⟨T, T', hS, hS', h⟩ := Finset.subset_mul h
  use T, T', hS, hS'
  have h' : (U : Set A) subseteq T * T' := by assumption_mod_cast
  have h'' := span_mono h' hU
  assumption

中文:
定理 mem_span_mul_finite_of_mem_span_mul
  结论: {R A} [半环 R] [加法交换幺半群 A] [乘法 A]
  证明: by
  classical
  obtain ⟨U, h, hU⟩ := mem_span_finite_of_mem_span hx
  obtain ⟨T, T', hS, hS', h⟩ := Finset.subset_mul h
  use T, T', hS, hS'
  have h' : (U : Set A) subseteq T * T' := by assumption_mod_cast
  have h'' := span_mono h' hU
  assumption

Depends on / 依赖: Finset, Finset.subset_mul, assumption_mod_cast, classical, mem_span_finite_of_mem_span, span_mono, subset_mul, subseteq
-/
theorem mem_span_mul_finite_of_mem_span_mul {R A} [Semiring R] [AddCommMonoid A] [Mul A]
    [Module R A] {S : Set A} {S' : Set A} {x : A} (hx : x in span R (S * S')) :
    exists T T' : Finset A, ↑T subseteq S ∧ ↑T' subseteq S' ∧ x in span R (T * T' : Set A) := by
  classical
  obtain ⟨U, h, hU⟩ := mem_span_finite_of_mem_span hx
  obtain ⟨T, T', hS, hS', h⟩ := Finset.subset_mul h
  use T, T', hS, hS'
  have h' : (U : Set A) subseteq T * T' := by assumption_mod_cast
  have h'' := span_mono h' hU
  assumption

end DecidableEq

/--
theorem `mul_eq_span_mul_set` / 定理 `mul_eq_span_mul_set`

English:
theorem mul_eq_span_mul_set
  given: (s t : Submodule R A)
  statement: s * t = span R ((s : Set A) * (t : Set A))
  proof: by
  rw [mul_eq_map₂]; exact map₂_eq_span_image2 _ s t

中文:
定理 mul_eq_span_mul_set
  条件: (s t : 子模 R A)
  结论: s * t = span R ((s : 集合 A) * (t : 集合 A))
  证明: by
  rw [mul_eq_map₂]; exact map₂_eq_span_image2 _ s t
-/
theorem mul_eq_span_mul_set (s t : Submodule R A) : s * t = span R ((s : Set A) * (t : Set A)) := by
  rw [mul_eq_map₂]; exact map₂_eq_span_image2 _ s t

/--
theorem `mem_span_mul_finite_of_mem_mul` / 定理 `mem_span_mul_finite_of_mem_mul`

English:
theorem mem_span_mul_finite_of_mem_mul
  given: {P Q : Submodule R A} {x : A} (hx : x in P * Q)
  proof: Submodule.mem_span_mul_finite_of_mem_span_mul
    (by rwa [← Submodule.span_eq P, ← Submodule.span_eq Q, Submodule.span_mul_span] at hx)

中文:
定理 mem_span_mul_finite_of_mem_mul
  条件: {P Q : 子模 R A} {x : A} (hx : x in P * Q)
  证明: Submodule.mem_span_mul_finite_of_mem_span_mul
    (by rwa [← Submodule.span_eq P, ← Submodule.span_eq Q, Submodule.span_mul_span] at hx)

Depends on / 依赖: Submodule, Submodule.mem_span_mul_finite_of_mem_span_mul, Submodule.span_eq, Submodule.span_mul_span, mem_span_mul_finite_of_mem_span_mul, span_eq, span_mul_span
-/
theorem mem_span_mul_finite_of_mem_mul {P Q : Submodule R A} {x : A} (hx : x in P * Q) :
    exists T T' : Finset A, (T : Set A) subseteq P ∧ (T' : Set A) subseteq Q ∧ x in span R (T * T' : Set A) :=
  Submodule.mem_span_mul_finite_of_mem_span_mul
    (by rwa [← Submodule.span_eq P, ← Submodule.span_eq Q, Submodule.span_mul_span] at hx)

variable {M N P}

/--
theorem `mem_span_singleton_mul` / 定理 `mem_span_singleton_mul`

English:
theorem mem_span_singleton_mul
  given: {x y : A}
  statement: x in span R {y} * P ↔ exists z in P, y * z = x
  proof: by
  simp_rw [mul_eq_map₂, map₂_span_singleton_eq_map, mem_map, LinearMap.mul_apply_apply]

中文:
定理 mem_span_singleton_mul
  条件: {x y : A}
  结论: x in span R {y} * P ↔ 存在 z in P, y * z = x
  证明: by
  simp_rw [mul_eq_map₂, map₂_span_singleton_eq_map, mem_map, LinearMap.mul_apply_apply]

Depends on / 依赖: LinearMap, LinearMap.mul_apply_apply, mem_map, mul_apply_apply, simp_rw
-/
theorem mem_span_singleton_mul {x y : A} : x in span R {y} * P ↔ exists z in P, y * z = x := by
  simp_rw [mul_eq_map₂, map₂_span_singleton_eq_map, mem_map, LinearMap.mul_apply_apply]

/--
theorem `mem_mul_span_singleton` / 定理 `mem_mul_span_singleton`

English:
theorem mem_mul_span_singleton
  given: {x y : A}
  statement: x in P * span R {y} ↔ exists z in P, z * y = x
  proof: by
  simp_rw [mul_eq_map₂, map₂_span_singleton_eq_map_flip, mem_map, LinearMap.flip_apply,
    LinearMap.mul_apply_apply]

中文:
定理 mem_mul_span_singleton
  条件: {x y : A}
  结论: x in P * span R {y} ↔ 存在 z in P, z * y = x
  证明: by
  simp_rw [mul_eq_map₂, map₂_span_singleton_eq_map_flip, mem_map, LinearMap.flip_apply,
    LinearMap.mul_apply_apply]

Depends on / 依赖: LinearMap, LinearMap.flip_apply, LinearMap.mul_apply_apply, flip_apply, mem_map, mul_apply_apply, simp_rw
-/
theorem mem_mul_span_singleton {x y : A} : x in P * span R {y} ↔ exists z in P, z * y = x := by
  simp_rw [mul_eq_map₂, map₂_span_singleton_eq_map_flip, mem_map, LinearMap.flip_apply,
    LinearMap.mul_apply_apply]

/--
lemma `span_singleton_mul` / 引理 `span_singleton_mul`

English:
lemma span_singleton_mul
  given: {x : A} {p : Submodule R A}
  proof: ext fun _ => mem_span_singleton_mul

中文:
引理 span_singleton_mul
  条件: {x : A} {p : 子模 R A}
  证明: ext fun _ => mem_span_singleton_mul

Depends on / 依赖: mem_span_singleton_mul
-/
lemma span_singleton_mul {x : A} {p : Submodule R A} :
    Submodule.span R {x} * p = x • p := ext fun _ => mem_span_singleton_mul

/--
lemma `mem_smul_iff_inv_mul_mem` / 引理 `mem_smul_iff_inv_mul_mem`

English:
lemma mem_smul_iff_inv_mul_mem
  statement: {S} [DivisionSemiring S] [Algebra R S] {x : S} {p : Submodule R S}
  proof: by
  constructor
  · rintro ⟨a, ha : a in p, rfl⟩; simpa [inv_mul_cancel_left₀ hx]
  · exact fun h => ⟨_, h, by simp [mul_inv_cancel_left₀ hx]⟩

中文:
引理 mem_smul_iff_inv_mul_mem
  结论: {S} [除半环 S] [代数 R S] {x : S} {p : 子模 R S}
  证明: by
  constructor
  · rintro ⟨a, ha : a in p, rfl⟩; simpa [inv_mul_cancel_left₀ hx]
  · exact fun h => ⟨_, h, by simp [mul_inv_cancel_left₀ hx]⟩
-/
lemma mem_smul_iff_inv_mul_mem {S} [DivisionSemiring S] [Algebra R S] {x : S} {p : Submodule R S}
    {y : S} (hx : x != 0) : y in x • p ↔ x⁻¹ * y in p := by
  constructor
  · rintro ⟨a, ha : a in p, rfl⟩; simpa [inv_mul_cancel_left₀ hx]
  · exact fun h => ⟨_, h, by simp [mul_inv_cancel_left₀ hx]⟩

/--
lemma `mul_mem_smul_iff` / 引理 `mul_mem_smul_iff`

English:
lemma mul_mem_smul_iff
  statement: {S} [Ring S] [Algebra R S] {x : S} {p : Submodule R S} {y : S}
  proof: by
  simp [mem_smul_pointwise_iff_exists, mul_cancel_left_mem_nonZeroDivisors hx]

中文:
引理 mul_mem_smul_iff
  结论: {S} [环 S] [代数 R S] {x : S} {p : 子模 R S} {y : S}
  证明: by
  simp [mem_smul_pointwise_iff_exists, mul_cancel_left_mem_nonZeroDivisors hx]

Depends on / 依赖: mem_smul_pointwise_iff_exists, mul_cancel_left_mem_nonZeroDivisors
-/
lemma mul_mem_smul_iff {S} [Ring S] [Algebra R S] {x : S} {p : Submodule R S} {y : S}
    (hx : x in nonZeroDivisors S) :
    x * y in x • p ↔ y in p := by
  simp [mem_smul_pointwise_iff_exists, mul_cancel_left_mem_nonZeroDivisors hx]

variable (M N) in
/--
theorem `mul_smul_mul_eq_smul_mul_smul` / 定理 `mul_smul_mul_eq_smul_mul_smul`

English:
theorem mul_smul_mul_eq_smul_mul_smul
  given: (x y : R)
  statement: (x * y) • (M * N) = (x • M) * (y • N)
  proof: mul_smul_mul_comm x y M N

中文:
定理 mul_smul_mul_eq_smul_mul_smul
  条件: (x y : R)
  结论: (x * y) • (M * N) = (x • M) * (y • N)
  证明: mul_smul_mul_comm x y M N

Depends on / 依赖: mul_smul_mul_comm
-/
theorem mul_smul_mul_eq_smul_mul_smul (x y : R) : (x * y) • (M * N) = (x • M) * (y • N) :=
  mul_smul_mul_comm x y M N

/--
Instance `idemSemiring` / 实例 `idemSemiring`

English:
instance idemSemiring
  signature: : IdemSemiring (Submodule R A) where
  body: Submodule.one_mul
  mul_one := Submodule.mul_one

中文:
实例 idemSemiring
  签名: : IdemSemiring (子模 R A) where
  定义体: Submodule.one_mul
  mul_one := Submodule.mul_one

Depends on / 依赖: Submodule, Submodule.one_mul, one_mul
-/
instance idemSemiring : IdemSemiring (Submodule R A) where
  one_mul := Submodule.one_mul
  mul_one := Submodule.mul_one

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedRing (Submodule R A)

中文:
实例 :
  签名: 是Ordered环 (子模 R A)
-/
instance : IsOrderedRing (Submodule R A) where

variable (M)

/--
theorem `span_pow` / 定理 `span_pow`

English:
theorem span_pow
  given: (s : Set A)
  statement: forall n : Nat, span R s ^ n = span R (s ^ n)

中文:
定理 span_pow
  条件: (s : 集合 A)
  结论: 对任意 n : 自然数, span R s ^ n = span R (s ^ n)
-/
theorem span_pow (s : Set A) : forall n : Nat, span R s ^ n = span R (s ^ n)
  | 0 => by rw [pow_zero, pow_zero, one_eq_span_one_set]
  | n + 1 => by rw [pow_succ, pow_succ, span_pow s n, span_mul_span]

/--
theorem `pow_eq_span_pow_set` / 定理 `pow_eq_span_pow_set`

English:
theorem pow_eq_span_pow_set
  given: (n : Nat)
  statement: M ^ n = span R ((M : Set A) ^ n)
  proof: by
  rw [← span_pow]; rw [span_eq]

中文:
定理 pow_eq_span_pow_set
  条件: (n : 自然数)
  结论: M ^ n = span R ((M : 集合 A) ^ n)
  证明: by
  rw [← span_pow]; rw [span_eq]

Depends on / 依赖: span_eq, span_pow
-/
theorem pow_eq_span_pow_set (n : Nat) : M ^ n = span R ((M : Set A) ^ n) := by
  rw [← span_pow]; rw [span_eq]

/--
theorem `top_mul_eq_top_of_mul_eq_one` / 定理 `top_mul_eq_top_of_mul_eq_one`

English:
theorem top_mul_eq_top_of_mul_eq_one
  given: (h : N * P = 1)
  statement: ⊤ * P = ⊤
  proof: top_unique by
    conv_lhs => rw [← mul_one ⊤, ← h, ← mul_assoc]
    exact smul_mono_left le_top

中文:
定理 top_mul_eq_top_of_mul_eq_one
  条件: (h : N * P = 1)
  结论: ⊤ * P = ⊤
  证明: top_unique by
    conv_lhs => rw [← mul_one ⊤, ← h, ← mul_assoc]
    exact smul_mono_left le_top

Depends on / 依赖: conv_lhs, le_top, mul_assoc, mul_one, smul_mono_left, top_unique
-/
theorem top_mul_eq_top_of_mul_eq_one (h : N * P = 1) : ⊤ * P = ⊤ :=
top_unique by
    conv_lhs => rw [← mul_one ⊤, ← h, ← mul_assoc]
    exact smul_mono_left le_top

/-- Dependent version of `Submodule.pow_induction_on_left`. -/
@[elab_as_elim]
/--
theorem `pow_induction_on_left'` / 定理 `pow_induction_on_left'`

English:
theorem pow_induction_on_left'
  statement: {C : forall (n : Nat) (x), x in M ^ n -> Prop}
  proof: by
  induction n generalizing x with
  | zero =>
    rw [pow_zero] at hx
    obtain ⟨r, rfl⟩ := mem_one.mp hx
    exact algebraMap r
  | succ n n_ih =>
    revert hx
    simp_rw [pow_succ']
    exact fun hx => Submodule.mul_induction_on' (fun m hm x ih => mem_mul _ hm _ _ _ (n_ih ih))
      (fun x hx y hy Cx Cy => add _ _ _ _ _ Cx Cy) hx

中文:
定理 pow_induction_on_left'
  结论: {C : 对任意 (n : 自然数) (x), x in M ^ n -> 命题}
  证明: by
  induction n generalizing x with
  | zero =>
    rw [pow_zero] at hx
    obtain ⟨r, rfl⟩ := mem_one.mp hx
    exact algebraMap r
  | succ n n_ih =>
    revert hx
    simp_rw [pow_succ']
    exact fun hx => Submodule.mul_induction_on' (fun m hm x ih => mem_mul _ hm _ _ _ (n_ih ih))
      (fun x hx y hy Cx Cy => add _ _ _ _ _ Cx Cy) hx
-/
protected theorem pow_induction_on_left' {C : forall (n : Nat) (x), x in M ^ n -> Prop}
    (algebraMap : forall r : R, C 0 (algebraMap _ _ r) (algebraMap_mem r))
    (add : forall x y i hx hy, C i x hx -> C i y hy -> C i (x + y) (add_mem ‹_› ‹_›))
    (mem_mul : forall m (hm : m in M), forall (i x hx), C i x hx -> C i.succ (m * x)
      ((pow_succ' M i).symm ▸ (mul_mem_mul hm hx)))
    {n : Nat} {x : A}
    (hx : x in M ^ n) : C n x hx := by
  induction n generalizing x with
  | zero =>
    rw [pow_zero] at hx
    obtain ⟨r, rfl⟩ := mem_one.mp hx
    exact algebraMap r
  | succ n n_ih =>
    revert hx
    simp_rw [pow_succ']
    exact fun hx => Submodule.mul_induction_on' (fun m hm x ih => mem_mul _ hm _ _ _ (n_ih ih))
      (fun x hx y hy Cx Cy => add _ _ _ _ _ Cx Cy) hx

/-- Dependent version of `Submodule.pow_induction_on_right`. -/
@[elab_as_elim]
/--
theorem `pow_induction_on_right'` / 定理 `pow_induction_on_right'`

English:
theorem pow_induction_on_right'
  statement: {C : forall (n : Nat) (x), x in M ^ n -> Prop}
  proof: by
  induction n generalizing x with
  | zero =>
    rw [pow_zero] at hx
    obtain ⟨r, rfl⟩ := mem_one.mp hx
    exact algebraMap r
  | succ n n_ih =>
    revert hx
    simp_rw [pow_succ]
    exact fun hx => Submodule.mul_induction_on' (fun m hm x ih => mul_mem _ _ hm (n_ih _) _ ih)
      (fun x hx y hy Cx Cy => add _ _ _ _ _ Cx Cy) hx

中文:
定理 pow_induction_on_right'
  结论: {C : 对任意 (n : 自然数) (x), x in M ^ n -> 命题}
  证明: by
  induction n generalizing x with
  | zero =>
    rw [pow_zero] at hx
    obtain ⟨r, rfl⟩ := mem_one.mp hx
    exact algebraMap r
  | succ n n_ih =>
    revert hx
    simp_rw [pow_succ]
    exact fun hx => Submodule.mul_induction_on' (fun m hm x ih => mul_mem _ _ hm (n_ih _) _ ih)
      (fun x hx y hy Cx Cy => add _ _ _ _ _ Cx Cy) hx
-/
protected theorem pow_induction_on_right' {C : forall (n : Nat) (x), x in M ^ n -> Prop}
    (algebraMap : forall r : R, C 0 (algebraMap _ _ r) (algebraMap_mem r))
    (add : forall x y i hx hy, C i x hx -> C i y hy -> C i (x + y) (add_mem ‹_› ‹_›))
    (mul_mem :
      forall i x hx, C i x hx ->
        forall m (hm : m in M), C i.succ (x * m) (mul_mem_mul hx hm))
    {n : Nat} {x : A} (hx : x in M ^ n) : C n x hx := by
  induction n generalizing x with
  | zero =>
    rw [pow_zero] at hx
    obtain ⟨r, rfl⟩ := mem_one.mp hx
    exact algebraMap r
  | succ n n_ih =>
    revert hx
    simp_rw [pow_succ]
    exact fun hx => Submodule.mul_induction_on' (fun m hm x ih => mul_mem _ _ hm (n_ih _) _ ih)
      (fun x hx y hy Cx Cy => add _ _ _ _ _ Cx Cy) hx

/-- To show a property on elements of `M ^ n` holds, it suffices to show that it holds for scalars,
is closed under addition, and holds for `m * x` where `m ∈ M` and it holds for `x` -/
@[elab_as_elim]
/--
theorem `pow_induction_on_left` / 定理 `pow_induction_on_left`

English:
theorem pow_induction_on_left
  statement: {C : A -> Prop} (hr : forall r : R, C (algebraMap _ _ r))
  proof: Submodule.pow_induction_on_left' M (C := fun _ a _ => C a) hr
    (fun x y _i _hx _hy => hadd x y)
    (fun _m hm _i _x _hx => hmul _ hm _) hx

中文:
定理 pow_induction_on_left
  结论: {C : A -> 命题} (hr : 对任意 r : R, C (algebraMap _ _ r))
  证明: Submodule.pow_induction_on_left' M (C := fun _ a _ => C a) hr
    (fun x y _i _hx _hy => hadd x y)
    (fun _m hm _i _x _hx => hmul _ hm _) hx
-/
protected theorem pow_induction_on_left {C : A -> Prop} (hr : forall r : R, C (algebraMap _ _ r))
    (hadd : forall x y, C x -> C y -> C (x + y)) (hmul : forall m in M, forall (x), C x -> C (m * x)) {x : A} {n : Nat}
    (hx : x in M ^ n) : C x :=
  Submodule.pow_induction_on_left' M (C := fun _ a _ => C a) hr
    (fun x y _i _hx _hy => hadd x y)
    (fun _m hm _i _x _hx => hmul _ hm _) hx

/-- To show a property on elements of `M ^ n` holds, it suffices to show that it holds for scalars,
is closed under addition, and holds for `x * m` where `m ∈ M` and it holds for `x` -/
@[elab_as_elim]
/--
theorem `pow_induction_on_right` / 定理 `pow_induction_on_right`

English:
theorem pow_induction_on_right
  statement: {C : A -> Prop} (hr : forall r : R, C (algebraMap _ _ r))
  proof: Submodule.pow_induction_on_right' (M := M) (C := fun _ a _ => C a) hr
    (fun x y _i _hx _hy => hadd x y)
    (fun _i _x _hx => hmul _) hx

中文:
定理 pow_induction_on_right
  结论: {C : A -> 命题} (hr : 对任意 r : R, C (algebraMap _ _ r))
  证明: Submodule.pow_induction_on_right' (M := M) (C := fun _ a _ => C a) hr
    (fun x y _i _hx _hy => hadd x y)
    (fun _i _x _hx => hmul _) hx
-/
protected theorem pow_induction_on_right {C : A -> Prop} (hr : forall r : R, C (algebraMap _ _ r))
    (hadd : forall x y, C x -> C y -> C (x + y)) (hmul : forall x, C x -> forall m in M, C (x * m)) {x : A} {n : Nat}
    (hx : x in M ^ n) : C x :=
  Submodule.pow_induction_on_right' (M := M) (C := fun _ a _ => C a) hr
    (fun x y _i _hx _hy => hadd x y)
    (fun _i _x _hx => hmul _) hx

/-- `Submonoid.map` as a `RingHom`, when applied to an `AlgHom`. -/
@[simps]
/--
Definition of `mapHom` / `mapHom` 的定义

English:
definition mapHom
  signature: {A'} [Semiring A'] [Algebra R A'] (f : A ->ₐ[R] A')
  body: map f.toLinearMap
  map_zero' := Submodule.map_bot _
  map_add' := (Submodule.map_sup · · _)
  map_one' := Submodule.map_one _
  map_mul' := (Submodule.map_mul · · _)

中文:
定义 mapHom
  签名: {A'} [半环 A'] [代数 R A'] (f : A ->ₐ[R] A')
  定义体: map f.toLinearMap
  map_zero' := Submodule.map_bot _
  map_add' := (Submodule.map_sup · · _)
  map_one' := Submodule.map_one _
  map_mul' := (Submodule.map_mul · · _)

Depends on / 依赖: f.toLinearMap, toLinearMap
-/
def mapHom {A'} [Semiring A'] [Algebra R A'] (f : A ->ₐ[R] A') :
    Submodule R A ->+* Submodule R A' where
  toFun := map f.toLinearMap
  map_zero' := Submodule.map_bot _
  map_add' := (Submodule.map_sup · · _)
  map_one' := Submodule.map_one _
  map_mul' := (Submodule.map_mul · · _)

/--
theorem `mapHom_id` / 定理 `mapHom_id`

English:
theorem mapHom_id
  statement: mapHom (.id R A) = .id _
  proof: RingHom.ext map_id

中文:
定理 mapHom_id
  结论: mapHom (.id R A) = .id _
  证明: RingHom.ext map_id

Depends on / 依赖: RingHom, RingHom.ext, map_id
-/
theorem mapHom_id : mapHom (.id R A) = .id _ := RingHom.ext map_id

/-- The ring of submodules of the opposite algebra is isomorphic to the opposite ring of
submodules. -/
@[simps apply symm_apply]
/--
Definition of `equivOpposite` / `equivOpposite` 的定义

English:
definition equivOpposite
  signature: : Submodule R Aᵐᵒᵖ ≃+* (Submodule R A)ᵐᵒᵖ where
  body: op p.comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ)
  invFun p := p.unop.comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A)
left_inv _ := SetLike.coe_injective rfl
right_inv _ := unop_injective SetLike.coe_injective rfl
  map_add' p q := by simp [comap_equiv_eq_map_symm, ← op_add]
map_mul' _ _ := congr_arg op comap_op_mul _ _

中文:
定义 equivOpposite
  签名: : 子模 R Aᵐᵒᵖ ≃+* (子模 R A)ᵐᵒᵖ where
  定义体: op p.comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ)
  invFun p := p.unop.comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A)
left_inv _ := SetLike.coe_injective rfl
right_inv _ := unop_injective SetLike.coe_injective rfl
  map_add' p q := by simp [comap_equiv_eq_map_symm, ← op_add]
map_mul' _ _ := congr_arg op comap_op_mul _ _

Depends on / 依赖: Function, Function.Injective.module, Injective, module, opLinearEquiv, p.comap, unsym_add, unsym_injective, unsym_smul, unsym_zero
-/
def equivOpposite : Submodule R Aᵐᵒᵖ ≃+* (Submodule R A)ᵐᵒᵖ where
toFun p := op p.comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ)
  invFun p := p.unop.comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A)
left_inv _ := SetLike.coe_injective rfl
right_inv _ := unop_injective SetLike.coe_injective rfl
  map_add' p q := by simp [comap_equiv_eq_map_symm, ← op_add]
map_mul' _ _ := congr_arg op comap_op_mul _ _

/--
theorem `map_pow` / 定理 `map_pow`

English:
theorem map_pow
  given: {A'} [Semiring A'] [Algebra R A'] (f : A ->ₐ[R] A') (n : Nat)
  proof: map_pow (mapHom f) M n

中文:
定理 map_pow
  条件: {A'} [半环 A'] [代数 R A'] (f : A ->ₐ[R] A') (n : 自然数)
  证明: map_pow (mapHom f) M n
-/
protected theorem map_pow {A'} [Semiring A'] [Algebra R A'] (f : A ->ₐ[R] A') (n : Nat) :
    map f.toLinearMap (M ^ n) = map f.toLinearMap M ^ n :=
  map_pow (mapHom f) M n

/--
theorem `comap_unop_pow` / 定理 `comap_unop_pow`

English:
theorem comap_unop_pow
  given: (n : Nat)
  proof: (equivOpposite : Submodule R Aᵐᵒᵖ ≃+* _).symm.map_pow (op M) n

中文:
定理 comap_unop_pow
  条件: (n : 自然数)
  证明: (equivOpposite : Submodule R Aᵐᵒᵖ ≃+* _).symm.map_pow (op M) n

Depends on / 依赖: Submodule, equivOpposite, map_pow, symm.map_pow
-/
theorem comap_unop_pow (n : Nat) :
    comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A) (M ^ n) =
      comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A) M ^ n :=
  (equivOpposite : Submodule R Aᵐᵒᵖ ≃+* _).symm.map_pow (op M) n

/--
theorem `comap_op_pow` / 定理 `comap_op_pow`

English:
theorem comap_op_pow
  given: (n : Nat) (M : Submodule R Aᵐᵒᵖ)
  proof: op_injective (equivOpposite : Submodule R Aᵐᵒᵖ ≃+* _).map_pow M n

中文:
定理 comap_op_pow
  条件: (n : 自然数) (M : 子模 R Aᵐᵒᵖ)
  证明: op_injective (equivOpposite : Submodule R Aᵐᵒᵖ ≃+* _).map_pow M n

Depends on / 依赖: Submodule, equivOpposite, map_pow, op_injective
-/
theorem comap_op_pow (n : Nat) (M : Submodule R Aᵐᵒᵖ) :
    comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) (M ^ n) =
      comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) M ^ n :=
op_injective (equivOpposite : Submodule R Aᵐᵒᵖ ≃+* _).map_pow M n

/--
theorem `map_op_pow` / 定理 `map_op_pow`

English:
theorem map_op_pow
  given: (n : Nat)
  proof: by
  rw [map_equiv_eq_comap_symm]; rw [map_equiv_eq_comap_symm]; rw [comap_unop_pow]

中文:
定理 map_op_pow
  条件: (n : 自然数)
  证明: by
  rw [map_equiv_eq_comap_symm]; rw [map_equiv_eq_comap_symm]; rw [comap_unop_pow]

Depends on / 依赖: comap_unop_pow, map_equiv_eq_comap_symm
-/
theorem map_op_pow (n : Nat) :
    map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) (M ^ n) =
      map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A ->ₗ[R] Aᵐᵒᵖ) M ^ n := by
  rw [map_equiv_eq_comap_symm]; rw [map_equiv_eq_comap_symm]; rw [comap_unop_pow]

/--
theorem `map_unop_pow` / 定理 `map_unop_pow`

English:
theorem map_unop_pow
  given: (n : Nat) (M : Submodule R Aᵐᵒᵖ)
  proof: by
  rw [← comap_equiv_eq_map_symm]; rw [← comap_equiv_eq_map_symm]; rw [comap_op_pow]

中文:
定理 map_unop_pow
  条件: (n : 自然数) (M : 子模 R Aᵐᵒᵖ)
  证明: by
  rw [← comap_equiv_eq_map_symm]; rw [← comap_equiv_eq_map_symm]; rw [comap_op_pow]

Depends on / 依赖: comap_equiv_eq_map_symm, comap_op_pow
-/
theorem map_unop_pow (n : Nat) (M : Submodule R Aᵐᵒᵖ) :
    map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A) (M ^ n) =
      map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ ->ₗ[R] A) M ^ n := by
  rw [← comap_equiv_eq_map_symm]; rw [← comap_equiv_eq_map_symm]; rw [comap_op_pow]

/-- `span` is a semiring homomorphism (recall multiplication is pointwise multiplication of subsets
on either side). -/
@[simps]
/--
Definition of `span.ringHom` / `span.ringHom` 的定义

English:
definition span.ringHom
  signature: : SetSemiring A ->+* Submodule R A where
  body: Submodule.span R (SetSemiring.down s)
  map_zero' := span_empty
  map_one' := one_eq_span.symm
  map_add' := span_union
  map_mul' s t := by simp_rw [SetSemiring.down_mul, span_mul_span]

中文:
定义 span.ringHom
  签名: : SetSemiring A ->+* 子模 R A where
  定义体: Submodule.span R (SetSemiring.down s)
  map_zero' := span_empty
  map_one' := one_eq_span.symm
  map_add' := span_union
  map_mul' s t := by simp_rw [SetSemiring.down_mul, span_mul_span]

Depends on / 依赖: SetSemiring, SetSemiring.down, Submodule, Submodule.span
-/
noncomputable def span.ringHom : SetSemiring A ->+* Submodule R A where
  toFun s := Submodule.span R (SetSemiring.down s)
  map_zero' := span_empty
  map_one' := one_eq_span.symm
  map_add' := span_union
  map_mul' s t := by simp_rw [SetSemiring.down_mul, span_mul_span]

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/--
Definition of `spanSingleton` / `spanSingleton` 的定义

English:
definition spanSingleton
  signature: : A ->*₀ Submodule R A where
  body: Submodule.span.ringHom.toMonoidHom.comp SetSemiring.singletonMonoidHom
  map_zero' := by simp [SetSemiring.singletonMonoidHom]

中文:
定义 spanSingleton
  签名: : A ->*₀ 子模 R A where
  定义体: Submodule.span.ringHom.toMonoidHom.comp SetSemiring.singletonMonoidHom
  map_zero' := by simp [SetSemiring.singletonMonoidHom]

Depends on / 依赖: SetSemiring, SetSemiring.singletonMonoidHom, Submodule, Submodule.span.ringHom.toMonoidHom.comp, ringHom, singletonMonoidHom, toMonoidHom
-/
noncomputable def spanSingleton : A ->*₀ Submodule R A where
  __ := Submodule.span.ringHom.toMonoidHom.comp SetSemiring.singletonMonoidHom
  map_zero' := by simp [SetSemiring.singletonMonoidHom]

/--
lemma `spanSingleton_apply` / 引理 `spanSingleton_apply`

English:
lemma spanSingleton_apply
  given: (x : A)
  statement: spanSingleton R x = Submodule.span R {x}
  proof: rfl

中文:
引理 spanSingleton_apply
  条件: (x : A)
  结论: spanSingleton R x = 子模.span R {x}
  证明: rfl
-/
@[simp] lemma spanSingleton_apply (x : A) : spanSingleton R x = Submodule.span R {x} := rfl

section FaithfulSMul

variable [FaithfulSMul R A]

/--
theorem `span_singleton_eq_one_iff` / 定理 `span_singleton_eq_one_iff`

English:
theorem span_singleton_eq_one_iff
  given: {x : A}
  statement: span R {x} = 1 ↔ exists r : Rˣ, x = algebraMap R A r where
  proof: by
    obtain ⟨r, rfl⟩ := mem_one.mp (h ▸ mem_span_singleton_self x)
    have ⟨r', eq⟩ := mem_span_singleton.mp (h ▸ algebraMap_mem 1)
    rw [Algebra.smul_def]; rw [← map_mul]; rw [(FaithfulSMul.algebraMap_injective R A).eq_iff] at eq
    exact ⟨.mkOfMulEqOne _ _ (mul_comm _ r ▸ eq), rfl⟩
  mpr := by rintro ⟨r, rfl⟩; exact span_singleton_algebraMap_of_isUnit r.isUnit

中文:
定理 span_singleton_eq_one_iff
  条件: {x : A}
  结论: span R {x} = 1 ↔ 存在 r : Rˣ, x = algebraMap R A r where
  证明: by
    obtain ⟨r, rfl⟩ := mem_one.mp (h ▸ mem_span_singleton_self x)
    have ⟨r', eq⟩ := mem_span_singleton.mp (h ▸ algebraMap_mem 1)
    rw [Algebra.smul_def]; rw [← map_mul]; rw [(FaithfulSMul.algebraMap_injective R A).eq_iff] at eq
    exact ⟨.mkOfMulEqOne _ _ (mul_comm _ r ▸ eq), rfl⟩
  mpr := by rintro ⟨r, rfl⟩; exact span_singleton_algebraMap_of_isUnit r.isUnit

Depends on / 依赖: Algebra, Algebra.smul_def, FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, algebraMap_mem, eq_iff, isUnit, map_mul, mem_one, mem_one.mp, mem_span_singleton, mem_span_singleton.mp, mem_span_singleton_self, mkOfMulEqOne, mul_comm, r.isUnit, smul_def, span_singleton_algebraMap_of_isUnit
-/
theorem span_singleton_eq_one_iff {x : A} : span R {x} = 1 ↔ exists r : Rˣ, x = algebraMap R A r where
  mp h := by
    obtain ⟨r, rfl⟩ := mem_one.mp (h ▸ mem_span_singleton_self x)
    have ⟨r', eq⟩ := mem_span_singleton.mp (h ▸ algebraMap_mem 1)
    rw [Algebra.smul_def]; rw [← map_mul]; rw [(FaithfulSMul.algebraMap_injective R A).eq_iff] at eq
    exact ⟨.mkOfMulEqOne _ _ (mul_comm _ r ▸ eq), rfl⟩
  mpr := by rintro ⟨r, rfl⟩; exact span_singleton_algebraMap_of_isUnit r.isUnit

/--
theorem `mker_spanSingleton` / 定理 `mker_spanSingleton`

English:
theorem mker_spanSingleton
  proof: by
  ext; simp_rw [Submonoid.mem_map, IsUnit.mem_submonoid_iff, IsUnit, existsAndEq, true_and, eq_comm]
  exact span_singleton_eq_one_iff

中文:
定理 mker_spanSingleton
  证明: by
  ext; simp_rw [Submonoid.mem_map, IsUnit.mem_submonoid_iff, IsUnit, existsAndEq, true_and, eq_comm]
  exact span_singleton_eq_one_iff

Depends on / 依赖: IsUnit, IsUnit.mem_submonoid_iff, Submonoid, Submonoid.mem_map, eq_comm, existsAndEq, mem_map, mem_submonoid_iff, simp_rw, span_singleton_eq_one_iff, true_and
-/
theorem mker_spanSingleton :
    MonoidHom.mker (Submodule.spanSingleton R) = (IsUnit.submonoid R).map (algebraMap R A) := by
  ext; simp_rw [Submonoid.mem_map, IsUnit.mem_submonoid_iff, IsUnit, existsAndEq, true_and, eq_comm]
  exact span_singleton_eq_one_iff

/-- Exactness of the sequence `1 → Rˣ → Aˣ → (Submodule R A)ˣ → Pic R → Pic A` at `Aˣ`.
See Exercise I.3.7(iv) in [Weibel2013] or Theorem 2.4 in [RobertsSingh1993]. -/
/--
theorem `ker_unitsMap_spanSingleton` / 定理 `ker_unitsMap_spanSingleton`

English:
theorem ker_unitsMap_spanSingleton
  proof: by
  ext; simpa [Units.ext_iff, eq_comm] using span_singleton_eq_one_iff

中文:
定理 ker_unitsMap_spanSingleton
  证明: by
  ext; simpa [Units.ext_iff, eq_comm] using span_singleton_eq_one_iff

Depends on / 依赖: Units.ext_iff, eq_comm, ext_iff, span_singleton_eq_one_iff
-/
theorem ker_unitsMap_spanSingleton :
    (Units.map (Submodule.spanSingleton R).toMonoidHom).ker =
    (Units.map (algebraMap R A).toMonoidHom).range := by
  ext; simpa [Units.ext_iff, eq_comm] using span_singleton_eq_one_iff

end FaithfulSMul

section

variable {α : Type*} [Monoid α] [MulSemiringAction α A] [SMulCommClass α R A]

/-- The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale.

This is a stronger version of `Submodule.pointwiseDistribMulAction`. -/
@[instance_reducible]
/--
Definition of `pointwiseMulSemiringAction` / `pointwiseMulSemiringAction` 的定义

English:
definition pointwiseMulSemiringAction
  signature: : MulSemiringAction α (Submodule R A) where
  body: Submodule.pointwiseDistribMulAction
smul_mul r x y := Submodule.map_mul x y MulSemiringAction.toAlgHom R A r
smul_one r := Submodule.map_one MulSemiringAction.toAlgHom R A r

scoped[Pointwise] attribute [instance] Submodule.pointwiseMulSemiringAction

中文:
定义 pointwiseMulSemiringAction
  签名: : MulSemiring作用 α (子模 R A) where
  定义体: Submodule.pointwiseDistribMulAction
smul_mul r x y := Submodule.map_mul x y MulSemiringAction.toAlgHom R A r
smul_one r := Submodule.map_one MulSemiringAction.toAlgHom R A r

scoped[Pointwise] attribute [instance] Submodule.pointwiseMulSemiringAction
-/
protected def pointwiseMulSemiringAction : MulSemiringAction α (Submodule R A) where
  __ := Submodule.pointwiseDistribMulAction
smul_mul r x y := Submodule.map_mul x y MulSemiringAction.toAlgHom R A r
smul_one r := Submodule.map_one MulSemiringAction.toAlgHom R A r

scoped[Pointwise] attribute [instance] Submodule.pointwiseMulSemiringAction

end

end AlgebraSemiring

section AlgebraCommSemiring

variable {A : Type v} [CommSemiring A] [Algebra R A]
variable {M N : Submodule R A} {m n : A}

/--
theorem `mul_mem_mul_rev` / 定理 `mul_mem_mul_rev`

English:
theorem mul_mem_mul_rev
  given: (hm : m in M) (hn : n in N)
  statement: n * m in M * N
  proof: mul_comm m n ▸ mul_mem_mul hm hn

中文:
定理 mul_mem_mul_rev
  条件: (hm : m in M) (hn : n in N)
  结论: n * m in M * N
  证明: mul_comm m n ▸ mul_mem_mul hm hn

Depends on / 依赖: mul_comm, mul_mem_mul
-/
theorem mul_mem_mul_rev (hm : m in M) (hn : n in N) : n * m in M * N :=
  mul_comm m n ▸ mul_mem_mul hm hn

variable (M N)

/--
theorem `mul_comm` / 定理 `mul_comm`

English:
theorem mul_comm
  statement: M * N = N * M
  proof: le_antisymm (mul_le.2 fun _r hrm _s hsn => mul_mem_mul_rev hsn hrm)
    (mul_le.2 fun _r hrn _s hsm => mul_mem_mul_rev hsm hrn)

中文:
定理 mul_comm
  结论: M * N = N * M
  证明: le_antisymm (mul_le.2 fun _r hrm _s hsn => mul_mem_mul_rev hsn hrm)
    (mul_le.2 fun _r hrn _s hsm => mul_mem_mul_rev hsm hrn)
-/
protected theorem mul_comm : M * N = N * M :=
  le_antisymm (mul_le.2 fun _r hrm _s hsn => mul_mem_mul_rev hsn hrm)
    (mul_le.2 fun _r hrn _s hsm => mul_mem_mul_rev hsm hrn)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IdemCommSemiring (Submodule R A)
  body: { Submodule.idemSemiring with mul_comm := Submodule.mul_comm }

中文:
实例 :
  签名: IdemCommSemiring (子模 R A)
  定义体: { Submodule.idemSemiring with mul_comm := Submodule.mul_comm }

Depends on / 依赖: Submodule, Submodule.idemSemiring, Submodule.mul_comm, idemSemiring, mul_comm
-/
instance : IdemCommSemiring (Submodule R A) :=
  { Submodule.idemSemiring with mul_comm := Submodule.mul_comm }

/--
theorem `prod_span` / 定理 `prod_span`

English:
theorem prod_span
  given: {ι : Type*} (s : Finset ι) (M : ι -> Set A)
  proof: by
  let := Classical.decEq ι
  refine Finset.induction_on s ?_ ?_
  · simp [one_eq_span, Set.singleton_one]
  · intro _ _ H ih
    rw [Finset.prod_insert H]; rw [Finset.prod_insert H]; rw [ih]; rw [span_mul_span]

中文:
定理 prod_span
  条件: {ι : 类型} (s : 有限集 ι) (M : ι -> 集合 A)
  证明: by
  let := Classical.decEq ι
  refine Finset.induction_on s ?_ ?_
  · simp [one_eq_span, Set.singleton_one]
  · intro _ _ H ih
    rw [Finset.prod_insert H]; rw [Finset.prod_insert H]; rw [ih]; rw [span_mul_span]

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.induction_on, Finset.prod_insert, Set.singleton_one, induction_on, one_eq_span, prod_insert, singleton_one, span_mul_span
-/
theorem prod_span {ι : Type*} (s : Finset ι) (M : ι -> Set A) :
    (∏ i in s, Submodule.span R (M i)) = Submodule.span R (∏ i in s, M i) := by
  let := Classical.decEq ι
  refine Finset.induction_on s ?_ ?_
  · simp [one_eq_span, Set.singleton_one]
  · intro _ _ H ih
    rw [Finset.prod_insert H]; rw [Finset.prod_insert H]; rw [ih]; rw [span_mul_span]

/--
theorem `prod_span_singleton` / 定理 `prod_span_singleton`

English:
theorem prod_span_singleton
  given: {ι : Type*} (s : Finset ι) (x : ι -> A)
  proof: by
  rw [prod_span]; rw [Set.finsetProd_singleton]

中文:
定理 prod_span_singleton
  条件: {ι : 类型} (s : 有限集 ι) (x : ι -> A)
  证明: by
  rw [prod_span]; rw [Set.finsetProd_singleton]

Depends on / 依赖: Set.finsetProd_singleton, finsetProd_singleton, prod_span
-/
theorem prod_span_singleton {ι : Type*} (s : Finset ι) (x : ι -> A) :
    (∏ i in s, span R ({x i} : Set A)) = span R {∏ i in s, x i} := by
  rw [prod_span]; rw [Set.finsetProd_singleton]

variable (R A)

/--
Instance `moduleSet` / 实例 `moduleSet`

English:
instance moduleSet
  signature: : Module (SetSemiring A) (Submodule R A) where
  body: span R (SetSemiring.down s) * P
  smul_add _ _ _ := mul_add _ _ _
  add_smul s t P := by
    simp_rw [HSMul.hSMul, SetSemiring.down_add, span_union, sup_mul, add_eq_sup]
  mul_smul s t P := by
    simp_rw [HSMul.hSMul, SetSemiring.down_mul, ← mul_assoc, span_mul_span]
  one_smul P := by
    simp_rw [HSMul.hSMul, SetSemiring.down_one, ← one_eq_span_one_set, one_mul]
  zero_smul P := by
    simp_rw [HSMul.hSMul, SetSemiring.down_zero, span_empty, bot_mul, bot_eq_zero]
  smul_zero _ := mul_bot _

中文:
实例 moduleSet
  签名: : 模 (SetSemiring A) (子模 R A) where
  定义体: span R (SetSemiring.down s) * P
  smul_add _ _ _ := mul_add _ _ _
  add_smul s t P := by
    simp_rw [HSMul.hSMul, SetSemiring.down_add, span_union, sup_mul, add_eq_sup]
  mul_smul s t P := by
    simp_rw [HSMul.hSMul, SetSemiring.down_mul, ← mul_assoc, span_mul_span]
  one_smul P := by
    simp_rw [HSMul.hSMul, SetSemiring.down_one, ← one_eq_span_one_set, one_mul]
  zero_smul P := by
    simp_rw [HSMul.hSMul, SetSemiring.down_zero, span_empty, bot_mul, bot_eq_zero]
  smul_zero _ := mul_bot _

Depends on / 依赖: SetSemiring, SetSemiring.down
-/
noncomputable instance moduleSet : Module (SetSemiring A) (Submodule R A) where
  smul s P := span R (SetSemiring.down s) * P
  smul_add _ _ _ := mul_add _ _ _
  add_smul s t P := by
    simp_rw [HSMul.hSMul, SetSemiring.down_add, span_union, sup_mul, add_eq_sup]
  mul_smul s t P := by
    simp_rw [HSMul.hSMul, SetSemiring.down_mul, ← mul_assoc, span_mul_span]
  one_smul P := by
    simp_rw [HSMul.hSMul, SetSemiring.down_one, ← one_eq_span_one_set, one_mul]
  zero_smul P := by
    simp_rw [HSMul.hSMul, SetSemiring.down_zero, span_empty, bot_mul, bot_eq_zero]
  smul_zero _ := mul_bot _

variable {R A}

/--
theorem `setSemiring_smul_def` / 定理 `setSemiring_smul_def`

English:
theorem setSemiring_smul_def
  given: (s : SetSemiring A) (P : Submodule R A)
  proof: rfl

中文:
定理 setSemiring_smul_def
  条件: (s : SetSemiring A) (P : 子模 R A)
  证明: rfl
-/
theorem setSemiring_smul_def (s : SetSemiring A) (P : Submodule R A) :
    s • P = span R (SetSemiring.down (α := A) s) * P :=
  rfl

/--
theorem `smul_le_smul` / 定理 `smul_le_smul`

English:
theorem smul_le_smul
  statement: {s t : SetSemiring A} {M N : Submodule R A}
  proof: mul_le_mul' (span_mono h₁) h₂

中文:
定理 smul_le_smul
  结论: {s t : SetSemiring A} {M N : 子模 R A}
  证明: mul_le_mul' (span_mono h₁) h₂

Depends on / 依赖: SetSemiring, SetSemiring.down, subseteq
-/
theorem smul_le_smul {s t : SetSemiring A} {M N : Submodule R A}
    (h₁ : SetSemiring.down (α := A) s subseteq SetSemiring.down (α := A) t)
    (h₂ : M <= N) : s • M <= t • N :=
  mul_le_mul' (span_mono h₁) h₂

/--
theorem `singleton_smul` / 定理 `singleton_smul`

English:
theorem singleton_smul
  given: (a : A) (M : Submodule R A)
  proof: by
  conv_lhs => rw [← span_eq M]
  rw [setSemiring_smul_def]; rw [SetSemiring.down_up]; rw [span_mul_span]; rw [singleton_mul]
  exact (map (LinearMap.mulLeft R a) M).span_eq

中文:
定理 singleton_smul
  条件: (a : A) (M : 子模 R A)
  证明: by
  conv_lhs => rw [← span_eq M]
  rw [setSemiring_smul_def]; rw [SetSemiring.down_up]; rw [span_mul_span]; rw [singleton_mul]
  exact (map (LinearMap.mulLeft R a) M).span_eq

Depends on / 依赖: LinearMap, LinearMap.mulLeft, SetSemiring, SetSemiring.down_up, conv_lhs, down_up, mulLeft, setSemiring_smul_def, singleton_mul, span_eq, span_mul_span
-/
theorem singleton_smul (a : A) (M : Submodule R A) :
    Set.up ({a} : Set A) • M = M.map (LinearMap.mulLeft R a) := by
  conv_lhs => rw [← span_eq M]
  rw [setSemiring_smul_def]; rw [SetSemiring.down_up]; rw [span_mul_span]; rw [singleton_mul]
  exact (map (LinearMap.mulLeft R a) M).span_eq

section Quotient

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Div (Submodule R A)
  body: ⟨fun I J =>
    { carrier := { x | forall y in J, x * y in I }
      zero_mem' := fun y _ => by
        rw [zero_mul]
        apply Submodule.zero_mem
      add_mem' := fun ha hb y hy => by
        rw [add_mul]
        exact Submodule.add_mem _ (ha _ hy) (hb _ hy)
      smul_mem' := fun r x hx y hy => by
        rw [Algebra.smul_mul_assoc]
        exact Submodule.smul_mem _ _ (hx _ hy) }⟩

中文:
实例 :
  签名: 除法 (子模 R A)
  定义体: ⟨fun I J =>
    { carrier := { x | forall y in J, x * y in I }
      zero_mem' := fun y _ => by
        rw [zero_mul]
        apply Submodule.zero_mem
      add_mem' := fun ha hb y hy => by
        rw [add_mul]
        exact Submodule.add_mem _ (ha _ hy) (hb _ hy)
      smul_mem' := fun r x hx y hy => by
        rw [Algebra.smul_mul_assoc]
        exact Submodule.smul_mem _ _ (hx _ hy) }⟩

Depends on / 依赖: Algebra, Algebra.smul_mul_assoc, Submodule, Submodule.add_mem, Submodule.smul_mem, Submodule.zero_mem, add_mem, add_mul, carrier, smul_mem, smul_mul_assoc, zero_mem, zero_mul
-/
instance : Div (Submodule R A) :=
  ⟨fun I J =>
    { carrier := { x | forall y in J, x * y in I }
      zero_mem' := fun y _ => by
        rw [zero_mul]
        apply Submodule.zero_mem
      add_mem' := fun ha hb y hy => by
        rw [add_mul]
        exact Submodule.add_mem _ (ha _ hy) (hb _ hy)
      smul_mem' := fun r x hx y hy => by
        rw [Algebra.smul_mul_assoc]
        exact Submodule.smul_mem _ _ (hx _ hy) }⟩

/--
theorem `mem_div_iff_forall_mul_mem` / 定理 `mem_div_iff_forall_mul_mem`

English:
theorem mem_div_iff_forall_mul_mem
  given: {x : A} {I J : Submodule R A}
  statement: x in I / J ↔ forall y in J, x * y in I
  proof: Iff.refl _

中文:
定理 mem_div_iff_对任意_mul_mem
  条件: {x : A} {I J : 子模 R A}
  结论: x in I / J ↔ 对任意 y in J, x * y in I
  证明: Iff.refl _

Depends on / 依赖: Iff.refl
-/
theorem mem_div_iff_forall_mul_mem {x : A} {I J : Submodule R A} : x in I / J ↔ forall y in J, x * y in I :=
  Iff.refl _

/--
theorem `mem_div_iff_smul_subset` / 定理 `mem_div_iff_smul_subset`

English:
theorem mem_div_iff_smul_subset
  given: {x : A} {I J : Submodule R A}
  statement: x in I / J ↔ x • (J : Set A) subseteq I
  proof: ⟨fun h y ⟨y', hy', xy'_eq_y⟩ => by rw [← xy'_eq_y]; exact h _ hy',
    fun h _ hy => h (Set.smul_mem_smul_set hy)⟩

中文:
定理 mem_div_iff_smul_subset
  条件: {x : A} {I J : 子模 R A}
  结论: x in I / J ↔ x • (J : 集合 A) subseteq I
  证明: ⟨fun h y ⟨y', hy', xy'_eq_y⟩ => by rw [← xy'_eq_y]; exact h _ hy',
    fun h _ hy => h (Set.smul_mem_smul_set hy)⟩

Depends on / 依赖: Set.smul_mem_smul_set, _eq_y, smul_mem_smul_set
-/
theorem mem_div_iff_smul_subset {x : A} {I J : Submodule R A} : x in I / J ↔ x • (J : Set A) subseteq I :=
  ⟨fun h y ⟨y', hy', xy'_eq_y⟩ => by rw [← xy'_eq_y]; exact h _ hy',
    fun h _ hy => h (Set.smul_mem_smul_set hy)⟩

/--
theorem `le_div_iff` / 定理 `le_div_iff`

English:
theorem le_div_iff
  given: {I J K : Submodule R A}
  statement: I <= J / K ↔ forall x in I, forall z in K, x * z in J
  proof: Iff.refl _

中文:
定理 le_div_iff
  条件: {I J K : 子模 R A}
  结论: I <= J / K ↔ 对任意 x in I, 对任意 z in K, x * z in J
  证明: Iff.refl _

Depends on / 依赖: Iff.refl
-/
theorem le_div_iff {I J K : Submodule R A} : I <= J / K ↔ forall x in I, forall z in K, x * z in J :=
  Iff.refl _

/--
theorem `le_div_iff_mul_le` / 定理 `le_div_iff_mul_le`

English:
theorem le_div_iff_mul_le
  given: {I J K : Submodule R A}
  statement: I <= J / K ↔ I * K <= J
  proof: by
  rw [le_div_iff]; rw [mul_le]

中文:
定理 le_div_iff_mul_le
  条件: {I J K : 子模 R A}
  结论: I <= J / K ↔ I * K <= J
  证明: by
  rw [le_div_iff]; rw [mul_le]

Depends on / 依赖: le_div_iff, mul_le
-/
theorem le_div_iff_mul_le {I J K : Submodule R A} : I <= J / K ↔ I * K <= J := by
  rw [le_div_iff]; rw [mul_le]

/--
theorem `one_le_one_div` / 定理 `one_le_one_div`

English:
theorem one_le_one_div
  given: {I : Submodule R A}
  statement: 1 <= 1 / I ↔ I <= 1
  proof: by
  rw [le_div_iff_mul_le]; rw [one_mul]

@[simp]

中文:
定理 one_le_one_div
  条件: {I : 子模 R A}
  结论: 1 <= 1 / I ↔ I <= 1
  证明: by
  rw [le_div_iff_mul_le]; rw [one_mul]

@[simp]

Depends on / 依赖: le_div_iff_mul_le, one_mul
-/
theorem one_le_one_div {I : Submodule R A} : 1 <= 1 / I ↔ I <= 1 := by
  rw [le_div_iff_mul_le]; rw [one_mul]

@[simp]
/--
theorem `one_mem_div` / 定理 `one_mem_div`

English:
theorem one_mem_div
  given: {I J : Submodule R A}
  statement: 1 in I / J ↔ J <= I
  proof: by
  rw [← one_le]; rw [le_div_iff_mul_le]; rw [one_mul]

中文:
定理 one_mem_div
  条件: {I J : 子模 R A}
  结论: 1 in I / J ↔ J <= I
  证明: by
  rw [← one_le]; rw [le_div_iff_mul_le]; rw [one_mul]

Depends on / 依赖: le_div_iff_mul_le, one_le, one_mul
-/
theorem one_mem_div {I J : Submodule R A} : 1 in I / J ↔ J <= I := by
  rw [← one_le]; rw [le_div_iff_mul_le]; rw [one_mul]

/--
theorem `le_self_mul_one_div` / 定理 `le_self_mul_one_div`

English:
theorem le_self_mul_one_div
  given: {I : Submodule R A} (hI : I <= 1)
  statement: I <= I * (1 / I)
  proof: by
  simpa using mul_le_mul_right (one_le_one_div.mpr hI) _

中文:
定理 le_self_mul_one_div
  条件: {I : 子模 R A} (hI : I <= 1)
  结论: I <= I * (1 / I)
  证明: by
  simpa using mul_le_mul_right (one_le_one_div.mpr hI) _

Depends on / 依赖: mul_le_mul_right, one_le_one_div, one_le_one_div.mpr
-/
theorem le_self_mul_one_div {I : Submodule R A} (hI : I <= 1) : I <= I * (1 / I) := by
  simpa using mul_le_mul_right (one_le_one_div.mpr hI) _

/--
theorem `mul_one_div_le_one` / 定理 `mul_one_div_le_one`

English:
theorem mul_one_div_le_one
  given: {I : Submodule R A}
  statement: I * (1 / I) <= 1
  proof: by
  rw [Submodule.mul_le]
  intro m hm n hn
  rw [Submodule.mem_div_iff_forall_mul_mem] at hn
  rw [mul_comm]
  exact hn m hm

@[simp]

中文:
定理 mul_one_div_le_one
  条件: {I : 子模 R A}
  结论: I * (1 / I) <= 1
  证明: by
  rw [Submodule.mul_le]
  intro m hm n hn
  rw [Submodule.mem_div_iff_forall_mul_mem] at hn
  rw [mul_comm]
  exact hn m hm

@[simp]

Depends on / 依赖: Submodule, Submodule.mem_div_iff_forall_mul_mem, Submodule.mul_le, mem_div_iff_forall_mul_mem, mul_comm, mul_le
-/
theorem mul_one_div_le_one {I : Submodule R A} : I * (1 / I) <= 1 := by
  rw [Submodule.mul_le]
  intro m hm n hn
  rw [Submodule.mem_div_iff_forall_mul_mem] at hn
  rw [mul_comm]
  exact hn m hm

@[simp]
/--
theorem `map_div` / 定理 `map_div`

English:
theorem map_div
  statement: {B : Type*} [CommSemiring B] [Algebra R B] (I J : Submodule R A)
  proof: by
  ext x
  simp only [mem_map, mem_div_iff_forall_mul_mem, AlgEquiv.toLinearMap_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨x * y, hx _ hy, map_mul h x y⟩
  · rintro hx
    refine ⟨h.symm x, fun z hz => ?_, h.apply_symm_apply x⟩
    obtain ⟨xz, xz_mem, hxz⟩ := hx (h z) ⟨z, hz, rfl⟩
    convert! xz_mem
    apply h.injective
    rw [map_mul]; rw [h.apply_symm_apply]; rw [hxz]

中文:
定理 map_div
  结论: {B : 类型} [交换半环 B] [代数 R B] (I J : 子模 R A)
  证明: by
  ext x
  simp only [mem_map, mem_div_iff_forall_mul_mem, AlgEquiv.toLinearMap_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨x * y, hx _ hy, map_mul h x y⟩
  · rintro hx
    refine ⟨h.symm x, fun z hz => ?_, h.apply_symm_apply x⟩
    obtain ⟨xz, xz_mem, hxz⟩ := hx (h z) ⟨z, hz, rfl⟩
    convert! xz_mem
    apply h.injective
    rw [map_mul]; rw [h.apply_symm_apply]; rw [hxz]
-/
protected theorem map_div {B : Type*} [CommSemiring B] [Algebra R B] (I J : Submodule R A)
    (h : A ≃ₐ[R] B) : (I / J).map h.toLinearMap = I.map h.toLinearMap / J.map h.toLinearMap := by
  ext x
  simp only [mem_map, mem_div_iff_forall_mul_mem, AlgEquiv.toLinearMap_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨x * y, hx _ hy, map_mul h x y⟩
  · rintro hx
    refine ⟨h.symm x, fun z hz => ?_, h.apply_symm_apply x⟩
    obtain ⟨xz, xz_mem, hxz⟩ := hx (h z) ⟨z, hz, rfl⟩
    convert! xz_mem
    apply h.injective
    rw [map_mul]; rw [h.apply_symm_apply]; rw [hxz]

end Quotient

end AlgebraCommSemiring

/--
theorem `restrictScalars_image_smul_eq` / 定理 `restrictScalars_image_smul_eq`

English:
theorem restrictScalars_image_smul_eq
  statement: {S M : Type*}
  proof: by
  refine le_antisymm (fun x x_in => ?_) (set_smul_le _ _ _ fun r x r_in x_in => ?_)
  · rw [restrictScalars_mem] at x_in
    refine set_smul_inductionOn x x_in ?_ ?_ (fun _ _ _ _ h h' => add_mem h h') (zero_mem _)
    · rintro _ x ⟨r, r_in, rfl⟩ x_in
      rw [algebraMap_smul]
      exact mem_set_smul_of_mem_mem r_in x_in
    · intro r y h h'
obtain ⟨c, c_supp, hc⟩ := (mem_set_smul ..).mp smul_mem _ r h
      simp only [hc, Finsupp.sum, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
      refine sum_mem fun u u_in => ?_
      obtain ⟨u, u_in', rfl⟩ := c_supp (Finset.mem_coe.mpr u_in)
      rw [algebraMap_smul]
      exact mem_set_smul_of_mem_mem u_in' (coe_mem (c ((algebraMap S R) u)))
  · rw [restrictScalars_mem, ← algebraMap_smul R r]
    exact mem_set_smul_of_mem_mem (Set.mem_image_of_mem _ r_in) x_in

中文:
定理 restrictScalars_image_smul_eq
  结论: {S M : 类型}
  证明: by
  refine le_antisymm (fun x x_in => ?_) (set_smul_le _ _ _ fun r x r_in x_in => ?_)
  · rw [restrictScalars_mem] at x_in
    refine set_smul_inductionOn x x_in ?_ ?_ (fun _ _ _ _ h h' => add_mem h h') (zero_mem _)
    · rintro _ x ⟨r, r_in, rfl⟩ x_in
      rw [algebraMap_smul]
      exact mem_set_smul_of_mem_mem r_in x_in
    · intro r y h h'
obtain ⟨c, c_supp, hc⟩ := (mem_set_smul ..).mp smul_mem _ r h
      simp only [hc, Finsupp.sum, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
      refine sum_mem fun u u_in => ?_
      obtain ⟨u, u_in', rfl⟩ := c_supp (Finset.mem_coe.mpr u_in)
      rw [algebraMap_smul]
      exact mem_set_smul_of_mem_mem u_in' (coe_mem (c ((algebraMap S R) u)))
  · rw [restrictScalars_mem, ← algebraMap_smul R r]
    exact mem_set_smul_of_mem_mem (Set.mem_image_of_mem _ r_in) x_in

Depends on / 依赖: AddSubmonoidClass, AddSubmonoidClass.coe_finsetSum, Finsupp, Finsupp.sum, SetLike, SetLike.val_smul, add_mem, algebraMap_smul, c_supp, coe_finsetSum, le_antisymm, mem_set_smul, mem_set_smul_of_mem_mem, r_in, restrictScalars_mem, set_smul_inductionOn, set_smul_le, smul_mem, sum_mem, u_in
-/
theorem restrictScalars_image_smul_eq {S M : Type*}
    [CommSemiring S] [Algebra S R]
    [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower S R M]
    (s : Set S) (N : Submodule R M) :
    (algebraMap S R '' s • N).restrictScalars S = s • N.restrictScalars S := by
  refine le_antisymm (fun x x_in => ?_) (set_smul_le _ _ _ fun r x r_in x_in => ?_)
  · rw [restrictScalars_mem] at x_in
    refine set_smul_inductionOn x x_in ?_ ?_ (fun _ _ _ _ h h' => add_mem h h') (zero_mem _)
    · rintro _ x ⟨r, r_in, rfl⟩ x_in
      rw [algebraMap_smul]
      exact mem_set_smul_of_mem_mem r_in x_in
    · intro r y h h'
obtain ⟨c, c_supp, hc⟩ := (mem_set_smul ..).mp smul_mem _ r h
      simp only [hc, Finsupp.sum, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
      refine sum_mem fun u u_in => ?_
      obtain ⟨u, u_in', rfl⟩ := c_supp (Finset.mem_coe.mpr u_in)
      rw [algebraMap_smul]
      exact mem_set_smul_of_mem_mem u_in' (coe_mem (c ((algebraMap S R) u)))
  · rw [restrictScalars_mem, ← algebraMap_smul R r]
    exact mem_set_smul_of_mem_mem (Set.mem_image_of_mem _ r_in) x_in

end Submodule
