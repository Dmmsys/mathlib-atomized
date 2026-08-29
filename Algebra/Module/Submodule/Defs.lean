/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Algebra.Group.Submonoid.Basic

/-!

# Submodules of a module

In this file we define

* `Submodule R M` : a subset of a `Module` `M` that contains zero and is closed with respect to
  addition and scalar multiplication.

* `Subspace k M` : an abbreviation for `Submodule` assuming that `k` is a `Field`.

## Tags

submodule, subspace, linear map
-/

@[expose] public section

assert_not_exists DivisionRing

open Function

universe u'' u' u v w

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

/--
Definition of `Submodule` / `Submodule` 的定义

English:
structure Submodule
  parameters: (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]
  extends: AddSubmonoid M, SubMulAction R M
  (no additional axioms)

中文:
结构 子模
  参数: (R : 类型u) (M : 类型v) [半环 R] [加法交换幺半群 M] [模 R M]
  继承: 加法子幺半群 M, SubMul作用 R M
  (无附加公理)
-/
structure Submodule (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] : Type v
    extends AddSubmonoid M, SubMulAction R M

/-- Reinterpret a `Submodule` as an `AddSubmonoid`. -/
add_decl_doc Submodule.toAddSubmonoid

/-- Reinterpret a `Submodule` as a `SubMulAction`. -/
add_decl_doc Submodule.toSubMulAction

namespace Submodule

variable [Semiring R] [AddCommMonoid M] [Module R M]

/--
Instance `setLike` / 实例 `setLike`

English:
instance setLike
  signature: : SetLike (Submodule R M) M where
  body: s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

中文:
实例 setLike
  签名: : 集合状 (子模 R M) M where
  定义体: s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

Depends on / 依赖: carrier, s.carrier
-/
instance setLike : SetLike (Submodule R M) M where
  coe s := s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.coe_injective h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Submodule R M)
  body: .ofSetLike (Submodule R M) M

initialize_simps_projections Submodule (carrier -> coe, as_prefix coe)

中文:
实例 :
  签名: 偏序 (子模 R M)
  定义体: .ofSetLike (Submodule R M) M

initialize_simps_projections Submodule (carrier -> coe, as_prefix coe)

Depends on / 依赖: Submodule, ofSetLike
-/
instance : PartialOrder (Submodule R M) := .ofSetLike (Submodule R M) M

initialize_simps_projections Submodule (carrier -> coe, as_prefix coe)

/--
lemma `carrier_eq_coe` / 引理 `carrier_eq_coe`

English:
lemma carrier_eq_coe
  given: (s : Submodule R M)
  statement: s.carrier = s
  proof: rfl

中文:
引理 carrier_eq_coe
  条件: (s : 子模 R M)
  结论: s.carrier = s
  证明: rfl
-/
@[simp] lemma carrier_eq_coe (s : Submodule R M) : s.carrier = s := rfl

/-- The actual `Submodule` obtained from an element of a `SMulMemClass` and `AddSubmonoidClass`. -/
@[simps]
/--
Definition of `ofClass` / `ofClass` 的定义

English:
definition ofClass
  signature: {S R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [SetLike S M]
  body: s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' := SMulMemClass.smul_mem

中文:
定义 ofClass
  签名: {S R M : 类型} [半环 R] [加法交换幺半群 M] [模 R M] [集合状 S M]
  定义体: s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' := SMulMemClass.smul_mem
-/
def ofClass {S R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [SetLike S M]
    [AddSubmonoidClass S M] [SMulMemClass S R M] (s : S) : Submodule R M where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' := SMulMemClass.smul_mem

/-- Construct a submodule from closure under two-element linear combinations.
I.e., a nonempty set closed under two-element linear combinations is a submodule. -/
@[simps]
/--
Definition of `ofLinearComb` / `ofLinearComb` 的定义

English:
definition ofLinearComb
  signature: (C : Set M) (nonempty : C.Nonempty)
  body: C
  zero_mem' := by
    obtain ⟨x, hx⟩ := nonempty
    simpa [zero_smul, add_zero] using linearComb x hx x hx 0 0
  add_mem' {x y} hx hy := by simpa [one_smul] using linearComb x hx y hy 1 1
  smul_mem' c x hx := by simpa using linearComb x hx x hx c 0

中文:
定义 ofLinearComb
  签名: (C : 集合 M) (nonempty : C.非空)
  定义体: C
  zero_mem' := by
    obtain ⟨x, hx⟩ := nonempty
    simpa [zero_smul, add_zero] using linearComb x hx x hx 0 0
  add_mem' {x y} hx hy := by simpa [one_smul] using linearComb x hx y hy 1 1
  smul_mem' c x hx := by simpa using linearComb x hx x hx c 0
-/
def ofLinearComb (C : Set M) (nonempty : C.Nonempty)
    (linearComb : forall x in C, forall y in C, forall a b : R, a • x + b • y in C) :
    Submodule R M where
  carrier := C
  zero_mem' := by
    obtain ⟨x, hx⟩ := nonempty
    simpa [zero_smul, add_zero] using linearComb x hx x hx 0 0
  add_mem' {x y} hx hy := by simpa [one_smul] using linearComb x hx y hy 1 1
  smul_mem' c x hx := by simpa using linearComb x hx x hx c 0

instance (priority := 100) : CanLift (Set M) (Submodule R M) (↑)
    (fun s => 0 in s ∧ (forall {x y}, x in s -> y in s -> x + y in s) ∧ forall (r : R) {x}, x in s -> r • x in s) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        smul_mem' := h.2.2 },
      rfl ⟩

/--
Instance `addSubmonoidClass` / 实例 `addSubmonoidClass`

English:
instance addSubmonoidClass
  signature: : AddSubmonoidClass (Submodule R M) M where
  body: AddSubmonoid.zero_mem' _
  add_mem := AddSubsemigroup.add_mem' _

中文:
实例 addSubmonoidClass
  签名: : 加法子幺半群类 (子模 R M) M where
  定义体: AddSubmonoid.zero_mem' _
  add_mem := AddSubsemigroup.add_mem' _

Depends on / 依赖: AddSubmonoid, AddSubmonoid.zero_mem, zero_mem
-/
instance addSubmonoidClass : AddSubmonoidClass (Submodule R M) M where
  zero_mem _ := AddSubmonoid.zero_mem' _
  add_mem := AddSubsemigroup.add_mem' _

/--
Instance `smulMemClass` / 实例 `smulMemClass`

English:
instance smulMemClass
  signature: : SMulMemClass (Submodule R M) R M where
  body: SubMulAction.smul_mem' s.toSubMulAction c h

@[simp]

中文:
实例 smulMemClass
  签名: : SMulMem类 (子模 R M) R M where
  定义体: SubMulAction.smul_mem' s.toSubMulAction c h

@[simp]

Depends on / 依赖: SubMulAction, SubMulAction.smul_mem, s.toSubMulAction, smul_mem, toSubMulAction
-/
instance smulMemClass : SMulMemClass (Submodule R M) R M where
  smul_mem {s} c _ h := SubMulAction.smul_mem' s.toSubMulAction c h

@[simp]
/--
theorem `mem_toAddSubmonoid` / 定理 `mem_toAddSubmonoid`

English:
theorem mem_toAddSubmonoid
  given: (p : Submodule R M) (x : M)
  statement: x in p.toAddSubmonoid ↔ x in p
  proof: Iff.rfl

中文:
定理 mem_toAddSubmonoid
  条件: (p : 子模 R M) (x : M)
  结论: x in p.toAddSubmonoid ↔ x in p
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_toAddSubmonoid (p : Submodule R M) (x : M) : x in p.toAddSubmonoid ↔ x in p :=
  Iff.rfl

variable {p q : Submodule R M}

@[simp]
/--
theorem `mem_mk` / 定理 `mem_mk`

English:
theorem mem_mk
  given: {S : AddSubmonoid M} {x : M} (h)
  statement: x in (⟨S, h⟩ : Submodule R M) ↔ x in S
  proof: Iff.rfl

@[simp]

中文:
定理 mem_mk
  条件: {S : 加法子幺半群 M} {x : M} (h)
  结论: x in (⟨S, h⟩ : 子模 R M) ↔ x in S
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk {S : AddSubmonoid M} {x : M} (h) : x in (⟨S, h⟩ : Submodule R M) ↔ x in S :=
  Iff.rfl

@[simp]
/--
theorem `coe_set_mk` / 定理 `coe_set_mk`

English:
theorem coe_set_mk
  given: (S : AddSubmonoid M) (h)
  statement: ((⟨S, h⟩ : Submodule R M) : Set M) = S
  proof: rfl

中文:
定理 coe_set_mk
  条件: (S : 加法子幺半群 M) (h)
  结论: ((⟨S, h⟩ : 子模 R M) : 集合 M) = S
  证明: rfl
-/
theorem coe_set_mk (S : AddSubmonoid M) (h) : ((⟨S, h⟩ : Submodule R M) : Set M) = S :=
  rfl

/--
theorem `eta` / 定理 `eta`

English:
theorem eta
  given: (h)
  statement: ({ p with smul_mem' := h } : Submodule R M) = p
  proof: rfl

@[simp]

中文:
定理 eta
  条件: (h)
  结论: ({ p with smul_mem' := h } : 子模 R M) = p
  证明: rfl

@[simp]
-/
@[simp] theorem eta (h) : ({ p with smul_mem' := h } : Submodule R M) = p :=
  rfl

@[simp]
/--
theorem `mk_le_mk` / 定理 `mk_le_mk`

English:
theorem mk_le_mk
  given: {S S' : AddSubmonoid M} (h h')
  proof: Iff.rfl

@[ext]

中文:
定理 mk_le_mk
  条件: {S S' : 加法子幺半群 M} (h h')
  证明: Iff.rfl

@[ext]

Depends on / 依赖: Iff.rfl
-/
theorem mk_le_mk {S S' : AddSubmonoid M} (h h') :
    (⟨S, h⟩ : Submodule R M) <= (⟨S', h'⟩ : Submodule R M) ↔ S <= S' :=
  Iff.rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (h : forall x, x in p ↔ x in q)
  statement: p = q
  proof: SetLike.ext h

中文:
定理 ext
  条件: (h : 对任意 x, x in p ↔ x in q)
  结论: p = q
  证明: SetLike.ext h

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext (h : forall x, x in p ↔ x in q) : p = q :=
  SetLike.ext h

/-- Copy of a submodule with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
@[simps]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (p : Submodule R M) (s : Set M) (hs : s = ↑p)
  body: s
  zero_mem' := by simp [hs]
  add_mem' := hs.symm ▸ p.add_mem'
  smul_mem' := by simpa [hs] using p.smul_mem'

中文:
定义 copy
  签名: (p : 子模 R M) (s : 集合 M) (hs : s = ↑p)
  定义体: s
  zero_mem' := by simp [hs]
  add_mem' := hs.symm ▸ p.add_mem'
  smul_mem' := by simpa [hs] using p.smul_mem'
-/
protected def copy (p : Submodule R M) (s : Set M) (hs : s = ↑p) : Submodule R M where
  carrier := s
  zero_mem' := by simp [hs]
  add_mem' := hs.symm ▸ p.add_mem'
  smul_mem' := by simpa [hs] using p.smul_mem'

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (S : Submodule R M) (s : Set M) (hs : s = ↑S)
  statement: S.copy s hs = S
  proof: SetLike.coe_injective hs

中文:
定理 copy_eq
  条件: (S : 子模 R M) (s : 集合 M) (hs : s = ↑S)
  结论: S.copy s hs = S
  证明: SetLike.coe_injective hs

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem copy_eq (S : Submodule R M) (s : Set M) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

/--
theorem `toAddSubmonoid_injective` / 定理 `toAddSubmonoid_injective`

English:
theorem toAddSubmonoid_injective
  statement: Injective (toAddSubmonoid : Submodule R M -> AddSubmonoid M)
  proof: fun p q h => SetLike.ext'_iff.2 (show (p.toAddSubmonoid : Set M) = q from SetLike.ext'_iff.1 h)

@[simp]

中文:
定理 toAddSubmonoid_injective
  结论: 单射 (toAddSubmonoid : 子模 R M -> 加法子幺半群 M)
  证明: fun p q h => SetLike.ext'_iff.2 (show (p.toAddSubmonoid : Set M) = q from SetLike.ext'_iff.1 h)

@[simp]

Depends on / 依赖: SetLike, SetLike.ext, _iff, p.toAddSubmonoid, toAddSubmonoid
-/
theorem toAddSubmonoid_injective : Injective (toAddSubmonoid : Submodule R M -> AddSubmonoid M) :=
  fun p q h => SetLike.ext'_iff.2 (show (p.toAddSubmonoid : Set M) = q from SetLike.ext'_iff.1 h)

@[simp]
/--
theorem `toAddSubmonoid_inj` / 定理 `toAddSubmonoid_inj`

English:
theorem toAddSubmonoid_inj
  statement: p.toAddSubmonoid = q.toAddSubmonoid ↔ p = q
  proof: toAddSubmonoid_injective.eq_iff

@[simp]

中文:
定理 toAddSubmonoid_inj
  结论: p.toAddSubmonoid = q.toAddSubmonoid ↔ p = q
  证明: toAddSubmonoid_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, toAddSubmonoid_injective, toAddSubmonoid_injective.eq_iff
-/
theorem toAddSubmonoid_inj : p.toAddSubmonoid = q.toAddSubmonoid ↔ p = q :=
  toAddSubmonoid_injective.eq_iff

@[simp]
/--
theorem `coe_toAddSubmonoid` / 定理 `coe_toAddSubmonoid`

English:
theorem coe_toAddSubmonoid
  given: (p : Submodule R M)
  statement: (p.toAddSubmonoid : Set M) = p
  proof: rfl

中文:
定理 coe_toAddSubmonoid
  条件: (p : 子模 R M)
  结论: (p.toAddSubmonoid : 集合 M) = p
  证明: rfl
-/
theorem coe_toAddSubmonoid (p : Submodule R M) : (p.toAddSubmonoid : Set M) = p :=
  rfl

/--
theorem `toSubMulAction_injective` / 定理 `toSubMulAction_injective`

English:
theorem toSubMulAction_injective
  statement: Injective (toSubMulAction : Submodule R M -> SubMulAction R M)
  proof: fun p q h => SetLike.ext'_iff.2 (show (p.toSubMulAction : Set M) = q from SetLike.ext'_iff.1 h)

中文:
定理 toSubMulAction_injective
  结论: 单射 (toSubMulAction : 子模 R M -> SubMul作用 R M)
  证明: fun p q h => SetLike.ext'_iff.2 (show (p.toSubMulAction : Set M) = q from SetLike.ext'_iff.1 h)

Depends on / 依赖: SetLike, SetLike.ext, _iff, p.toSubMulAction, toSubMulAction
-/
theorem toSubMulAction_injective : Injective (toSubMulAction : Submodule R M -> SubMulAction R M) :=
  fun p q h => SetLike.ext'_iff.2 (show (p.toSubMulAction : Set M) = q from SetLike.ext'_iff.1 h)

/--
theorem `toSubMulAction_inj` / 定理 `toSubMulAction_inj`

English:
theorem toSubMulAction_inj
  statement: p.toSubMulAction = q.toSubMulAction ↔ p = q
  proof: toSubMulAction_injective.eq_iff

@[simp]

中文:
定理 toSubMulAction_inj
  结论: p.toSubMulAction = q.toSubMulAction ↔ p = q
  证明: toSubMulAction_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, toSubMulAction_injective, toSubMulAction_injective.eq_iff
-/
theorem toSubMulAction_inj : p.toSubMulAction = q.toSubMulAction ↔ p = q :=
  toSubMulAction_injective.eq_iff

@[simp]
/--
theorem `coe_toSubMulAction` / 定理 `coe_toSubMulAction`

English:
theorem coe_toSubMulAction
  given: (p : Submodule R M)
  statement: (p.toSubMulAction : Set M) = p
  proof: rfl

中文:
定理 coe_toSubMulAction
  条件: (p : 子模 R M)
  结论: (p.toSubMulAction : 集合 M) = p
  证明: rfl
-/
theorem coe_toSubMulAction (p : Submodule R M) : (p.toSubMulAction : Set M) = p :=
  rfl

/--
Instance `decidableEq` / 实例 `decidableEq`

English:
instance decidableEq
  signature: : DecidableEq (Submodule R M)
  body: Classical.typeDecidableEq _

中文:
实例 decidableEq
  签名: : DecidableEq (子模 R M)
  定义体: Classical.typeDecidableEq _

Depends on / 依赖: Classical, Classical.typeDecidableEq, typeDecidableEq
-/
noncomputable instance decidableEq : DecidableEq (Submodule R M) := Classical.typeDecidableEq _

end Submodule

namespace SMulMemClass

variable [Semiring R] [AddCommMonoid M] [Module R M] {A : Type*} [SetLike A M]
  [AddSubmonoidClass A M] [SMulMemClass A R M] (S' : A)

-- Prefer subclasses of `Module` over `SMulMemClass`.
/-- A submodule of a `Module` is a `Module`. -/
instance (priority := 75) toModule : Module R S' := fast_instance%
  Subtype.coe_injective.module R (AddSubmonoidClass.subtype S') (SetLike.val_smul S')

/-- This can't be an instance because Lean wouldn't know how to find `R`, but we can still use
this to manually derive `Module` on specific types. -/
@[instance_reducible]
/--
Definition of `toModule'` / `toModule'` 的定义

English:
definition toModule'
  signature: (S R' R A : Type*) [Semiring R] [NonUnitalNonAssocSemiring A]
  body: haveI : SMulMemClass S R' A := SMulMemClass.ofIsScalarTower S R' R A
  SMulMemClass.toModule s

中文:
定义 toModule'
  签名: (S R' R A : 类型) [半环 R] [非幺非结合半环 A]
  定义体: haveI : SMulMemClass S R' A := SMulMemClass.ofIsScalarTower S R' R A
  SMulMemClass.toModule s

Depends on / 依赖: SMulMemClass, SMulMemClass.ofIsScalarTower, SMulMemClass.toModule, ofIsScalarTower, toModule
-/
def toModule' (S R' R A : Type*) [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [Semiring R'] [SMul R' R] [Module R' A] [IsScalarTower R' R A]
    [SetLike S A] [AddSubmonoidClass S A] [SMulMemClass S R A] (s : S) :
    Module R' s :=
  haveI : SMulMemClass S R' A := SMulMemClass.ofIsScalarTower S R' R A
  SMulMemClass.toModule s

end SMulMemClass

namespace Submodule

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M]

-- We can infer the module structure implicitly from the bundled submodule,
-- rather than via typeclass resolution.
variable {module_M : Module R M}
variable {p q : Submodule R M}
variable {r : R} {x y : M}
variable (p)

/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  statement: x in p.carrier ↔ x in (p : Set M)
  proof: Iff.rfl

中文:
定理 mem_carrier
  结论: x in p.carrier ↔ x in (p : 集合 M)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier : x in p.carrier ↔ x in (p : Set M) :=
  Iff.rfl

/--
theorem `zero_mem` / 定理 `zero_mem`

English:
theorem zero_mem
  statement: (0 : M) in p
  proof: zero_mem _

中文:
定理 zero_mem
  结论: (0 : M) in p
  证明: zero_mem _
-/
protected theorem zero_mem : (0 : M) in p :=
  zero_mem _

/--
theorem `add_mem` / 定理 `add_mem`

English:
theorem add_mem
  given: (h₁ : x in p) (h₂ : y in p)
  statement: x + y in p
  proof: add_mem h₁ h₂

中文:
定理 add_mem
  条件: (h₁ : x in p) (h₂ : y in p)
  结论: x + y in p
  证明: add_mem h₁ h₂
-/
protected theorem add_mem (h₁ : x in p) (h₂ : y in p) : x + y in p :=
  add_mem h₁ h₂

/--
theorem `smul_mem` / 定理 `smul_mem`

English:
theorem smul_mem
  given: (r : R) (h : x in p)
  statement: r • x in p
  proof: p.smul_mem' r h

中文:
定理 smul_mem
  条件: (r : R) (h : x in p)
  结论: r • x in p
  证明: p.smul_mem' r h

Depends on / 依赖: p.smul_mem, smul_mem
-/
theorem smul_mem (r : R) (h : x in p) : r • x in p :=
  p.smul_mem' r h

/--
theorem `smul_of_tower_mem` / 定理 `smul_of_tower_mem`

English:
theorem smul_of_tower_mem
  given: [SMul S R] [SMul S M] [IsScalarTower S R M] (r : S) (h : x in p)
  proof: p.toSubMulAction.smul_of_tower_mem r h

@[simp]

中文:
定理 smul_of_tower_mem
  条件: [标量乘法 S R] [标量乘法 S M] [标量塔 S R M] (r : S) (h : x in p)
  证明: p.toSubMulAction.smul_of_tower_mem r h

@[simp]

Depends on / 依赖: p.toSubMulAction.smul_of_tower_mem, smul_of_tower_mem, toSubMulAction
-/
theorem smul_of_tower_mem [SMul S R] [SMul S M] [IsScalarTower S R M] (r : S) (h : x in p) :
    r • x in p :=
  p.toSubMulAction.smul_of_tower_mem r h

@[simp]
/--
theorem `smul_mem_iff'` / 定理 `smul_mem_iff'`

English:
theorem smul_mem_iff'
  given: [Group G] [MulAction G M] [SMul G R] [IsScalarTower G R M] (g : G)
  proof: p.toSubMulAction.smul_mem_iff' g

@[simp]

中文:
定理 smul_mem_iff'
  条件: [群 G] [乘法作用 G M] [标量乘法 G R] [标量塔 G R M] (g : G)
  证明: p.toSubMulAction.smul_mem_iff' g

@[simp]

Depends on / 依赖: p.toSubMulAction.smul_mem_iff, smul_mem_iff, toSubMulAction
-/
theorem smul_mem_iff' [Group G] [MulAction G M] [SMul G R] [IsScalarTower G R M] (g : G) :
    g • x in p ↔ x in p :=
  p.toSubMulAction.smul_mem_iff' g

@[simp]
/--
lemma `smul_mem_iff''` / 引理 `smul_mem_iff''`

English:
lemma smul_mem_iff''
  given: [Invertible r]
  proof: by
  refine ⟨fun h => ?_, p.smul_mem r⟩
  rw [← invOf_smul_smul r x]
  exact p.smul_mem _ h

中文:
引理 smul_mem_iff''
  条件: [可逆 r]
  证明: by
  refine ⟨fun h => ?_, p.smul_mem r⟩
  rw [← invOf_smul_smul r x]
  exact p.smul_mem _ h

Depends on / 依赖: invOf_smul_smul, p.smul_mem, smul_mem
-/
lemma smul_mem_iff'' [Invertible r] :
    r • x in p ↔ x in p := by
  refine ⟨fun h => ?_, p.smul_mem r⟩
  rw [← invOf_smul_smul r x]
  exact p.smul_mem _ h

/--
lemma `smul_mem_iff_of_isUnit` / 引理 `smul_mem_iff_of_isUnit`

English:
lemma smul_mem_iff_of_isUnit
  given: (hr : IsUnit r)
  proof: let _ : Invertible r := hr.invertible
  smul_mem_iff'' p

中文:
引理 smul_mem_iff_of_isUnit
  条件: (hr : 是单位 r)
  证明: let _ : Invertible r := hr.invertible
  smul_mem_iff'' p

Depends on / 依赖: Invertible, hr.invertible, invertible, smul_mem_iff
-/
lemma smul_mem_iff_of_isUnit (hr : IsUnit r) :
    r • x in p ↔ x in p :=
  let _ : Invertible r := hr.invertible
  smul_mem_iff'' p

/--
Instance `add` / 实例 `add`

English:
instance add
  signature: : Add p
  body: ⟨fun x y => ⟨x.1 + y.1, add_mem x.2 y.2⟩⟩

中文:
实例 add
  签名: : 加法 p
  定义体: ⟨fun x y => ⟨x.1 + y.1, add_mem x.2 y.2⟩⟩

Depends on / 依赖: add_mem
-/
instance add : Add p :=
  ⟨fun x y => ⟨x.1 + y.1, add_mem x.2 y.2⟩⟩

/--
Instance `zero` / 实例 `zero`

English:
instance zero
  signature: : Zero p
  body: ⟨⟨0, zero_mem _⟩⟩

中文:
实例 zero
  签名: : 零 p
  定义体: ⟨⟨0, zero_mem _⟩⟩

Depends on / 依赖: zero_mem
-/
instance zero : Zero p :=
  ⟨⟨0, zero_mem _⟩⟩

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: : Inhabited p
  body: ⟨0⟩

中文:
实例 inhabited
  签名: : 可居 p
  定义体: ⟨0⟩
-/
instance inhabited : Inhabited p :=
  ⟨0⟩

/--
Instance `smul` / 实例 `smul`

English:
instance smul
  signature: [SMul S R] [SMul S M] [IsScalarTower S R M]
  body: ⟨fun c x => ⟨c • x.1, smul_of_tower_mem _ c x.2⟩⟩

中文:
实例 smul
  签名: [标量乘法 S R] [标量乘法 S M] [标量塔 S R M]
  定义体: ⟨fun c x => ⟨c • x.1, smul_of_tower_mem _ c x.2⟩⟩

Depends on / 依赖: smul_of_tower_mem
-/
instance smul [SMul S R] [SMul S M] [IsScalarTower S R M] : SMul S p :=
  ⟨fun c x => ⟨c • x.1, smul_of_tower_mem _ c x.2⟩⟩

/--
Instance `isScalarTower` / 实例 `isScalarTower`

English:
instance isScalarTower
  signature: [SMul S R] [SMul S M] [IsScalarTower S R M]
  body: p.toSubMulAction.isScalarTower

中文:
实例 isScalarTower
  签名: [标量乘法 S R] [标量乘法 S M] [标量塔 S R M]
  定义体: p.toSubMulAction.isScalarTower

Depends on / 依赖: isScalarTower, p.toSubMulAction.isScalarTower, toSubMulAction
-/
instance isScalarTower [SMul S R] [SMul S M] [IsScalarTower S R M] : IsScalarTower S R p :=
  p.toSubMulAction.isScalarTower

/--
Instance `isScalarTower'` / 实例 `isScalarTower'`

English:
instance isScalarTower'
  signature: {S' : Type*} [SMul S R] [SMul S M] [SMul S' R] [SMul S' M] [SMul S S']
  body: p.toSubMulAction.isScalarTower'

中文:
实例 isScalarTower'
  签名: {S' : 类型} [标量乘法 S R] [标量乘法 S M] [标量乘法 S' R] [标量乘法 S' M] [标量乘法 S S']
  定义体: p.toSubMulAction.isScalarTower'

Depends on / 依赖: isScalarTower, p.toSubMulAction.isScalarTower, toSubMulAction
-/
instance isScalarTower' {S' : Type*} [SMul S R] [SMul S M] [SMul S' R] [SMul S' M] [SMul S S']
    [IsScalarTower S' R M] [IsScalarTower S S' M] [IsScalarTower S R M] : IsScalarTower S S' p :=
  p.toSubMulAction.isScalarTower'

/--
theorem `nonempty` / 定理 `nonempty`

English:
theorem nonempty
  statement: (p : Set M).Nonempty
  proof: ⟨0, p.zero_mem⟩

@[simp]

中文:
定理 nonempty
  结论: (p : 集合 M).非空
  证明: ⟨0, p.zero_mem⟩

@[simp]
-/
protected theorem nonempty : (p : Set M).Nonempty :=
  ⟨0, p.zero_mem⟩

@[simp]
/--
theorem `mk_eq_zero` / 定理 `mk_eq_zero`

English:
theorem mk_eq_zero
  given: {x} (h : x in p)
  statement: (⟨x, h⟩ : p) = 0 ↔ x = 0
  proof: Subtype.ext_iff

中文:
定理 mk_eq_zero
  条件: {x} (h : x in p)
  结论: (⟨x, h⟩ : p) = 0 ↔ x = 0
  证明: Subtype.ext_iff

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff
-/
theorem mk_eq_zero {x} (h : x in p) : (⟨x, h⟩ : p) = 0 ↔ x = 0 :=
  Subtype.ext_iff

variable {p}

@[norm_cast]
/--
theorem `coe_eq_zero` / 定理 `coe_eq_zero`

English:
theorem coe_eq_zero
  given: {x : p}
  statement: (x : M) = 0 ↔ x = 0
  proof: (SetLike.coe_eq_coe : (x : M) = (0 : p) ↔ x = 0)

@[simp, norm_cast]

中文:
定理 coe_eq_zero
  条件: {x : p}
  结论: (x : M) = 0 ↔ x = 0
  证明: (SetLike.coe_eq_coe : (x : M) = (0 : p) ↔ x = 0)

@[simp, norm_cast]

Depends on / 依赖: SetLike, SetLike.coe_eq_coe, coe_eq_coe
-/
theorem coe_eq_zero {x : p} : (x : M) = 0 ↔ x = 0 :=
  (SetLike.coe_eq_coe : (x : M) = (0 : p) ↔ x = 0)

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (x y : p)
  statement: (↑(x + y) : M) = ↑x + ↑y
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_add
  条件: (x y : p)
  结论: (↑(x + y) : M) = ↑x + ↑y
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_add (x y : p) : (↑(x + y) : M) = ↑x + ↑y :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : p) : M) = 0
  proof: rfl

@[norm_cast]

中文:
定理 coe_zero
  结论: ((0 : p) : M) = 0
  证明: rfl

@[norm_cast]
-/
theorem coe_zero : ((0 : p) : M) = 0 :=
  rfl

@[norm_cast]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (r : R) (x : p)
  statement: ((r • x : p) : M) = r • (x : M)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_smul
  条件: (r : R) (x : p)
  结论: ((r • x : p) : M) = r • (x : M)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_smul (r : R) (x : p) : ((r • x : p) : M) = r • (x : M) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_smul_of_tower` / 定理 `coe_smul_of_tower`

English:
theorem coe_smul_of_tower
  given: [SMul S R] [SMul S M] [IsScalarTower S R M] (r : S) (x : p)
  proof: rfl

@[norm_cast]

中文:
定理 coe_smul_of_tower
  条件: [标量乘法 S R] [标量乘法 S M] [标量塔 S R M] (r : S) (x : p)
  证明: rfl

@[norm_cast]
-/
theorem coe_smul_of_tower [SMul S R] [SMul S M] [IsScalarTower S R M] (r : S) (x : p) :
    ((r • x : p) : M) = r • (x : M) :=
  rfl

@[norm_cast]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (x : M) (hx : x in p)
  statement: ((⟨x, hx⟩ : p) : M) = x
  proof: rfl

中文:
定理 coe_mk
  条件: (x : M) (hx : x in p)
  结论: ((⟨x, hx⟩ : p) : M) = x
  证明: rfl
-/
theorem coe_mk (x : M) (hx : x in p) : ((⟨x, hx⟩ : p) : M) = x :=
  rfl

/--
theorem `coe_mem` / 定理 `coe_mem`

English:
theorem coe_mem
  given: (x : p)
  statement: (x : M) in p
  proof: x.2

中文:
定理 coe_mem
  条件: (x : p)
  结论: (x : M) in p
  证明: x.2
-/
theorem coe_mem (x : p) : (x : M) in p :=
  x.2

variable (p)

/--
Instance `addCommMonoid` / 实例 `addCommMonoid`

English:
instance addCommMonoid
  signature: : AddCommMonoid p
  body: AddSubmonoidClass.toAddCommMonoid p

中文:
实例 addCommMonoid
  签名: : 加法交换幺半群 p
  定义体: AddSubmonoidClass.toAddCommMonoid p

Depends on / 依赖: AddSubmonoidClass, AddSubmonoidClass.toAddCommMonoid, toAddCommMonoid
-/
instance addCommMonoid : AddCommMonoid p := AddSubmonoidClass.toAddCommMonoid p

/--
Instance `module'` / 实例 `module'`

English:
instance module'
  signature: [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M]
  body: fast_instance%
  { (show MulAction S p from p.toSubMulAction.mulAction') with
    smul_zero := fun a => by ext; simp
    zero_smul := fun a => by ext; simp
    add_smul := fun a b x => by ext; simp [add_smul]
    smul_add := fun a x y => by ext; simp [smul_add] }

中文:
实例 module'
  签名: [半环 S] [标量乘法 S R] [模 S M] [标量塔 S R M]
  定义体: fast_instance%
  { (show MulAction S p from p.toSubMulAction.mulAction') with
    smul_zero := fun a => by ext; simp
    zero_smul := fun a => by ext; simp
    add_smul := fun a b x => by ext; simp [add_smul]
    smul_add := fun a x y => by ext; simp [smul_add] }

Depends on / 依赖: fast_instance
-/
instance module' [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] :
    Module S p := fast_instance%
  { (show MulAction S p from p.toSubMulAction.mulAction') with
    smul_zero := fun a => by ext; simp
    zero_smul := fun a => by ext; simp
    add_smul := fun a b x => by ext; simp [add_smul]
    smul_add := fun a x y => by ext; simp [smul_add] }

/--
Instance `module` / 实例 `module`

English:
instance module
  signature: : Module R p
  body: p.module'

中文:
实例 module
  签名: : 模 R p
  定义体: p.module'

Depends on / 依赖: module, p.module
-/
instance module : Module R p :=
  p.module'

end AddCommMonoid

section AddCommGroup

variable [Ring R] [AddCommGroup M]
variable {module_M : Module R M}
variable (p p' : Submodule R M)
variable {r : R} {x y : M}

/--
Instance `addSubgroupClass` / 实例 `addSubgroupClass`

English:
instance addSubgroupClass
  signature: [Module R M]
  body: { Submodule.addSubmonoidClass with neg_mem := fun p {_} => p.toSubMulAction.neg_mem }

中文:
实例 addSubgroupClass
  签名: [模 R M]
  定义体: { Submodule.addSubmonoidClass with neg_mem := fun p {_} => p.toSubMulAction.neg_mem }

Depends on / 依赖: Submodule, Submodule.addSubmonoidClass, addSubmonoidClass, neg_mem, p.toSubMulAction.neg_mem, toSubMulAction
-/
instance addSubgroupClass [Module R M] : AddSubgroupClass (Submodule R M) M :=
  { Submodule.addSubmonoidClass with neg_mem := fun p {_} => p.toSubMulAction.neg_mem }

/--
theorem `neg_mem` / 定理 `neg_mem`

English:
theorem neg_mem
  given: (hx : x in p)
  statement: -x in p
  proof: neg_mem hx

中文:
定理 neg_mem
  条件: (hx : x in p)
  结论: -x in p
  证明: neg_mem hx
-/
protected theorem neg_mem (hx : x in p) : -x in p :=
  neg_mem hx

/-- Reinterpret a submodule as an additive subgroup. -/
@[reducible]
/--
Definition of `toAddSubgroup` / `toAddSubgroup` 的定义

English:
definition toAddSubgroup
  signature: : AddSubgroup M
  body: { p.toAddSubmonoid with neg_mem' := fun {_} => p.neg_mem }

@[simp]

中文:
定义 toAddSubgroup
  签名: : 加法子群 M
  定义体: { p.toAddSubmonoid with neg_mem' := fun {_} => p.neg_mem }

@[simp]

Depends on / 依赖: neg_mem, p.neg_mem, p.toAddSubmonoid, toAddSubmonoid
-/
def toAddSubgroup : AddSubgroup M :=
  { p.toAddSubmonoid with neg_mem' := fun {_} => p.neg_mem }

@[simp]
/--
theorem `coe_toAddSubgroup` / 定理 `coe_toAddSubgroup`

English:
theorem coe_toAddSubgroup
  statement: (p.toAddSubgroup : Set M) = p
  proof: rfl

中文:
定理 coe_toAddSubgroup
  结论: (p.toAddSubgroup : 集合 M) = p
  证明: rfl
-/
theorem coe_toAddSubgroup : (p.toAddSubgroup : Set M) = p :=
  rfl

/--
theorem `mem_toAddSubgroup` / 定理 `mem_toAddSubgroup`

English:
theorem mem_toAddSubgroup
  statement: x in p.toAddSubgroup ↔ x in p
  proof: Iff.rfl

中文:
定理 mem_toAddSubgroup
  结论: x in p.toAddSubgroup ↔ x in p
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_toAddSubgroup : x in p.toAddSubgroup ↔ x in p :=
  Iff.rfl

/--
theorem `toAddSubgroup_injective` / 定理 `toAddSubgroup_injective`

English:
theorem toAddSubgroup_injective
  statement: Injective (toAddSubgroup : Submodule R M -> AddSubgroup M)

中文:
定理 toAddSubgroup_injective
  结论: 单射 (toAddSubgroup : 子模 R M -> 加法子群 M)
-/
theorem toAddSubgroup_injective : Injective (toAddSubgroup : Submodule R M -> AddSubgroup M)
  | _, _, h => SetLike.ext (SetLike.ext_iff.1 h :)

/--
theorem `toAddSubgroup_inj` / 定理 `toAddSubgroup_inj`

English:
theorem toAddSubgroup_inj
  statement: p.toAddSubgroup = p'.toAddSubgroup ↔ p = p'
  proof: toAddSubgroup_injective.eq_iff

中文:
定理 toAddSubgroup_inj
  结论: p.toAddSubgroup = p'.toAddSubgroup ↔ p = p'
  证明: toAddSubgroup_injective.eq_iff

Depends on / 依赖: eq_iff, toAddSubgroup_injective, toAddSubgroup_injective.eq_iff
-/
theorem toAddSubgroup_inj : p.toAddSubgroup = p'.toAddSubgroup ↔ p = p' :=
  toAddSubgroup_injective.eq_iff

/--
theorem `sub_mem` / 定理 `sub_mem`

English:
theorem sub_mem
  statement: x in p -> y in p -> x - y in p
  proof: sub_mem

中文:
定理 sub_mem
  结论: x in p -> y in p -> x - y in p
  证明: sub_mem
-/
protected theorem sub_mem : x in p -> y in p -> x - y in p :=
  sub_mem

/--
theorem `neg_mem_iff` / 定理 `neg_mem_iff`

English:
theorem neg_mem_iff
  statement: -x in p ↔ x in p
  proof: neg_mem_iff

中文:
定理 neg_mem_iff
  结论: -x in p ↔ x in p
  证明: neg_mem_iff
-/
protected theorem neg_mem_iff : -x in p ↔ x in p :=
  neg_mem_iff

/--
theorem `add_mem_iff_left` / 定理 `add_mem_iff_left`

English:
theorem add_mem_iff_left
  statement: y in p -> (x + y in p ↔ x in p)
  proof: add_mem_cancel_right

中文:
定理 add_mem_iff_left
  结论: y in p -> (x + y in p ↔ x in p)
  证明: add_mem_cancel_right
-/
protected theorem add_mem_iff_left : y in p -> (x + y in p ↔ x in p) :=
  add_mem_cancel_right

/--
theorem `add_mem_iff_right` / 定理 `add_mem_iff_right`

English:
theorem add_mem_iff_right
  statement: x in p -> (x + y in p ↔ y in p)
  proof: add_mem_cancel_left

中文:
定理 add_mem_iff_right
  结论: x in p -> (x + y in p ↔ y in p)
  证明: add_mem_cancel_left
-/
protected theorem add_mem_iff_right : x in p -> (x + y in p ↔ y in p) :=
  add_mem_cancel_left

/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (x : p)
  statement: ((-x : p) : M) = -x
  proof: NegMemClass.coe_neg _

中文:
定理 coe_neg
  条件: (x : p)
  结论: ((-x : p) : M) = -x
  证明: NegMemClass.coe_neg _
-/
protected theorem coe_neg (x : p) : ((-x : p) : M) = -x :=
  NegMemClass.coe_neg _

/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (x y : p)
  statement: (↑(x - y) : M) = ↑x - ↑y
  proof: AddSubgroupClass.coe_sub _ _

中文:
定理 coe_sub
  条件: (x y : p)
  结论: (↑(x - y) : M) = ↑x - ↑y
  证明: AddSubgroupClass.coe_sub _ _
-/
protected theorem coe_sub (x y : p) : (↑(x - y) : M) = ↑x - ↑y :=
  AddSubgroupClass.coe_sub _ _

/--
theorem `sub_mem_iff_left` / 定理 `sub_mem_iff_left`

English:
theorem sub_mem_iff_left
  given: (hy : y in p)
  statement: x - y in p ↔ x in p
  proof: by
  rw [sub_eq_add_neg]; rw [p.add_mem_iff_left (p.neg_mem hy)]

中文:
定理 sub_mem_iff_left
  条件: (hy : y in p)
  结论: x - y in p ↔ x in p
  证明: by
  rw [sub_eq_add_neg]; rw [p.add_mem_iff_left (p.neg_mem hy)]

Depends on / 依赖: add_mem_iff_left, neg_mem, p.add_mem_iff_left, p.neg_mem, sub_eq_add_neg
-/
theorem sub_mem_iff_left (hy : y in p) : x - y in p ↔ x in p := by
  rw [sub_eq_add_neg]; rw [p.add_mem_iff_left (p.neg_mem hy)]

/--
theorem `sub_mem_iff_right` / 定理 `sub_mem_iff_right`

English:
theorem sub_mem_iff_right
  given: (hx : x in p)
  statement: x - y in p ↔ y in p
  proof: by
  rw [sub_eq_add_neg]; rw [p.add_mem_iff_right hx]; rw [p.neg_mem_iff]

中文:
定理 sub_mem_iff_right
  条件: (hx : x in p)
  结论: x - y in p ↔ y in p
  证明: by
  rw [sub_eq_add_neg]; rw [p.add_mem_iff_right hx]; rw [p.neg_mem_iff]

Depends on / 依赖: add_mem_iff_right, neg_mem_iff, p.add_mem_iff_right, p.neg_mem_iff, sub_eq_add_neg
-/
theorem sub_mem_iff_right (hx : x in p) : x - y in p ↔ y in p := by
  rw [sub_eq_add_neg]; rw [p.add_mem_iff_right hx]; rw [p.neg_mem_iff]

/--
Instance `addCommGroup` / 实例 `addCommGroup`

English:
instance addCommGroup
  signature: : AddCommGroup p
  body: AddSubgroupClass.toAddCommGroup p

中文:
实例 addCommGroup
  签名: : 加法交换群 p
  定义体: AddSubgroupClass.toAddCommGroup p

Depends on / 依赖: AddSubgroupClass, AddSubgroupClass.toAddCommGroup, toAddCommGroup
-/
instance addCommGroup : AddCommGroup p := AddSubgroupClass.toAddCommGroup p

end AddCommGroup

end Submodule

namespace SubmoduleClass

instance (priority := 75) module' {T : Type*} [Semiring R] [AddCommMonoid M] [Semiring S]
    [Module R M] [SMul S R] [Module S M] [IsScalarTower S R M] [SetLike T M] [AddSubmonoidClass T M]
    [SMulMemClass T R M] (t : T) : Module S t where
  one_smul _ := by ext; simp
  mul_smul _ _ _ := by ext; simp [mul_smul]
  smul_zero _ := by ext; simp
  zero_smul _ := by ext; simp
  add_smul _ _ _ := by ext; simp [add_smul]
  smul_add _ _ _ := by ext; simp [smul_add]

instance (priority := 75) module [Semiring R] [AddCommMonoid M] [Module R M] [SetLike S M]
    [AddSubmonoidClass S M] [SMulMemClass S R M] (s : S) : Module R s :=
  module' s

end SubmoduleClass
