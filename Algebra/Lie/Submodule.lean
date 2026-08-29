/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.LinearAlgebra.Finsupp.Span

/-!
# Lie submodules of a Lie algebra

In this file we define Lie submodules, we construct the lattice structure on Lie submodules and we
use it to define various important operations, notably the Lie span of a subset of a Lie module.

## Main definitions

  * `LieSubmodule`
  * `LieSubmodule.wellFounded_of_noetherian`
  * `LieSubmodule.lieSpan`
  * `LieSubmodule.map`
  * `LieSubmodule.comap`

## Tags

lie algebra, lie submodule, lie ideal, lattice structure
-/

@[expose] public section


universe u v w w₁ w₂

section LieSubmodule

variable (R : Type u) (L : Type v) (M : Type w)
variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M]

/--
Definition of `LieSubmodule` / `LieSubmodule` 的定义

English:
structure LieSubmodule
  parameters: extends Submodule R M
  extends: Submodule R M
  axioms and operations (1):
    - lie_mem : forall {x : L} {m : M}, m in carrier -> ⁅x, m⁆ in carrier

中文:
结构 LieSubmodule
  参数: extends Submodule R M
  继承: Submodule R M
  公理与运算 (1 个):
    - lie_mem : 对任意 {x : L} {m : M}, m in carrier -> ⁅x, m⁆ in carrier
-/
structure LieSubmodule extends Submodule R M where
  lie_mem : forall {x : L} {m : M}, m in carrier -> ⁅x, m⁆ in carrier

attribute [nolint docBlame] LieSubmodule.toSubmodule
attribute [coe] LieSubmodule.toSubmodule

namespace LieSubmodule

variable {R L M}
variable (N N' : LieSubmodule R L M)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (LieSubmodule R L M) M
  body: s.carrier
  coe_injective N O h := by cases N; cases O; congr; exact SetLike.coe_injective h

中文:
实例 :
  签名: SetLike (LieSubmodule R L M) M
  定义体: s.carrier
  coe_injective N O h := by cases N; cases O; congr; exact SetLike.coe_injective h

Depends on / 依赖: carrier, s.carrier
-/
instance : SetLike (LieSubmodule R L M) M where
  coe s := s.carrier
  coe_injective N O h := by cases N; cases O; congr; exact SetLike.coe_injective h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (LieSubmodule R L M)
  body: .ofSetLike (LieSubmodule R L M) M

中文:
实例 :
  签名: PartialOrder (LieSubmodule R L M)
  定义体: .ofSetLike (LieSubmodule R L M) M

Depends on / 依赖: LieSubmodule, ofSetLike
-/
instance : PartialOrder (LieSubmodule R L M) := .ofSetLike (LieSubmodule R L M) M

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddSubgroupClass (LieSubmodule R L M) M
  body: N.add_mem'
  zero_mem N := N.zero_mem'
  neg_mem {N} x hx := show -x in N.toSubmodule from neg_mem hx

中文:
实例 :
  签名: AddSubgroupClass (LieSubmodule R L M) M
  定义体: N.add_mem'
  zero_mem N := N.zero_mem'
  neg_mem {N} x hx := show -x in N.toSubmodule from neg_mem hx

Depends on / 依赖: N.add_mem, add_mem
-/
instance : AddSubgroupClass (LieSubmodule R L M) M where
  add_mem {N} _ _ := N.add_mem'
  zero_mem N := N.zero_mem'
  neg_mem {N} x hx := show -x in N.toSubmodule from neg_mem hx

/--
Instance `instSMulMemClass` / 实例 `instSMulMemClass`

English:
instance instSMulMemClass
  signature: : SMulMemClass (LieSubmodule R L M) R M where
  body: s.smul_mem' c h

中文:
实例 instSMulMemClass
  签名: : SMulMemClass (LieSubmodule R L M) R M where
  定义体: s.smul_mem' c h

Depends on / 依赖: s.smul_mem, smul_mem
-/
instance instSMulMemClass : SMulMemClass (LieSubmodule R L M) R M where
  smul_mem {s} c _ h := s.smul_mem' c h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (LieSubmodule R L M)
  body: ⟨{ (0 : Submodule R M) with
      lie_mem := fun {x m} h => by rw [(Submodule.mem_bot R).1 h]; apply lie_zero }⟩

中文:
实例 :
  签名: Zero (LieSubmodule R L M)
  定义体: ⟨{ (0 : Submodule R M) with
      lie_mem := fun {x m} h => by rw [(Submodule.mem_bot R).1 h]; apply lie_zero }⟩

Depends on / 依赖: Submodule, Submodule.mem_bot, lie_mem, lie_zero, mem_bot
-/
instance : Zero (LieSubmodule R L M) :=
  ⟨{ (0 : Submodule R M) with
      lie_mem := fun {x m} h => by rw [(Submodule.mem_bot R).1 h]; apply lie_zero }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (LieSubmodule R L M)
  body: ⟨0⟩

中文:
实例 :
  签名: Inhabited (LieSubmodule R L M)
  定义体: ⟨0⟩
-/
instance : Inhabited (LieSubmodule R L M) :=
  ⟨0⟩

instance (priority := mid) coeSubmodule : CoeOut (LieSubmodule R L M) (Submodule R M) :=
  ⟨toSubmodule⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanLift (Submodule R M) (LieSubmodule R L M) (·)
  body: ⟨⟨N, hN⟩, rfl⟩

@[norm_cast]

中文:
实例 :
  签名: CanLift (Submodule R M) (LieSubmodule R L M) (·)
  定义体: ⟨⟨N, hN⟩, rfl⟩

@[norm_cast]
-/
instance : CanLift (Submodule R M) (LieSubmodule R L M) (·)
    (fun N => forall {x : L} {m : M}, m in N -> ⁅x, m⁆ in N) where
  prf N hN := ⟨⟨N, hN⟩, rfl⟩

@[norm_cast]
/--
theorem `coe_toSubmodule` / 定理 `coe_toSubmodule`

English:
theorem coe_toSubmodule
  statement: ((N : Submodule R M) : Set M) = N
  proof: rfl

中文:
定理 coe_toSubmodule
  结论: ((N : Submodule R M) : Set M) = N
  证明: rfl
-/
theorem coe_toSubmodule : ((N : Submodule R M) : Set M) = N :=
  rfl

/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  given: {x : M}
  statement: x in N.carrier ↔ x in (N : Set M)
  proof: Iff.rfl

中文:
定理 mem_carrier
  条件: {x : M}
  结论: x in N.carrier ↔ x in (N : Set M)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier {x : M} : x in N.carrier ↔ x in (N : Set M) :=
  Iff.rfl

/--
theorem `mem_mk_iff` / 定理 `mem_mk_iff`

English:
theorem mem_mk_iff
  given: (S : Set M) (h₁ h₂ h₃ h₄) {x : M}
  proof: Iff.rfl

@[simp]

中文:
定理 mem_mk_iff
  条件: (S : Set M) (h₁ h₂ h₃ h₄) {x : M}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk_iff (S : Set M) (h₁ h₂ h₃ h₄) {x : M} :
    x in (⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieSubmodule R L M) ↔ x in S :=
  Iff.rfl

@[simp]
/--
theorem `mem_mk_iff'` / 定理 `mem_mk_iff'`

English:
theorem mem_mk_iff'
  given: (p : Submodule R M) (h) {x : M}
  proof: Iff.rfl

@[simp]

中文:
定理 mem_mk_iff'
  条件: (p : Submodule R M) (h) {x : M}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk_iff' (p : Submodule R M) (h) {x : M} :
    x in (⟨p, h⟩ : LieSubmodule R L M) ↔ x in p :=
  Iff.rfl

@[simp]
/--
theorem `mem_toSubmodule` / 定理 `mem_toSubmodule`

English:
theorem mem_toSubmodule
  given: {x : M}
  statement: x in (N : Submodule R M) ↔ x in N
  proof: Iff.rfl

中文:
定理 mem_toSubmodule
  条件: {x : M}
  结论: x in (N : Submodule R M) ↔ x in N
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_toSubmodule {x : M} : x in (N : Submodule R M) ↔ x in N :=
  Iff.rfl

/--
theorem `mem_coe` / 定理 `mem_coe`

English:
theorem mem_coe
  given: {x : M}
  statement: x in (N : Set M) ↔ x in N
  proof: Iff.rfl

中文:
定理 mem_coe
  条件: {x : M}
  结论: x in (N : Set M) ↔ x in N
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_coe {x : M} : x in (N : Set M) ↔ x in N :=
  Iff.rfl

/--
theorem `zero_mem` / 定理 `zero_mem`

English:
theorem zero_mem
  statement: (0 : M) in N
  proof: zero_mem N

@[simp]

中文:
定理 zero_mem
  结论: (0 : M) in N
  证明: zero_mem N

@[simp]
-/
protected theorem zero_mem : (0 : M) in N :=
  zero_mem N

@[simp]
/--
theorem `mk_eq_zero` / 定理 `mk_eq_zero`

English:
theorem mk_eq_zero
  given: {x} (h : x in N)
  statement: (⟨x, h⟩ : N) = 0 ↔ x = 0
  proof: Subtype.ext_iff

@[simp]

中文:
定理 mk_eq_zero
  条件: {x} (h : x in N)
  结论: (⟨x, h⟩ : N) = 0 ↔ x = 0
  证明: Subtype.ext_iff

@[simp]

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff
-/
theorem mk_eq_zero {x} (h : x in N) : (⟨x, h⟩ : N) = 0 ↔ x = 0 :=
  Subtype.ext_iff

@[simp]
/--
theorem `coe_toSet_mk` / 定理 `coe_toSet_mk`

English:
theorem coe_toSet_mk
  given: (S : Set M) (h₁ h₂ h₃ h₄)
  proof: rfl

中文:
定理 coe_toSet_mk
  条件: (S : Set M) (h₁ h₂ h₃ h₄)
  证明: rfl
-/
theorem coe_toSet_mk (S : Set M) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieSubmodule R L M) : Set M) = S :=
  rfl

/--
theorem `toSubmodule_mk` / 定理 `toSubmodule_mk`

English:
theorem toSubmodule_mk
  given: (p : Submodule R M) (h)
  proof: by cases p; rfl

中文:
定理 toSubmodule_mk
  条件: (p : Submodule R M) (h)
  证明: by cases p; rfl

Depends on / 依赖: LieSubmodule, Submodule
-/
theorem toSubmodule_mk (p : Submodule R M) (h) :
    (({ p with lie_mem := h } : LieSubmodule R L M) : Submodule R M) = p := by cases p; rfl

/--
theorem `toSubmodule_injective` / 定理 `toSubmodule_injective`

English:
theorem toSubmodule_injective
  proof: fun x y h => by
  cases x; cases y; congr

@[ext]

中文:
定理 toSubmodule_injective
  证明: fun x y h => by
  cases x; cases y; congr

@[ext]
-/
theorem toSubmodule_injective :
    Function.Injective (toSubmodule : LieSubmodule R L M -> Submodule R M) := fun x y h => by
  cases x; cases y; congr

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (h : forall m, m in N ↔ m in N')
  statement: N = N'
  proof: SetLike.ext h

@[simp]

中文:
定理 ext
  条件: (h : 对任意 m, m in N ↔ m in N')
  结论: N = N'
  证明: SetLike.ext h

@[simp]

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext (h : forall m, m in N ↔ m in N') : N = N' :=
  SetLike.ext h

@[simp]
/--
theorem `toSubmodule_inj` / 定理 `toSubmodule_inj`

English:
theorem toSubmodule_inj
  statement: (N : Submodule R M) = (N' : Submodule R M) ↔ N = N'
  proof: toSubmodule_injective.eq_iff

中文:
定理 toSubmodule_inj
  结论: (N : Submodule R M) = (N' : Submodule R M) ↔ N = N'
  证明: toSubmodule_injective.eq_iff

Depends on / 依赖: eq_iff, toSubmodule_injective, toSubmodule_injective.eq_iff
-/
theorem toSubmodule_inj : (N : Submodule R M) = (N' : Submodule R M) ↔ N = N' :=
  toSubmodule_injective.eq_iff

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (s : Set M) (hs : s = ↑N)
  body: s
  zero_mem' := by simp [hs]
  add_mem' x y := by rw [hs] at x y ⊢; exact N.add_mem' x y
  smul_mem' := by exact hs.symm ▸ N.smul_mem'
  lie_mem := by exact hs.symm ▸ N.lie_mem

@[simp, norm_cast]

中文:
定义 copy
  签名: (s : Set M) (hs : s = ↑N)
  定义体: s
  zero_mem' := by simp [hs]
  add_mem' x y := by rw [hs] at x y ⊢; exact N.add_mem' x y
  smul_mem' := by exact hs.symm ▸ N.smul_mem'
  lie_mem := by exact hs.symm ▸ N.lie_mem

@[simp, norm_cast]
-/
protected def copy (s : Set M) (hs : s = ↑N) : LieSubmodule R L M where
  carrier := s
  zero_mem' := by simp [hs]
  add_mem' x y := by rw [hs] at x y ⊢; exact N.add_mem' x y
  smul_mem' := by exact hs.symm ▸ N.smul_mem'
  lie_mem := by exact hs.symm ▸ N.lie_mem

@[simp, norm_cast]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (S : LieSubmodule R L M) (s : Set M) (hs : s = ↑S)
  statement: (S.copy s hs : Set M) = s
  proof: rfl

中文:
定理 coe_copy
  条件: (S : LieSubmodule R L M) (s : Set M) (hs : s = ↑S)
  结论: (S.copy s hs : Set M) = s
  证明: rfl
-/
theorem coe_copy (S : LieSubmodule R L M) (s : Set M) (hs : s = ↑S) : (S.copy s hs : Set M) = s :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (S : LieSubmodule R L M) (s : Set M) (hs : s = ↑S)
  statement: S.copy s hs = S
  proof: SetLike.coe_injective hs

中文:
定理 copy_eq
  条件: (S : LieSubmodule R L M) (s : Set M) (hs : s = ↑S)
  结论: S.copy s hs = S
  证明: SetLike.coe_injective hs

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem copy_eq (S : LieSubmodule R L M) (s : Set M) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieRingModule L N
  body: ⟨⁅x, m.val⁆, N.lie_mem m.property⟩
  add_lie := by intro x y m; apply SetCoe.ext; apply add_lie
  lie_add := by intro x m n; apply SetCoe.ext; apply lie_add
  leibniz_lie := by intro x y m; apply SetCoe.ext; apply leibniz_lie

@[simp, norm_cast]

中文:
实例 :
  签名: LieRingModule L N
  定义体: ⟨⁅x, m.val⁆, N.lie_mem m.property⟩
  add_lie := by intro x y m; apply SetCoe.ext; apply add_lie
  lie_add := by intro x m n; apply SetCoe.ext; apply lie_add
  leibniz_lie := by intro x y m; apply SetCoe.ext; apply leibniz_lie

@[simp, norm_cast]

Depends on / 依赖: N.lie_mem, lie_mem, m.property, m.val, property
-/
instance : LieRingModule L N where
  bracket (x : L) (m : N) := ⟨⁅x, m.val⁆, N.lie_mem m.property⟩
  add_lie := by intro x y m; apply SetCoe.ext; apply add_lie
  lie_add := by intro x m n; apply SetCoe.ext; apply lie_add
  leibniz_lie := by intro x y m; apply SetCoe.ext; apply leibniz_lie

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ((0 : N) : M) = (0 : M)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_zero
  结论: ((0 : N) : M) = (0 : M)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_zero : ((0 : N) : M) = (0 : M) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (m m' : N)
  statement: (↑(m + m') : M) = (m : M) + (m' : M)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_add
  条件: (m m' : N)
  结论: (↑(m + m') : M) = (m : M) + (m' : M)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_add (m m' : N) : (↑(m + m') : M) = (m : M) + (m' : M) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (m : N)
  statement: (↑(-m) : M) = -(m : M)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_neg
  条件: (m : N)
  结论: (↑(-m) : M) = -(m : M)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_neg (m : N) : (↑(-m) : M) = -(m : M) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (m m' : N)
  statement: (↑(m - m') : M) = (m : M) - (m' : M)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_sub
  条件: (m m' : N)
  结论: (↑(m - m') : M) = (m : M) - (m' : M)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_sub (m m' : N) : (↑(m - m') : M) = (m : M) - (m' : M) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (t : R) (m : N)
  statement: (↑(t • m) : M) = t • (m : M)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_smul
  条件: (t : R) (m : N)
  结论: (↑(t • m) : M) = t • (m : M)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_smul (t : R) (m : N) : (↑(t • m) : M) = t • (m : M) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_bracket` / 定理 `coe_bracket`

English:
theorem coe_bracket
  given: (x : L) (m : N)
  proof: rfl

中文:
定理 coe_bracket
  条件: (x : L) (m : N)
  证明: rfl
-/
theorem coe_bracket (x : L) (m : N) :
    (↑⁅x, m⁆ : M) = ⁅x, ↑m⁆ :=
  rfl

-- Copying instances from `Submodule` for correct discrimination keys
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsNoetherian
  signature: R M] (N
  body: inferInstanceAs IsNoetherian R N.toSubmodule

中文:
实例 [IsNoetherian
  签名: R M] (N
  定义体: inferInstanceAs IsNoetherian R N.toSubmodule

Depends on / 依赖: IsNoetherian, N.toSubmodule, toSubmodule
-/
instance [IsNoetherian R M] (N : LieSubmodule R L M) : IsNoetherian R N :=
inferInstanceAs IsNoetherian R N.toSubmodule

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsArtinian
  signature: R M] (N
  body: inferInstanceAs IsArtinian R N.toSubmodule

中文:
实例 [IsArtinian
  签名: R M] (N
  定义体: inferInstanceAs IsArtinian R N.toSubmodule

Depends on / 依赖: IsArtinian, N.toSubmodule, toSubmodule
-/
instance [IsArtinian R M] (N : LieSubmodule R L M) : IsArtinian R N :=
inferInstanceAs IsArtinian R N.toSubmodule

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module.IsTorsionFree
  signature: R M] : Module.IsTorsionFree R N
  body: inferInstanceAs Module.IsTorsionFree R N.toSubmodule

中文:
实例 [Module.IsTorsionFree
  签名: R M] : Module.IsTorsionFree R N
  定义体: inferInstanceAs Module.IsTorsionFree R N.toSubmodule

Depends on / 依赖: IsTorsionFree, Module, Module.IsTorsionFree, N.toSubmodule, toSubmodule
-/
instance [Module.IsTorsionFree R M] : Module.IsTorsionFree R N :=
inferInstanceAs Module.IsTorsionFree R N.toSubmodule

variable [LieAlgebra R L]

/--
Definition of `restr` / `restr` 的定义

English:
definition restr
  signature: (N : LieSubmodule R L M) (H : LieSubalgebra R L)
  body: N
  add_mem' := N.add_mem'
  zero_mem' := N.zero_mem'
  smul_mem' := SMulMemClass.smul_mem
  lie_mem hm := N.lie_mem hm

中文:
定义 restr
  签名: (N : LieSubmodule R L M) (H : LieSubalgebra R L)
  定义体: N
  add_mem' := N.add_mem'
  zero_mem' := N.zero_mem'
  smul_mem' := SMulMemClass.smul_mem
  lie_mem hm := N.lie_mem hm
-/
def restr (N : LieSubmodule R L M) (H : LieSubalgebra R L) : LieSubmodule R H M where
  carrier := N
  add_mem' := N.add_mem'
  zero_mem' := N.zero_mem'
  smul_mem' := SMulMemClass.smul_mem
  lie_mem hm := N.lie_mem hm

/--
lemma `mem_restr` / 引理 `mem_restr`

English:
lemma mem_restr
  given: {N : LieSubmodule R L M} {H : LieSubalgebra R L} {m : M}
  proof: Iff.rfl

中文:
引理 mem_restr
  条件: {N : LieSubmodule R L M} {H : LieSubalgebra R L} {m : M}
  证明: Iff.rfl
-/
@[simp] lemma mem_restr {N : LieSubmodule R L M} {H : LieSubalgebra R L} {m : M} :
    m in N.restr H ↔ m in N := Iff.rfl

/--
lemma `restr_toSubmodule` / 引理 `restr_toSubmodule`

English:
lemma restr_toSubmodule
  given: (N : LieSubmodule R L M) (H : LieSubalgebra R L)
  proof: rfl

中文:
引理 restr_toSubmodule
  条件: (N : LieSubmodule R L M) (H : LieSubalgebra R L)
  证明: rfl
-/
@[simp] lemma restr_toSubmodule (N : LieSubmodule R L M) (H : LieSubalgebra R L) :
    (N.restr H).toSubmodule = N.toSubmodule := rfl

variable [LieModule R L M]

/--
Instance `instLieModule` / 实例 `instLieModule`

English:
instance instLieModule
  signature: : LieModule R L N where
  body: by intro t x y; apply SetCoe.ext; apply lie_smul
  smul_lie := by intro t x y; apply SetCoe.ext; apply smul_lie

中文:
实例 instLieModule
  签名: : LieModule R L N where
  定义体: by intro t x y; apply SetCoe.ext; apply lie_smul
  smul_lie := by intro t x y; apply SetCoe.ext; apply smul_lie

Depends on / 依赖: SetCoe, SetCoe.ext, lie_smul, smul_lie
-/
instance instLieModule : LieModule R L N where
  lie_smul := by intro t x y; apply SetCoe.ext; apply lie_smul
  smul_lie := by intro t x y; apply SetCoe.ext; apply smul_lie

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: M] : Unique (LieSubmodule R L M)
  body: ⟨⟨0⟩, fun _ => (toSubmodule_inj _ _).mp (Subsingleton.elim _ _)⟩

中文:
实例 [Subsingleton
  签名: M] : Unique (LieSubmodule R L M)
  定义体: ⟨⟨0⟩, fun _ => (toSubmodule_inj _ _).mp (Subsingleton.elim _ _)⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, toSubmodule_inj
-/
instance [Subsingleton M] : Unique (LieSubmodule R L M) :=
  ⟨⟨0⟩, fun _ => (toSubmodule_inj _ _).mp (Subsingleton.elim _ _)⟩

end LieSubmodule

variable {R M}

/--
theorem `Submodule.exists_lieSubmodule_coe_eq_iff` / 定理 `Submodule.exists_lieSubmodule_coe_eq_iff`

English:
theorem Submodule.exists_lieSubmodule_coe_eq_iff
  given: (p : Submodule R M)
  proof: by
  constructor
  · rintro ⟨N, rfl⟩ _ _; exact N.lie_mem
  · intro h; use { p with lie_mem := @h }

中文:
定理 Submodule.exists_lieSubmodule_coe_eq_iff
  条件: (p : Submodule R M)
  证明: by
  constructor
  · rintro ⟨N, rfl⟩ _ _; exact N.lie_mem
  · intro h; use { p with lie_mem := @h }

Depends on / 依赖: N.lie_mem, lie_mem
-/
theorem Submodule.exists_lieSubmodule_coe_eq_iff (p : Submodule R M) :
    (exists N : LieSubmodule R L M, ↑N = p) ↔ forall (x : L) (m : M), m in p -> ⁅x, m⁆ in p := by
  constructor
  · rintro ⟨N, rfl⟩ _ _; exact N.lie_mem
  · intro h; use { p with lie_mem := @h }

namespace LieSubalgebra

variable {L}
variable [LieAlgebra R L]
variable (K : LieSubalgebra R L)

/--
Definition of `toLieSubmodule` / `toLieSubmodule` 的定义

English:
definition toLieSubmodule
  signature: : LieSubmodule R K L
  body: { (K : Submodule R L) with lie_mem := fun {x _} hy => K.lie_mem x.property hy }

@[simp]

中文:
定义 toLieSubmodule
  签名: : LieSubmodule R K L
  定义体: { (K : Submodule R L) with lie_mem := fun {x _} hy => K.lie_mem x.property hy }

@[simp]

Depends on / 依赖: K.lie_mem, Submodule, lie_mem, property, x.property
-/
def toLieSubmodule : LieSubmodule R K L :=
  { (K : Submodule R L) with lie_mem := fun {x _} hy => K.lie_mem x.property hy }

@[simp]
/--
theorem `coe_toLieSubmodule` / 定理 `coe_toLieSubmodule`

English:
theorem coe_toLieSubmodule
  statement: (K.toLieSubmodule : Submodule R L) = K
  proof: rfl

中文:
定理 coe_toLieSubmodule
  结论: (K.toLieSubmodule : Submodule R L) = K
  证明: rfl
-/
theorem coe_toLieSubmodule : (K.toLieSubmodule : Submodule R L) = K := rfl

variable {K}

@[simp]
/--
theorem `mem_toLieSubmodule` / 定理 `mem_toLieSubmodule`

English:
theorem mem_toLieSubmodule
  given: (x : L)
  statement: x in K.toLieSubmodule ↔ x in K
  proof: Iff.rfl

中文:
定理 mem_toLieSubmodule
  条件: (x : L)
  结论: x in K.toLieSubmodule ↔ x in K
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_toLieSubmodule (x : L) : x in K.toLieSubmodule ↔ x in K :=
  Iff.rfl

end LieSubalgebra

end LieSubmodule

namespace LieSubmodule

variable {R : Type u} {L : Type v} {M : Type w}
variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M]
variable (N N' : LieSubmodule R L M)

section LatticeStructure

open Set

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: Function.Injective ((↑) : LieSubmodule R L M -> Set M)
  proof: SetLike.coe_injective

@[simp, norm_cast]

中文:
定理 coe_injective
  结论: Function.Injective ((↑) : LieSubmodule R L M -> Set M)
  证明: SetLike.coe_injective

@[simp, norm_cast]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem coe_injective : Function.Injective ((↑) : LieSubmodule R L M -> Set M) :=
  SetLike.coe_injective

@[simp, norm_cast]
/--
theorem `toSubmodule_le_toSubmodule` / 定理 `toSubmodule_le_toSubmodule`

English:
theorem toSubmodule_le_toSubmodule
  statement: (N : Submodule R M) <= N' ↔ N <= N'
  proof: Iff.rfl

中文:
定理 toSubmodule_le_toSubmodule
  结论: (N : Submodule R M) <= N' ↔ N <= N'
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem toSubmodule_le_toSubmodule : (N : Submodule R M) <= N' ↔ N <= N' :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (LieSubmodule R L M)
  body: ⟨0⟩

中文:
实例 :
  签名: Bot (LieSubmodule R L M)
  定义体: ⟨0⟩
-/
instance : Bot (LieSubmodule R L M) :=
  ⟨0⟩

/--
Instance `instUniqueBot` / 实例 `instUniqueBot`

English:
instance instUniqueBot
  signature: : Unique (⊥ : LieSubmodule R L M)
  body: inferInstanceAs Unique (⊥ : Submodule R M)

@[simp]

中文:
实例 instUniqueBot
  签名: : Unique (⊥ : LieSubmodule R L M)
  定义体: inferInstanceAs Unique (⊥ : Submodule R M)

@[simp]

Depends on / 依赖: Submodule, Unique
-/
instance instUniqueBot : Unique (⊥ : LieSubmodule R L M) :=
inferInstanceAs Unique (⊥ : Submodule R M)

@[simp]
/--
theorem `bot_coe` / 定理 `bot_coe`

English:
theorem bot_coe
  statement: ((⊥ : LieSubmodule R L M) : Set M) = {0}
  proof: rfl

@[simp]

中文:
定理 bot_coe
  结论: ((⊥ : LieSubmodule R L M) : Set M) = {0}
  证明: rfl

@[simp]
-/
theorem bot_coe : ((⊥ : LieSubmodule R L M) : Set M) = {0} :=
  rfl

@[simp]
/--
theorem `bot_toSubmodule` / 定理 `bot_toSubmodule`

English:
theorem bot_toSubmodule
  statement: ((⊥ : LieSubmodule R L M) : Submodule R M) = ⊥
  proof: rfl

@[simp]

中文:
定理 bot_toSubmodule
  结论: ((⊥ : LieSubmodule R L M) : Submodule R M) = ⊥
  证明: rfl

@[simp]
-/
theorem bot_toSubmodule : ((⊥ : LieSubmodule R L M) : Submodule R M) = ⊥ :=
  rfl

@[simp]
/--
theorem `toSubmodule_eq_bot` / 定理 `toSubmodule_eq_bot`

English:
theorem toSubmodule_eq_bot
  statement: (N : Submodule R M) = ⊥ ↔ N = ⊥
  proof: by
  rw [← toSubmodule_inj]; rw [bot_toSubmodule]

中文:
定理 toSubmodule_eq_bot
  结论: (N : Submodule R M) = ⊥ ↔ N = ⊥
  证明: by
  rw [← toSubmodule_inj]; rw [bot_toSubmodule]

Depends on / 依赖: bot_toSubmodule, toSubmodule_inj
-/
theorem toSubmodule_eq_bot : (N : Submodule R M) = ⊥ ↔ N = ⊥ := by
  rw [← toSubmodule_inj]; rw [bot_toSubmodule]

/--
theorem `mk_eq_bot_iff` / 定理 `mk_eq_bot_iff`

English:
theorem mk_eq_bot_iff
  given: {N : Submodule R M} {h}
  proof: by
  rw [← toSubmodule_inj]; rw [bot_toSubmodule]

@[simp]

中文:
定理 mk_eq_bot_iff
  条件: {N : Submodule R M} {h}
  证明: by
  rw [← toSubmodule_inj]; rw [bot_toSubmodule]

@[simp]
-/
@[simp] theorem mk_eq_bot_iff {N : Submodule R M} {h} :
    (⟨N, h⟩ : LieSubmodule R L M) = ⊥ ↔ N = ⊥ := by
  rw [← toSubmodule_inj]; rw [bot_toSubmodule]

@[simp]
/--
theorem `mem_bot` / 定理 `mem_bot`

English:
theorem mem_bot
  given: (x : M)
  statement: x in (⊥ : LieSubmodule R L M) ↔ x = 0
  proof: mem_singleton_iff

中文:
定理 mem_bot
  条件: (x : M)
  结论: x in (⊥ : LieSubmodule R L M) ↔ x = 0
  证明: mem_singleton_iff

Depends on / 依赖: mem_singleton_iff
-/
theorem mem_bot (x : M) : x in (⊥ : LieSubmodule R L M) ↔ x = 0 :=
  mem_singleton_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (LieSubmodule R L M)
  body: ⟨{ (⊤ : Submodule R M) with lie_mem := fun {x m} _ => mem_univ ⁅x, m⁆ }⟩

@[simp]

中文:
实例 :
  签名: Top (LieSubmodule R L M)
  定义体: ⟨{ (⊤ : Submodule R M) with lie_mem := fun {x m} _ => mem_univ ⁅x, m⁆ }⟩

@[simp]

Depends on / 依赖: Submodule, lie_mem, mem_univ
-/
instance : Top (LieSubmodule R L M) :=
  ⟨{ (⊤ : Submodule R M) with lie_mem := fun {x m} _ => mem_univ ⁅x, m⁆ }⟩

@[simp]
/--
theorem `top_coe` / 定理 `top_coe`

English:
theorem top_coe
  statement: ((⊤ : LieSubmodule R L M) : Set M) = univ
  proof: rfl

@[simp]

中文:
定理 top_coe
  结论: ((⊤ : LieSubmodule R L M) : Set M) = univ
  证明: rfl

@[simp]
-/
theorem top_coe : ((⊤ : LieSubmodule R L M) : Set M) = univ :=
  rfl

@[simp]
/--
theorem `top_toSubmodule` / 定理 `top_toSubmodule`

English:
theorem top_toSubmodule
  statement: ((⊤ : LieSubmodule R L M) : Submodule R M) = ⊤
  proof: rfl

@[simp]

中文:
定理 top_toSubmodule
  结论: ((⊤ : LieSubmodule R L M) : Submodule R M) = ⊤
  证明: rfl

@[simp]
-/
theorem top_toSubmodule : ((⊤ : LieSubmodule R L M) : Submodule R M) = ⊤ :=
  rfl

@[simp]
/--
theorem `toSubmodule_eq_top` / 定理 `toSubmodule_eq_top`

English:
theorem toSubmodule_eq_top
  statement: (N : Submodule R M) = ⊤ ↔ N = ⊤
  proof: by
  rw [← toSubmodule_inj]; rw [top_toSubmodule]

中文:
定理 toSubmodule_eq_top
  结论: (N : Submodule R M) = ⊤ ↔ N = ⊤
  证明: by
  rw [← toSubmodule_inj]; rw [top_toSubmodule]

Depends on / 依赖: toSubmodule_inj, top_toSubmodule
-/
theorem toSubmodule_eq_top : (N : Submodule R M) = ⊤ ↔ N = ⊤ := by
  rw [← toSubmodule_inj]; rw [top_toSubmodule]

/--
theorem `mk_eq_top_iff` / 定理 `mk_eq_top_iff`

English:
theorem mk_eq_top_iff
  given: {N : Submodule R M} {h}
  proof: by
  rw [← toSubmodule_inj]; rw [top_toSubmodule]

@[simp]

中文:
定理 mk_eq_top_iff
  条件: {N : Submodule R M} {h}
  证明: by
  rw [← toSubmodule_inj]; rw [top_toSubmodule]

@[simp]
-/
@[simp] theorem mk_eq_top_iff {N : Submodule R M} {h} :
    (⟨N, h⟩ : LieSubmodule R L M) = ⊤ ↔ N = ⊤ := by
  rw [← toSubmodule_inj]; rw [top_toSubmodule]

@[simp]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  given: (x : M)
  statement: x in (⊤ : LieSubmodule R L M)
  proof: mem_univ x

中文:
定理 mem_top
  条件: (x : M)
  结论: x in (⊤ : LieSubmodule R L M)
  证明: mem_univ x

Depends on / 依赖: mem_univ
-/
theorem mem_top (x : M) : x in (⊤ : LieSubmodule R L M) :=
  mem_univ x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (LieSubmodule R L M)
  body: ⟨fun N N' =>
    { (N ⊓ N' : Submodule R M) with
      lie_mem := fun h => mem_inter (N.lie_mem h.1) (N'.lie_mem h.2) }⟩

中文:
实例 :
  签名: Min (LieSubmodule R L M)
  定义体: ⟨fun N N' =>
    { (N ⊓ N' : Submodule R M) with
      lie_mem := fun h => mem_inter (N.lie_mem h.1) (N'.lie_mem h.2) }⟩

Depends on / 依赖: N.lie_mem, Submodule, lie_mem, mem_inter
-/
instance : Min (LieSubmodule R L M) :=
  ⟨fun N N' =>
    { (N ⊓ N' : Submodule R M) with
      lie_mem := fun h => mem_inter (N.lie_mem h.1) (N'.lie_mem h.2) }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (LieSubmodule R L M)
  body: ⟨fun S =>
    { toSubmodule := sInf {(s : Submodule R M) | s in S}
      lie_mem := fun {x m} h => by
        simp only [Submodule.mem_carrier, mem_iInter, Submodule.coe_sInf, mem_ofPred_eq,
          forall_apply_eq_imp_iff₂, forall_exists_index, and_imp] at h ⊢
        intro N hN; apply N.lie_mem 

中文:
实例 :
  签名: InfSet (LieSubmodule R L M)
  定义体: ⟨fun S =>
    { toSubmodule := sInf {(s : Submodule R M) | s in S}
      lie_mem := fun {x m} h => by
        simp only [Submodule.mem_carrier, mem_iInter, Submodule.coe_sInf, mem_ofPred_eq,
          forall_apply_eq_imp_iff₂, forall_exists_index, and_imp] at h ⊢
        intro N hN; apply N.lie_mem 

Depends on / 依赖: N.lie_mem, Submodule, Submodule.coe_sInf, Submodule.mem_carrier, and_imp, coe_sInf, forall_exists_index, lie_mem, mem_carrier, mem_iInter, mem_ofPred_eq, toSubmodule
-/
instance : InfSet (LieSubmodule R L M) :=
  ⟨fun S =>
    { toSubmodule := sInf {(s : Submodule R M) | s in S}
      lie_mem := fun {x m} h => by
        simp only [Submodule.mem_carrier, mem_iInter, Submodule.coe_sInf, mem_ofPred_eq,
          forall_apply_eq_imp_iff₂, forall_exists_index, and_imp] at h ⊢
        intro N hN; apply N.lie_mem (h N hN) }⟩

@[simp]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  statement: (↑(N ⊓ N') : Set M) = ↑N inter ↑N'
  proof: rfl

@[norm_cast, simp]

中文:
定理 coe_inf
  结论: (↑(N ⊓ N') : Set M) = ↑N inter ↑N'
  证明: rfl

@[norm_cast, simp]
-/
theorem coe_inf : (↑(N ⊓ N') : Set M) = ↑N inter ↑N' :=
  rfl

@[norm_cast, simp]
/--
theorem `inf_toSubmodule` / 定理 `inf_toSubmodule`

English:
theorem inf_toSubmodule
  proof: rfl

@[simp]

中文:
定理 inf_toSubmodule
  证明: rfl

@[simp]
-/
theorem inf_toSubmodule :
    (↑(N ⊓ N') : Submodule R M) = (N : Submodule R M) ⊓ (N' : Submodule R M) :=
  rfl

@[simp]
/--
theorem `sInf_toSubmodule` / 定理 `sInf_toSubmodule`

English:
theorem sInf_toSubmodule
  given: (S : Set (LieSubmodule R L M))
  proof: rfl

中文:
定理 sInf_toSubmodule
  条件: (S : Set (LieSubmodule R L M))
  证明: rfl
-/
theorem sInf_toSubmodule (S : Set (LieSubmodule R L M)) :
    (↑(sInf S) : Submodule R M) = sInf {(s : Submodule R M) | s in S} :=
  rfl

/--
theorem `sInf_toSubmodule_eq_iInf` / 定理 `sInf_toSubmodule_eq_iInf`

English:
theorem sInf_toSubmodule_eq_iInf
  given: (S : Set (LieSubmodule R L M))
  proof: by
  rw [sInf_toSubmodule]; rw [← Set.image]; rw [sInf_image]

@[simp]

中文:
定理 sInf_toSubmodule_eq_iInf
  条件: (S : Set (LieSubmodule R L M))
  证明: by
  rw [sInf_toSubmodule]; rw [← Set.image]; rw [sInf_image]

@[simp]

Depends on / 依赖: Set.image, sInf_image, sInf_toSubmodule
-/
theorem sInf_toSubmodule_eq_iInf (S : Set (LieSubmodule R L M)) :
    (↑(sInf S) : Submodule R M) = ⨅ N in S, (N : Submodule R M) := by
  rw [sInf_toSubmodule]; rw [← Set.image]; rw [sInf_image]

@[simp]
/--
theorem `iInf_toSubmodule` / 定理 `iInf_toSubmodule`

English:
theorem iInf_toSubmodule
  given: {ι} (p : ι -> LieSubmodule R L M)
  proof: by
  rw [iInf]; rw [sInf_toSubmodule]; ext; simp

@[simp]

中文:
定理 iInf_toSubmodule
  条件: {ι} (p : ι -> LieSubmodule R L M)
  证明: by
  rw [iInf]; rw [sInf_toSubmodule]; ext; simp

@[simp]

Depends on / 依赖: sInf_toSubmodule
-/
theorem iInf_toSubmodule {ι} (p : ι -> LieSubmodule R L M) :
    (↑(⨅ i, p i) : Submodule R M) = ⨅ i, (p i : Submodule R M) := by
  rw [iInf]; rw [sInf_toSubmodule]; ext; simp

@[simp]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: (S : Set (LieSubmodule R L M))
  statement: (↑(sInf S) : Set M) = ⋂ s in S, (s : Set M)
  proof: by
  rw [← LieSubmodule.coe_toSubmodule]; rw [sInf_toSubmodule]; rw [Submodule.coe_sInf]
  ext m
  simp only [mem_iInter, mem_ofPred_eq, forall_apply_eq_imp_iff₂, exists_imp,
    and_imp, SetLike.mem_coe, mem_toSubmodule]

@[simp]

中文:
定理 coe_sInf
  条件: (S : Set (LieSubmodule R L M))
  结论: (↑(sInf S) : Set M) = ⋂ s in S, (s : Set M)
  证明: by
  rw [← LieSubmodule.coe_toSubmodule]; rw [sInf_toSubmodule]; rw [Submodule.coe_sInf]
  ext m
  simp only [mem_iInter, mem_ofPred_eq, forall_apply_eq_imp_iff₂, exists_imp,
    and_imp, SetLike.mem_coe, mem_toSubmodule]

@[simp]

Depends on / 依赖: LieSubmodule, LieSubmodule.coe_toSubmodule, SetLike, SetLike.mem_coe, Submodule, Submodule.coe_sInf, and_imp, coe_sInf, coe_toSubmodule, exists_imp, mem_coe, mem_iInter, mem_ofPred_eq, mem_toSubmodule, sInf_toSubmodule
-/
theorem coe_sInf (S : Set (LieSubmodule R L M)) : (↑(sInf S) : Set M) = ⋂ s in S, (s : Set M) := by
  rw [← LieSubmodule.coe_toSubmodule]; rw [sInf_toSubmodule]; rw [Submodule.coe_sInf]
  ext m
  simp only [mem_iInter, mem_ofPred_eq, forall_apply_eq_imp_iff₂, exists_imp,
    and_imp, SetLike.mem_coe, mem_toSubmodule]

@[simp]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι} (p : ι -> LieSubmodule R L M)
  statement: (↑(⨅ i, p i) : Set M) = ⋂ i, ↑(p i)
  proof: by
  rw [iInf]; rw [coe_sInf]; simp only [Set.mem_range, Set.iInter_exists, Set.iInter_iInter_eq']

@[simp]

中文:
定理 coe_iInf
  条件: {ι} (p : ι -> LieSubmodule R L M)
  结论: (↑(⨅ i, p i) : Set M) = ⋂ i, ↑(p i)
  证明: by
  rw [iInf]; rw [coe_sInf]; simp only [Set.mem_range, Set.iInter_exists, Set.iInter_iInter_eq']

@[simp]

Depends on / 依赖: Set.iInter_exists, Set.iInter_iInter_eq, Set.mem_range, coe_sInf, iInter_exists, iInter_iInter_eq, mem_range
-/
theorem coe_iInf {ι} (p : ι -> LieSubmodule R L M) : (↑(⨅ i, p i) : Set M) = ⋂ i, ↑(p i) := by
  rw [iInf]; rw [coe_sInf]; simp only [Set.mem_range, Set.iInter_exists, Set.iInter_iInter_eq']

@[simp]
/--
theorem `mem_iInf` / 定理 `mem_iInf`

English:
theorem mem_iInf
  given: {ι} (p : ι -> LieSubmodule R L M) {x}
  statement: x in ⨅ i, p i ↔ forall i, x in p i
  proof: by
  rw [← SetLike.mem_coe]; rw [coe_iInf]; rw [Set.mem_iInter]; rfl

中文:
定理 mem_iInf
  条件: {ι} (p : ι -> LieSubmodule R L M) {x}
  结论: x in ⨅ i, p i ↔ 对任意 i, x in p i
  证明: by
  rw [← SetLike.mem_coe]; rw [coe_iInf]; rw [Set.mem_iInter]; rfl

Depends on / 依赖: Set.mem_iInter, SetLike, SetLike.mem_coe, coe_iInf, mem_coe, mem_iInter
-/
theorem mem_iInf {ι} (p : ι -> LieSubmodule R L M) {x} : x in ⨅ i, p i ↔ forall i, x in p i := by
  rw [← SetLike.mem_coe]; rw [coe_iInf]; rw [Set.mem_iInter]; rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (LieSubmodule R L M)
  body: { toSubmodule := (N : Submodule R M) ⊔ (N' : Submodule R M)
      lie_mem := by
        rintro x m (hm : m in (N : Submodule R M) ⊔ (N' : Submodule R M))
        change ⁅x, m⁆ in (N : Submodule R M) ⊔ (N' : Submodule R M)
        rw [Submodule.mem_sup] at hm ⊢
        obtain ⟨y, hy, z, hz, rfl⟩ := h

中文:
实例 :
  签名: Max (LieSubmodule R L M)
  定义体: { toSubmodule := (N : Submodule R M) ⊔ (N' : Submodule R M)
      lie_mem := by
        rintro x m (hm : m in (N : Submodule R M) ⊔ (N' : Submodule R M))
        change ⁅x, m⁆ in (N : Submodule R M) ⊔ (N' : Submodule R M)
        rw [Submodule.mem_sup] at hm ⊢
        obtain ⟨y, hy, z, hz, rfl⟩ := h

Depends on / 依赖: N.lie_mem, Submodule, Submodule.mem_sup, lie_add, lie_mem, mem_sup, toSubmodule
-/
instance : Max (LieSubmodule R L M) where
  max N N' :=
    { toSubmodule := (N : Submodule R M) ⊔ (N' : Submodule R M)
      lie_mem := by
        rintro x m (hm : m in (N : Submodule R M) ⊔ (N' : Submodule R M))
        change ⁅x, m⁆ in (N : Submodule R M) ⊔ (N' : Submodule R M)
        rw [Submodule.mem_sup] at hm ⊢
        obtain ⟨y, hy, z, hz, rfl⟩ := hm
        exact ⟨⁅x, y⁆, N.lie_mem hy, ⁅x, z⁆, N'.lie_mem hz, (lie_add _ _ _).symm⟩ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SupSet (LieSubmodule R L M)
  body: { toSubmodule := sSup {(p : Submodule R M) | p in S}
      lie_mem := by
        intro x m (hm : m in sSup {(p : Submodule R M) | p in S})
        change ⁅x, m⁆ in sSup {(p : Submodule R M) | p in S}
        obtain ⟨s, hs, hsm⟩ := Submodule.mem_sSup_iff_exists_finset.mp hm
        clear hm
        i

中文:
实例 :
  签名: SupSet (LieSubmodule R L M)
  定义体: { toSubmodule := sSup {(p : Submodule R M) | p in S}
      lie_mem := by
        intro x m (hm : m in sSup {(p : Submodule R M) | p in S})
        change ⁅x, m⁆ in sSup {(p : Submodule R M) | p in S}
        obtain ⟨s, hs, hsm⟩ := Submodule.mem_sSup_iff_exists_finset.mp hm
        clear hm
        i

Depends on / 依赖: Finset, Finset.iSup_insert, Finset.induction_on, Submodule, Submodule.mem_sSup_iff_exists_finset.mp, Submodule.mem_sup.mp, generalizing, iSup_insert, induction_on, insert, lie_add, lie_mem, mem_sSup_iff_exists_finset, mem_sup, replace, toSubmodule
-/
instance : SupSet (LieSubmodule R L M) where
  sSup S :=
    { toSubmodule := sSup {(p : Submodule R M) | p in S}
      lie_mem := by
        intro x m (hm : m in sSup {(p : Submodule R M) | p in S})
        change ⁅x, m⁆ in sSup {(p : Submodule R M) | p in S}
        obtain ⟨s, hs, hsm⟩ := Submodule.mem_sSup_iff_exists_finset.mp hm
        clear hm
        induction s using Finset.induction_on generalizing m with
        | empty =>
          replace hsm : m = 0 := by simpa using hsm
          simp [hsm]
        | insert q t hqt ih =>
          rw [Finset.iSup_insert] at hsm
          obtain ⟨m', hm', u, hu, rfl⟩ := Submodule.mem_sup.mp hsm
          rw [lie_add]
          refine add_mem ?_ (ih (Subset.trans (by simp) hs) hu)
          obtain ⟨p, hp, rfl⟩ : exists p in S, ↑p = q := hs (Finset.mem_insert_self q t)
          suffices p <= sSup {(p : Submodule R M) | p in S} by exact this (p.lie_mem hm')
          exact le_sSup ⟨p, hp, rfl⟩ }

@[norm_cast, simp]
/--
theorem `sup_toSubmodule` / 定理 `sup_toSubmodule`

English:
theorem sup_toSubmodule
  proof: by
  rfl

@[simp]

中文:
定理 sup_toSubmodule
  证明: by
  rfl

@[simp]
-/
theorem sup_toSubmodule :
    (↑(N ⊔ N') : Submodule R M) = (N : Submodule R M) ⊔ (N' : Submodule R M) := by
  rfl

@[simp]
/--
theorem `sSup_toSubmodule` / 定理 `sSup_toSubmodule`

English:
theorem sSup_toSubmodule
  given: (S : Set (LieSubmodule R L M))
  proof: rfl

中文:
定理 sSup_toSubmodule
  条件: (S : Set (LieSubmodule R L M))
  证明: rfl
-/
theorem sSup_toSubmodule (S : Set (LieSubmodule R L M)) :
    (↑(sSup S) : Submodule R M) = sSup {(s : Submodule R M) | s in S} :=
  rfl

/--
theorem `sSup_toSubmodule_eq_iSup` / 定理 `sSup_toSubmodule_eq_iSup`

English:
theorem sSup_toSubmodule_eq_iSup
  given: (S : Set (LieSubmodule R L M))
  proof: by
  rw [sSup_toSubmodule]; rw [← Set.image]; rw [sSup_image]

@[simp]

中文:
定理 sSup_toSubmodule_eq_iSup
  条件: (S : Set (LieSubmodule R L M))
  证明: by
  rw [sSup_toSubmodule]; rw [← Set.image]; rw [sSup_image]

@[simp]

Depends on / 依赖: Set.image, sSup_image, sSup_toSubmodule
-/
theorem sSup_toSubmodule_eq_iSup (S : Set (LieSubmodule R L M)) :
    (↑(sSup S) : Submodule R M) = ⨆ N in S, (N : Submodule R M) := by
  rw [sSup_toSubmodule]; rw [← Set.image]; rw [sSup_image]

@[simp]
/--
theorem `iSup_toSubmodule` / 定理 `iSup_toSubmodule`

English:
theorem iSup_toSubmodule
  given: {ι} (p : ι -> LieSubmodule R L M)
  proof: by
  rw [iSup]; rw [sSup_toSubmodule]; ext; simp [Submodule.mem_sSup, Submodule.mem_iSup]

中文:
定理 iSup_toSubmodule
  条件: {ι} (p : ι -> LieSubmodule R L M)
  证明: by
  rw [iSup]; rw [sSup_toSubmodule]; ext; simp [Submodule.mem_sSup, Submodule.mem_iSup]

Depends on / 依赖: Submodule, Submodule.mem_iSup, Submodule.mem_sSup, mem_iSup, mem_sSup, sSup_toSubmodule
-/
theorem iSup_toSubmodule {ι} (p : ι -> LieSubmodule R L M) :
    (↑(⨆ i, p i) : Submodule R M) = ⨆ i, (p i : Submodule R M) := by
  rw [iSup]; rw [sSup_toSubmodule]; ext; simp [Submodule.mem_sSup, Submodule.mem_iSup]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (LieSubmodule R L M)
  body: toSubmodule_injective.completeLattice toSubmodule .rfl .rfl sup_toSubmodule inf_toSubmodule
    sSup_toSubmodule_eq_iSup sInf_toSubmodule_eq_iInf rfl rfl

中文:
实例 :
  签名: CompleteLattice (LieSubmodule R L M)
  定义体: toSubmodule_injective.completeLattice toSubmodule .rfl .rfl sup_toSubmodule inf_toSubmodule
    sSup_toSubmodule_eq_iSup sInf_toSubmodule_eq_iInf rfl rfl

Depends on / 依赖: completeLattice, inf_toSubmodule, sInf_toSubmodule_eq_iInf, sSup_toSubmodule_eq_iSup, sup_toSubmodule, toSubmodule, toSubmodule_injective, toSubmodule_injective.completeLattice
-/
instance : CompleteLattice (LieSubmodule R L M) :=
  toSubmodule_injective.completeLattice toSubmodule .rfl .rfl sup_toSubmodule inf_toSubmodule
    sSup_toSubmodule_eq_iSup sInf_toSubmodule_eq_iInf rfl rfl

/--
theorem `mem_iSup_of_mem` / 定理 `mem_iSup_of_mem`

English:
theorem mem_iSup_of_mem
  given: {ι} {b : M} {N : ι -> LieSubmodule R L M} (i : ι) (h : b in N i)
  proof: (le_iSup N i) h

@[elab_as_elim]

中文:
定理 mem_iSup_of_mem
  条件: {ι} {b : M} {N : ι -> LieSubmodule R L M} (i : ι) (h : b in N i)
  证明: (le_iSup N i) h

@[elab_as_elim]

Depends on / 依赖: le_iSup
-/
theorem mem_iSup_of_mem {ι} {b : M} {N : ι -> LieSubmodule R L M} (i : ι) (h : b in N i) :
    b in ⨆ i, N i :=
  (le_iSup N i) h

@[elab_as_elim]
/--
lemma `iSup_induction` / 引理 `iSup_induction`

English:
lemma iSup_induction
  statement: {ι} (N : ι -> LieSubmodule R L M) {motive : M -> Prop} {x : M}
  proof: by
  rw [← LieSubmodule.mem_toSubmodule]; rw [LieSubmodule.iSup_toSubmodule] at hx
  exact Submodule.iSup_induction (motive := motive) (fun i => (N i : Submodule R M)) hx mem zero add

@[elab_as_elim]

中文:
引理 iSup_induction
  结论: {ι} (N : ι -> LieSubmodule R L M) {motive : M -> 命题} {x : M}
  证明: by
  rw [← LieSubmodule.mem_toSubmodule]; rw [LieSubmodule.iSup_toSubmodule] at hx
  exact Submodule.iSup_induction (motive := motive) (fun i => (N i : Submodule R M)) hx mem zero add

@[elab_as_elim]

Depends on / 依赖: LieSubmodule, LieSubmodule.iSup_toSubmodule, LieSubmodule.mem_toSubmodule, Submodule, Submodule.iSup_induction, iSup_induction, iSup_toSubmodule, mem_toSubmodule, motive
-/
lemma iSup_induction {ι} (N : ι -> LieSubmodule R L M) {motive : M -> Prop} {x : M}
    (hx : x in ⨆ i, N i) (mem : forall i, forall y in N i, motive y) (zero : motive 0)
    (add : forall y z, motive y -> motive z -> motive (y + z)) : motive x := by
  rw [← LieSubmodule.mem_toSubmodule]; rw [LieSubmodule.iSup_toSubmodule] at hx
  exact Submodule.iSup_induction (motive := motive) (fun i => (N i : Submodule R M)) hx mem zero add

@[elab_as_elim]
/--
theorem `iSup_induction'` / 定理 `iSup_induction'`

English:
theorem iSup_induction'
  statement: {ι} (N : ι -> LieSubmodule R L M) {motive : (x : M) -> (x in ⨆ i, N i) -> Prop}
  proof: by
  refine Exists.elim ?_ fun (hx : x in ⨆ i, N i) (hc : motive x hx) => hc
  refine iSup_induction N (motive := fun x : M => exists (hx : x in ⨆ i, N i), motive x hx) hx
    (fun i x hx => ?_) ?_ fun x y => ?_
  · exact ⟨_, mem _ _ hx⟩
  · exact ⟨_, zero⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    exact ⟨_, a

中文:
定理 iSup_induction'
  结论: {ι} (N : ι -> LieSubmodule R L M) {motive : (x : M) -> (x in ⨆ i, N i) -> 命题}
  证明: by
  refine Exists.elim ?_ fun (hx : x in ⨆ i, N i) (hc : motive x hx) => hc
  refine iSup_induction N (motive := fun x : M => exists (hx : x in ⨆ i, N i), motive x hx) hx
    (fun i x hx => ?_) ?_ fun x y => ?_
  · exact ⟨_, mem _ _ hx⟩
  · exact ⟨_, zero⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    exact ⟨_, a

Depends on / 依赖: Exists, Exists.elim, iSup_induction, motive
-/
theorem iSup_induction' {ι} (N : ι -> LieSubmodule R L M) {motive : (x : M) -> (x in ⨆ i, N i) -> Prop}
    (mem : forall (i) (x) (hx : x in N i), motive x (mem_iSup_of_mem i hx)) (zero : motive 0 (zero_mem _))
    (add : forall x y hx hy, motive x hx -> motive y hy -> motive (x + y) (add_mem ‹_› ‹_›)) {x : M}
    (hx : x in ⨆ i, N i) : motive x hx := by
  refine Exists.elim ?_ fun (hx : x in ⨆ i, N i) (hc : motive x hx) => hc
  refine iSup_induction N (motive := fun x : M => exists (hx : x in ⨆ i, N i), motive x hx) hx
    (fun i x hx => ?_) ?_ fun x y => ?_
  · exact ⟨_, mem _ _ hx⟩
  · exact ⟨_, zero⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    exact ⟨_, add _ _ _ _ Cx Cy⟩

variable {N N'}

/--
lemma `disjoint_toSubmodule` / 引理 `disjoint_toSubmodule`

English:
lemma disjoint_toSubmodule
  proof: by
  rw [disjoint_iff]; rw [disjoint_iff]; rw [← toSubmodule_inj]; rw [inf_toSubmodule]; rw [bot_toSubmodule]; rw [← disjoint_iff]

中文:
引理 disjoint_toSubmodule
  证明: by
  rw [disjoint_iff]; rw [disjoint_iff]; rw [← toSubmodule_inj]; rw [inf_toSubmodule]; rw [bot_toSubmodule]; rw [← disjoint_iff]
-/
@[simp] lemma disjoint_toSubmodule :
    Disjoint (N : Submodule R M) (N' : Submodule R M) ↔ Disjoint N N' := by
  rw [disjoint_iff]; rw [disjoint_iff]; rw [← toSubmodule_inj]; rw [inf_toSubmodule]; rw [bot_toSubmodule]; rw [← disjoint_iff]

/--
lemma `codisjoint_toSubmodule` / 引理 `codisjoint_toSubmodule`

English:
lemma codisjoint_toSubmodule
  proof: by
  rw [codisjoint_iff]; rw [codisjoint_iff]; rw [← toSubmodule_inj]; rw [sup_toSubmodule]; rw [top_toSubmodule]; rw [← codisjoint_iff]

中文:
引理 codisjoint_toSubmodule
  证明: by
  rw [codisjoint_iff]; rw [codisjoint_iff]; rw [← toSubmodule_inj]; rw [sup_toSubmodule]; rw [top_toSubmodule]; rw [← codisjoint_iff]
-/
@[simp] lemma codisjoint_toSubmodule :
    Codisjoint (N : Submodule R M) (N' : Submodule R M) ↔ Codisjoint N N' := by
  rw [codisjoint_iff]; rw [codisjoint_iff]; rw [← toSubmodule_inj]; rw [sup_toSubmodule]; rw [top_toSubmodule]; rw [← codisjoint_iff]

/--
lemma `isCompl_toSubmodule` / 引理 `isCompl_toSubmodule`

English:
lemma isCompl_toSubmodule
  proof: by
  simp [isCompl_iff]

中文:
引理 isCompl_toSubmodule
  证明: by
  simp [isCompl_iff]
-/
@[simp] lemma isCompl_toSubmodule :
    IsCompl (N : Submodule R M) (N' : Submodule R M) ↔ IsCompl N N' := by
  simp [isCompl_iff]

/--
lemma `iSupIndep_toSubmodule` / 引理 `iSupIndep_toSubmodule`

English:
lemma iSupIndep_toSubmodule
  given: {ι : Type*} {N : ι -> LieSubmodule R L M}
  proof: by
  simp [iSupIndep_def, ← disjoint_toSubmodule]

中文:
引理 iSupIndep_toSubmodule
  条件: {ι : 类型} {N : ι -> LieSubmodule R L M}
  证明: by
  simp [iSupIndep_def, ← disjoint_toSubmodule]
-/
@[simp] lemma iSupIndep_toSubmodule {ι : Type*} {N : ι -> LieSubmodule R L M} :
    iSupIndep (fun i => (N i : Submodule R M)) ↔ iSupIndep N := by
  simp [iSupIndep_def, ← disjoint_toSubmodule]

/--
lemma `iSup_toSubmodule_eq_top` / 引理 `iSup_toSubmodule_eq_top`

English:
lemma iSup_toSubmodule_eq_top
  given: {ι : Sort*} {N : ι -> LieSubmodule R L M}
  proof: by
  rw [← iSup_toSubmodule]; rw [← top_toSubmodule (L := L)]; rw [toSubmodule_inj]

中文:
引理 iSup_toSubmodule_eq_top
  条件: {ι : Sort*} {N : ι -> LieSubmodule R L M}
  证明: by
  rw [← iSup_toSubmodule]; rw [← top_toSubmodule (L := L)]; rw [toSubmodule_inj]
-/
@[simp] lemma iSup_toSubmodule_eq_top {ι : Sort*} {N : ι -> LieSubmodule R L M} :
    ⨆ i, (N i : Submodule R M) = ⊤ ↔ ⨆ i, N i = ⊤ := by
  rw [← iSup_toSubmodule]; rw [← top_toSubmodule (L := L)]; rw [toSubmodule_inj]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (LieSubmodule R L M)
  body: max

中文:
实例 :
  签名: Add (LieSubmodule R L M)
  定义体: max
-/
instance : Add (LieSubmodule R L M) where add := max

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid (LieSubmodule R L M)
  body: sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  nsmul := nsmulRec

中文:
实例 :
  签名: AddCommMonoid (LieSubmodule R L M)
  定义体: sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  nsmul := nsmulRec

Depends on / 依赖: sup_assoc
-/
instance : AddCommMonoid (LieSubmodule R L M) where
  add_assoc := sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  nsmul := nsmulRec

variable (N N')

@[simp]
/--
theorem `add_eq_sup` / 定理 `add_eq_sup`

English:
theorem add_eq_sup
  statement: N + N' = N ⊔ N'
  proof: rfl

@[simp]

中文:
定理 add_eq_sup
  结论: N + N' = N ⊔ N'
  证明: rfl

@[simp]
-/
theorem add_eq_sup : N + N' = N ⊔ N' :=
  rfl

@[simp]
/--
theorem `mem_inf` / 定理 `mem_inf`

English:
theorem mem_inf
  given: (x : M)
  statement: x in N ⊓ N' ↔ x in N ∧ x in N'
  proof: by
  rw [← mem_toSubmodule]; rw [← mem_toSubmodule]; rw [← mem_toSubmodule]; rw [inf_toSubmodule]; rw [Submodule.mem_inf]

中文:
定理 mem_inf
  条件: (x : M)
  结论: x in N ⊓ N' ↔ x in N ∧ x in N'
  证明: by
  rw [← mem_toSubmodule]; rw [← mem_toSubmodule]; rw [← mem_toSubmodule]; rw [inf_toSubmodule]; rw [Submodule.mem_inf]

Depends on / 依赖: Submodule, Submodule.mem_inf, inf_toSubmodule, mem_inf, mem_toSubmodule
-/
theorem mem_inf (x : M) : x in N ⊓ N' ↔ x in N ∧ x in N' := by
  rw [← mem_toSubmodule]; rw [← mem_toSubmodule]; rw [← mem_toSubmodule]; rw [inf_toSubmodule]; rw [Submodule.mem_inf]

/--
theorem `mem_sup` / 定理 `mem_sup`

English:
theorem mem_sup
  given: (x : M)
  statement: x in N ⊔ N' ↔ exists y in N, exists z in N', y + z = x
  proof: by
  rw [← mem_toSubmodule]; rw [sup_toSubmodule]; rw [Submodule.mem_sup]; exact Iff.rfl

中文:
定理 mem_sup
  条件: (x : M)
  结论: x in N ⊔ N' ↔ 存在 y in N, 存在 z in N', y + z = x
  证明: by
  rw [← mem_toSubmodule]; rw [sup_toSubmodule]; rw [Submodule.mem_sup]; exact Iff.rfl

Depends on / 依赖: Iff.rfl, Submodule, Submodule.mem_sup, mem_sup, mem_toSubmodule, sup_toSubmodule
-/
theorem mem_sup (x : M) : x in N ⊔ N' ↔ exists y in N, exists z in N', y + z = x := by
  rw [← mem_toSubmodule]; rw [sup_toSubmodule]; rw [Submodule.mem_sup]; exact Iff.rfl

variable {N N'} in
/--
theorem `mem_sup_left` / 定理 `mem_sup_left`

English:
theorem mem_sup_left
  given: {x : M} (hx : x in N)
  statement: x in N ⊔ N'
  proof: le_sup_left (a := N) hx

中文:
定理 mem_sup_left
  条件: {x : M} (hx : x in N)
  结论: x in N ⊔ N'
  证明: le_sup_left (a := N) hx

Depends on / 依赖: le_sup_left
-/
theorem mem_sup_left {x : M} (hx : x in N) : x in N ⊔ N' :=
  le_sup_left (a := N) hx

variable {N N'} in
/--
theorem `mem_sup_right` / 定理 `mem_sup_right`

English:
theorem mem_sup_right
  given: {x : M} (hx : x in N')
  statement: x in N ⊔ N'
  proof: (mem_sup _ _ _).mpr ⟨0, by simp, x, hx, by simp⟩

nonrec theorem eq_bot_iff : N = ⊥ ↔ forall m : M, m in N -> m = 0 := by rw [eq_bot_iff]; exact Iff.rfl

中文:
定理 mem_sup_right
  条件: {x : M} (hx : x in N')
  结论: x in N ⊔ N'
  证明: (mem_sup _ _ _).mpr ⟨0, by simp, x, hx, by simp⟩

nonrec theorem eq_bot_iff : N = ⊥ ↔ forall m : M, m in N -> m = 0 := by rw [eq_bot_iff]; exact Iff.rfl

Depends on / 依赖: mem_sup
-/
theorem mem_sup_right {x : M} (hx : x in N') : x in N ⊔ N' :=
  (mem_sup _ _ _).mpr ⟨0, by simp, x, hx, by simp⟩

nonrec theorem eq_bot_iff : N = ⊥ ↔ forall m : M, m in N -> m = 0 := by rw [eq_bot_iff]; exact Iff.rfl

/--
Instance `subsingleton_of_bot` / 实例 `subsingleton_of_bot`

English:
instance subsingleton_of_bot
  signature: : Subsingleton (LieSubmodule R L (⊥ : LieSubmodule R L M))
  body: by
  apply subsingleton_of_bot_eq_top
  subsingleton

中文:
实例 subsingleton_of_bot
  签名: : Subsingleton (LieSubmodule R L (⊥ : LieSubmodule R L M))
  定义体: by
  apply subsingleton_of_bot_eq_top
  subsingleton

Depends on / 依赖: subsingleton, subsingleton_of_bot_eq_top
-/
instance subsingleton_of_bot : Subsingleton (LieSubmodule R L (⊥ : LieSubmodule R L M)) := by
  apply subsingleton_of_bot_eq_top
  subsingleton

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsModularLattice (LieSubmodule R L M)
  body: by
    simp only [← toSubmodule_le_toSubmodule, sup_toSubmodule, inf_toSubmodule]
    exact IsModularLattice.sup_inf_le_assoc_of_le _

中文:
实例 :
  签名: IsModularLattice (LieSubmodule R L M)
  定义体: by
    simp only [← toSubmodule_le_toSubmodule, sup_toSubmodule, inf_toSubmodule]
    exact IsModularLattice.sup_inf_le_assoc_of_le _

Depends on / 依赖: IsModularLattice, IsModularLattice.sup_inf_le_assoc_of_le, inf_toSubmodule, sup_inf_le_assoc_of_le, sup_toSubmodule, toSubmodule_le_toSubmodule
-/
instance : IsModularLattice (LieSubmodule R L M) where
  sup_inf_le_assoc_of_le _ _ := by
    simp only [← toSubmodule_le_toSubmodule, sup_toSubmodule, inf_toSubmodule]
    exact IsModularLattice.sup_inf_le_assoc_of_le _

variable (R L M)

/--
Definition of `toSubmodule_orderEmbedding` / `toSubmodule_orderEmbedding` 的定义

English:
definition toSubmodule_orderEmbedding
  signature: : LieSubmodule R L M ↪o Submodule R M
  body: { toFun := (↑)
    inj' := toSubmodule_injective
    map_rel_iff' := Iff.rfl }

中文:
定义 toSubmodule_orderEmbedding
  签名: : LieSubmodule R L M ↪o Submodule R M
  定义体: { toFun := (↑)
    inj' := toSubmodule_injective
    map_rel_iff' := Iff.rfl }
-/
@[simps] def toSubmodule_orderEmbedding : LieSubmodule R L M ↪o Submodule R M :=
  { toFun := (↑)
    inj' := toSubmodule_injective
    map_rel_iff' := Iff.rfl }

/--
Instance `wellFoundedGT_of_noetherian` / 实例 `wellFoundedGT_of_noetherian`

English:
instance wellFoundedGT_of_noetherian
  signature: [IsNoetherian R M]
  body: RelHomClass.isWellFounded (toSubmodule_orderEmbedding R L M).dual.ltEmbedding

中文:
实例 wellFoundedGT_of_noetherian
  签名: [IsNoetherian R M]
  定义体: RelHomClass.isWellFounded (toSubmodule_orderEmbedding R L M).dual.ltEmbedding

Depends on / 依赖: RelHomClass, RelHomClass.isWellFounded, dual.ltEmbedding, isWellFounded, ltEmbedding, toSubmodule_orderEmbedding
-/
instance wellFoundedGT_of_noetherian [IsNoetherian R M] : WellFoundedGT (LieSubmodule R L M) :=
  RelHomClass.isWellFounded (toSubmodule_orderEmbedding R L M).dual.ltEmbedding

/--
theorem `wellFoundedLT_of_isArtinian` / 定理 `wellFoundedLT_of_isArtinian`

English:
theorem wellFoundedLT_of_isArtinian
  given: [IsArtinian R M]
  statement: WellFoundedLT (LieSubmodule R L M)
  proof: RelHomClass.isWellFounded (toSubmodule_orderEmbedding R L M).ltEmbedding

中文:
定理 wellFoundedLT_of_isArtinian
  条件: [IsArtinian R M]
  结论: WellFoundedLT (LieSubmodule R L M)
  证明: RelHomClass.isWellFounded (toSubmodule_orderEmbedding R L M).ltEmbedding

Depends on / 依赖: Algebra, RelHomClass, RelHomClass.isWellFounded, Semiring, Submonoid, isWellFounded, ltEmbedding, toSubmodule_orderEmbedding
-/
theorem wellFoundedLT_of_isArtinian [IsArtinian R M] : WellFoundedLT (LieSubmodule R L M) :=
  RelHomClass.isWellFounded (toSubmodule_orderEmbedding R L M).ltEmbedding

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsArtinian
  signature: R M] : IsAtomic (LieSubmodule R L M)
  body: isAtomic_of_orderBot_wellFounded_lt (wellFoundedLT_of_isArtinian R L M).wf

@[simp]

中文:
实例 [IsArtinian
  签名: R M] : IsAtomic (LieSubmodule R L M)
  定义体: isAtomic_of_orderBot_wellFounded_lt (wellFoundedLT_of_isArtinian R L M).wf

@[simp]

Depends on / 依赖: isAtomic_of_orderBot_wellFounded_lt, wellFoundedLT_of_isArtinian
-/
instance [IsArtinian R M] : IsAtomic (LieSubmodule R L M) :=
isAtomic_of_orderBot_wellFounded_lt (wellFoundedLT_of_isArtinian R L M).wf

@[simp]
/--
theorem `subsingleton_iff` / 定理 `subsingleton_iff`

English:
theorem subsingleton_iff
  statement: Subsingleton (LieSubmodule R L M) ↔ Subsingleton M
  proof: have h : Subsingleton (LieSubmodule R L M) ↔ Subsingleton (Submodule R M) := by
    rw [← subsingleton_iff_bot_eq_top]; rw [← subsingleton_iff_bot_eq_top]; rw [← toSubmodule_inj]; rw [top_toSubmodule]; rw [bot_toSubmodule]
h.trans Submodule.subsingleton_iff R

@[simp]

中文:
定理 subsingleton_iff
  结论: Subsingleton (LieSubmodule R L M) ↔ Subsingleton M
  证明: have h : Subsingleton (LieSubmodule R L M) ↔ Subsingleton (Submodule R M) := by
    rw [← subsingleton_iff_bot_eq_top]; rw [← subsingleton_iff_bot_eq_top]; rw [← toSubmodule_inj]; rw [top_toSubmodule]; rw [bot_toSubmodule]
h.trans Submodule.subsingleton_iff R

@[simp]

Depends on / 依赖: LieSubmodule, Submodule, Submodule.subsingleton_iff, Subsingleton, bot_toSubmodule, h.trans, subsingleton_iff, subsingleton_iff_bot_eq_top, toSubmodule_inj, top_toSubmodule
-/
theorem subsingleton_iff : Subsingleton (LieSubmodule R L M) ↔ Subsingleton M :=
  have h : Subsingleton (LieSubmodule R L M) ↔ Subsingleton (Submodule R M) := by
    rw [← subsingleton_iff_bot_eq_top]; rw [← subsingleton_iff_bot_eq_top]; rw [← toSubmodule_inj]; rw [top_toSubmodule]; rw [bot_toSubmodule]
h.trans Submodule.subsingleton_iff R

@[simp]
/--
theorem `nontrivial_iff` / 定理 `nontrivial_iff`

English:
theorem nontrivial_iff
  statement: Nontrivial (LieSubmodule R L M) ↔ Nontrivial M
  proof: not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans <| subsingleton_iff R L M).trans
      not_nontrivial_iff_subsingleton.symm)

中文:
定理 nontrivial_iff
  结论: Nontrivial (LieSubmodule R L M) ↔ Nontrivial M
  证明: not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans <| subsingleton_iff R L M).trans
      not_nontrivial_iff_subsingleton.symm)

Depends on / 依赖: not_iff_not, not_iff_not.mp, not_nontrivial_iff_subsingleton, not_nontrivial_iff_subsingleton.symm, not_nontrivial_iff_subsingleton.trans, subsingleton_iff
-/
theorem nontrivial_iff : Nontrivial (LieSubmodule R L M) ↔ Nontrivial M :=
  not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans <| subsingleton_iff R L M).trans
      not_nontrivial_iff_subsingleton.symm)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: M] : Nontrivial (LieSubmodule R L M)
  body: (nontrivial_iff R L M).mpr ‹_›

中文:
实例 [Nontrivial
  签名: M] : Nontrivial (LieSubmodule R L M)
  定义体: (nontrivial_iff R L M).mpr ‹_›

Depends on / 依赖: Algebra, Semiring, Submonoid, nontrivial_iff
-/
instance [Nontrivial M] : Nontrivial (LieSubmodule R L M) :=
  (nontrivial_iff R L M).mpr ‹_›

/--
theorem `nontrivial_iff_ne_bot` / 定理 `nontrivial_iff_ne_bot`

English:
theorem nontrivial_iff_ne_bot
  given: {N : LieSubmodule R L M}
  statement: Nontrivial N ↔ N != ⊥
  proof: by
  constructor
  · rintro ⟨⟨m₁, h₁⟩, ⟨m₂, h₂⟩, h₁₂⟩ rfl
    simp [(LieSubmodule.mem_bot _).mp h₁, (LieSubmodule.mem_bot _).mp h₂] at h₁₂
  · contrapose!
    rw [LieSubmodule.eq_bot_iff]
    rintro ⟨h⟩ m hm
    simpa using h ⟨m, hm⟩ ⟨_, N.zero_mem⟩

中文:
定理 nontrivial_iff_ne_bot
  条件: {N : LieSubmodule R L M}
  结论: Nontrivial N ↔ N != ⊥
  证明: by
  constructor
  · rintro ⟨⟨m₁, h₁⟩, ⟨m₂, h₂⟩, h₁₂⟩ rfl
    simp [(LieSubmodule.mem_bot _).mp h₁, (LieSubmodule.mem_bot _).mp h₂] at h₁₂
  · contrapose!
    rw [LieSubmodule.eq_bot_iff]
    rintro ⟨h⟩ m hm
    simpa using h ⟨m, hm⟩ ⟨_, N.zero_mem⟩

Depends on / 依赖: Algebra, CommSemiring, LieSubmodule, LieSubmodule.eq_bot_iff, LieSubmodule.mem_bot, N.zero_mem, Submonoid, contrapose, eq_bot_iff, mem_bot, zero_mem
-/
theorem nontrivial_iff_ne_bot {N : LieSubmodule R L M} : Nontrivial N ↔ N != ⊥ := by
  constructor
  · rintro ⟨⟨m₁, h₁⟩, ⟨m₂, h₂⟩, h₁₂⟩ rfl
    simp [(LieSubmodule.mem_bot _).mp h₁, (LieSubmodule.mem_bot _).mp h₂] at h₁₂
  · contrapose!
    rw [LieSubmodule.eq_bot_iff]
    rintro ⟨h⟩ m hm
    simpa using h ⟨m, hm⟩ ⟨_, N.zero_mem⟩

variable {R L M}

section InclusionMaps

/--
Definition of `incl` / `incl` 的定义

English:
definition incl
  signature: : N ->ₗ⁅R,L⁆ M
  body: { Submodule.subtype (N : Submodule R M) with map_lie' := fun {_ _} => rfl }

@[simp]

中文:
定义 incl
  签名: : N ->ₗ⁅R,L⁆ M
  定义体: { Submodule.subtype (N : Submodule R M) with map_lie' := fun {_ _} => rfl }

@[simp]

Depends on / 依赖: Algebra, Submodule, Submodule.subtype, Submonoid, map_lie, subtype
-/
def incl : N ->ₗ⁅R,L⁆ M :=
  { Submodule.subtype (N : Submodule R M) with map_lie' := fun {_ _} => rfl }

@[simp]
/--
theorem `incl_coe` / 定理 `incl_coe`

English:
theorem incl_coe
  statement: (N.incl : N ->ₗ[R] M) = (N : Submodule R M).subtype
  proof: rfl

@[simp]

中文:
定理 incl_coe
  结论: (N.incl : N ->ₗ[R] M) = (N : Submodule R M).subtype
  证明: rfl

@[simp]

Depends on / 依赖: Algebra, CommRing, Submonoid
-/
theorem incl_coe : (N.incl : N ->ₗ[R] M) = (N : Submodule R M).subtype :=
  rfl

@[simp]
/--
theorem `incl_apply` / 定理 `incl_apply`

English:
theorem incl_apply
  given: (m : N)
  statement: N.incl m = m
  proof: rfl

中文:
定理 incl_apply
  条件: (m : N)
  结论: N.incl m = m
  证明: rfl
-/
theorem incl_apply (m : N) : N.incl m = m :=
  rfl

/--
theorem `incl_eq_val` / 定理 `incl_eq_val`

English:
theorem incl_eq_val
  statement: (N.incl : N -> M) = Subtype.val
  proof: rfl

中文:
定理 incl_eq_val
  结论: (N.incl : N -> M) = Subtype.val
  证明: rfl
-/
theorem incl_eq_val : (N.incl : N -> M) = Subtype.val :=
  rfl

/--
theorem `injective_incl` / 定理 `injective_incl`

English:
theorem injective_incl
  statement: Function.Injective N.incl
  proof: Subtype.coe_injective

中文:
定理 injective_incl
  结论: Function.Injective N.incl
  证明: Subtype.coe_injective

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
theorem injective_incl : Function.Injective N.incl := Subtype.coe_injective

variable {N N'}
variable (h : N <= N')

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: : N ->ₗ⁅R,L⁆ N' where
  body: Submodule.inclusion (show N.toSubmodule <= N'.toSubmodule from h)
  map_lie' := rfl

@[simp]

中文:
定义 inclusion
  签名: : N ->ₗ⁅R,L⁆ N' where
  定义体: Submodule.inclusion (show N.toSubmodule <= N'.toSubmodule from h)
  map_lie' := rfl

@[simp]

Depends on / 依赖: N.toSubmodule, Submodule, Submodule.inclusion, inclusion, toSubmodule
-/
def inclusion : N ->ₗ⁅R,L⁆ N' where
  __ := Submodule.inclusion (show N.toSubmodule <= N'.toSubmodule from h)
  map_lie' := rfl

@[simp]
/--
theorem `coe_inclusion` / 定理 `coe_inclusion`

English:
theorem coe_inclusion
  given: (m : N)
  statement: (inclusion h m : M) = m
  proof: rfl

中文:
定理 coe_inclusion
  条件: (m : N)
  结论: (inclusion h m : M) = m
  证明: rfl
-/
theorem coe_inclusion (m : N) : (inclusion h m : M) = m :=
  rfl

/--
theorem `inclusion_apply` / 定理 `inclusion_apply`

English:
theorem inclusion_apply
  given: (m : N)
  statement: inclusion h m = ⟨m.1, h m.2⟩
  proof: rfl

中文:
定理 inclusion_apply
  条件: (m : N)
  结论: inclusion h m = ⟨m.1, h m.2⟩
  证明: rfl
-/
theorem inclusion_apply (m : N) : inclusion h m = ⟨m.1, h m.2⟩ :=
  rfl

/--
theorem `inclusion_injective` / 定理 `inclusion_injective`

English:
theorem inclusion_injective
  statement: Function.Injective (inclusion h)
  proof: fun x y => by
  simp only [inclusion_apply, imp_self, Subtype.mk_eq_mk, SetLike.coe_eq_coe]

中文:
定理 inclusion_injective
  结论: Function.Injective (inclusion h)
  证明: fun x y => by
  simp only [inclusion_apply, imp_self, Subtype.mk_eq_mk, SetLike.coe_eq_coe]

Depends on / 依赖: SetLike, SetLike.coe_eq_coe, Subtype, Subtype.mk_eq_mk, coe_eq_coe, imp_self, inclusion_apply, mk_eq_mk
-/
theorem inclusion_injective : Function.Injective (inclusion h) := fun x y => by
  simp only [inclusion_apply, imp_self, Subtype.mk_eq_mk, SetLike.coe_eq_coe]

end InclusionMaps

section LieSpan

variable (R L) (s : Set M)

/--
Definition of `lieSpan` / `lieSpan` 的定义

English:
definition lieSpan
  signature: : LieSubmodule R L M
  body: sInf { N | s subseteq N }

中文:
定义 lieSpan
  签名: : LieSubmodule R L M
  定义体: sInf { N | s subseteq N }

Depends on / 依赖: subseteq
-/
def lieSpan : LieSubmodule R L M :=
  sInf { N | s subseteq N }

variable {R L s}

/--
theorem `mem_lieSpan` / 定理 `mem_lieSpan`

English:
theorem mem_lieSpan
  given: {x : M}
  statement: x in lieSpan R L s ↔ forall N : LieSubmodule R L M, s subseteq N -> x in N
  proof: by
  rw [← SetLike.mem_coe]; rw [lieSpan]; rw [coe_sInf]
  exact mem_iInter₂

中文:
定理 mem_lieSpan
  条件: {x : M}
  结论: x in lieSpan R L s ↔ 对任意 N : LieSubmodule R L M, s subseteq N -> x in N
  证明: by
  rw [← SetLike.mem_coe]; rw [lieSpan]; rw [coe_sInf]
  exact mem_iInter₂

Depends on / 依赖: SetLike, SetLike.mem_coe, coe_sInf, lieSpan, mem_coe
-/
theorem mem_lieSpan {x : M} : x in lieSpan R L s ↔ forall N : LieSubmodule R L M, s subseteq N -> x in N := by
  rw [← SetLike.mem_coe]; rw [lieSpan]; rw [coe_sInf]
  exact mem_iInter₂

/--
theorem `subset_lieSpan` / 定理 `subset_lieSpan`

English:
theorem subset_lieSpan
  statement: s subseteq lieSpan R L s
  proof: by
  intro m hm
  rw [SetLike.mem_coe]; rw [mem_lieSpan]
  intro N hN
  exact hN hm

中文:
定理 subset_lieSpan
  结论: s subseteq lieSpan R L s
  证明: by
  intro m hm
  rw [SetLike.mem_coe]; rw [mem_lieSpan]
  intro N hN
  exact hN hm

Depends on / 依赖: SetLike, SetLike.mem_coe, mem_coe, mem_lieSpan
-/
theorem subset_lieSpan : s subseteq lieSpan R L s := by
  intro m hm
  rw [SetLike.mem_coe]; rw [mem_lieSpan]
  intro N hN
  exact hN hm

/--
theorem `submodule_span_le_lieSpan` / 定理 `submodule_span_le_lieSpan`

English:
theorem submodule_span_le_lieSpan
  statement: Submodule.span R s <= lieSpan R L s
  proof: by
  rw [Submodule.span_le]
  apply subset_lieSpan

@[simp]

中文:
定理 submodule_span_le_lieSpan
  结论: Submodule.span R s <= lieSpan R L s
  证明: by
  rw [Submodule.span_le]
  apply subset_lieSpan

@[simp]

Depends on / 依赖: Submodule, Submodule.span_le, span_le, subset_lieSpan
-/
theorem submodule_span_le_lieSpan : Submodule.span R s <= lieSpan R L s := by
  rw [Submodule.span_le]
  apply subset_lieSpan

@[simp]
/--
theorem `lieSpan_le` / 定理 `lieSpan_le`

English:
theorem lieSpan_le
  given: {N}
  statement: lieSpan R L s <= N ↔ s subseteq N
  proof: by
  constructor
  · exact Subset.trans subset_lieSpan
  · intro hs m hm; rw [mem_lieSpan] at hm; exact hm _ hs

@[gcongr]

中文:
定理 lieSpan_le
  条件: {N}
  结论: lieSpan R L s <= N ↔ s subseteq N
  证明: by
  constructor
  · exact Subset.trans subset_lieSpan
  · intro hs m hm; rw [mem_lieSpan] at hm; exact hm _ hs

@[gcongr]

Depends on / 依赖: Subset, Subset.trans, mem_lieSpan, subset_lieSpan
-/
theorem lieSpan_le {N} : lieSpan R L s <= N ↔ s subseteq N := by
  constructor
  · exact Subset.trans subset_lieSpan
  · intro hs m hm; rw [mem_lieSpan] at hm; exact hm _ hs

@[gcongr]
/--
theorem `lieSpan_mono` / 定理 `lieSpan_mono`

English:
theorem lieSpan_mono
  given: {t : Set M} (h : s subseteq t)
  statement: lieSpan R L s <= lieSpan R L t
  proof: by
  rw [lieSpan_le]
  exact Subset.trans h subset_lieSpan

中文:
定理 lieSpan_mono
  条件: {t : Set M} (h : s subseteq t)
  结论: lieSpan R L s <= lieSpan R L t
  证明: by
  rw [lieSpan_le]
  exact Subset.trans h subset_lieSpan

Depends on / 依赖: Subset, Subset.trans, lieSpan_le, subset_lieSpan
-/
theorem lieSpan_mono {t : Set M} (h : s subseteq t) : lieSpan R L s <= lieSpan R L t := by
  rw [lieSpan_le]
  exact Subset.trans h subset_lieSpan

/--
theorem `lieSpan_eq` / 定理 `lieSpan_eq`

English:
theorem lieSpan_eq
  given: (N : LieSubmodule R L M)
  statement: lieSpan R L (N : Set M) = N
  proof: le_antisymm (lieSpan_le.mpr rfl.subset) subset_lieSpan

中文:
定理 lieSpan_eq
  条件: (N : LieSubmodule R L M)
  结论: lieSpan R L (N : Set M) = N
  证明: le_antisymm (lieSpan_le.mpr rfl.subset) subset_lieSpan

Depends on / 依赖: le_antisymm, lieSpan_le, lieSpan_le.mpr, mk_mul_mk, mul_assoc, rfl.subset, smul_def, smul_mul_assoc, subset, subset_lieSpan
-/
theorem lieSpan_eq (N : LieSubmodule R L M) : lieSpan R L (N : Set M) = N :=
  le_antisymm (lieSpan_le.mpr rfl.subset) subset_lieSpan

/--
theorem `coe_lieSpan_submodule_eq_iff` / 定理 `coe_lieSpan_submodule_eq_iff`

English:
theorem coe_lieSpan_submodule_eq_iff
  given: {p : Submodule R M}
  proof: by
  rw [p.exists_lieSubmodule_coe_eq_iff L]; constructor <;> intro h
  · intro x m hm; rw [← h, mem_toSubmodule]; exact lie_mem _ (subset_lieSpan hm)
  · rw [← toSubmodule_mk p @h, coe_toSubmodule, toSubmodule_inj, lieSpan_eq]

中文:
定理 coe_lieSpan_submodule_eq_iff
  条件: {p : Submodule R M}
  证明: by
  rw [p.exists_lieSubmodule_coe_eq_iff L]; constructor <;> intro h
  · intro x m hm; rw [← h, mem_toSubmodule]; exact lie_mem _ (subset_lieSpan hm)
  · rw [← toSubmodule_mk p @h, coe_toSubmodule, toSubmodule_inj, lieSpan_eq]

Depends on / 依赖: coe_toSubmodule, exists_lieSubmodule_coe_eq_iff, lieSpan_eq, lie_mem, mem_toSubmodule, p.exists_lieSubmodule_coe_eq_iff, subset_lieSpan, toSubmodule_inj, toSubmodule_mk
-/
theorem coe_lieSpan_submodule_eq_iff {p : Submodule R M} :
    (lieSpan R L (p : Set M) : Submodule R M) = p ↔ exists N : LieSubmodule R L M, ↑N = p := by
  rw [p.exists_lieSubmodule_coe_eq_iff L]; constructor <;> intro h
  · intro x m hm; rw [← h, mem_toSubmodule]; exact lie_mem _ (subset_lieSpan hm)
  · rw [← toSubmodule_mk p @h, coe_toSubmodule, toSubmodule_inj, lieSpan_eq]

variable (R L M)

/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion (lieSpan R L : Set M -> LieSubmodule R L M) (↑) where
  body: lieSpan R L s
  gc _ _ := lieSpan_le
  le_l_u _ := subset_lieSpan
  choice_eq _ _ := rfl

@[simp]

中文:
定义 gi
  签名: : GaloisInsertion (lieSpan R L : Set M -> LieSubmodule R L M) (↑) where
  定义体: lieSpan R L s
  gc _ _ := lieSpan_le
  le_l_u _ := subset_lieSpan
  choice_eq _ _ := rfl

@[simp]
-/
protected def gi : GaloisInsertion (lieSpan R L : Set M -> LieSubmodule R L M) (↑) where
  choice s _ := lieSpan R L s
  gc _ _ := lieSpan_le
  le_l_u _ := subset_lieSpan
  choice_eq _ _ := rfl

@[simp]
/--
theorem `span_empty` / 定理 `span_empty`

English:
theorem span_empty
  statement: lieSpan R L (∅ : Set M) = ⊥
  proof: (LieSubmodule.gi R L M).gc.l_bot

@[simp]

中文:
定理 span_empty
  结论: lieSpan R L (∅ : Set M) = ⊥
  证明: (LieSubmodule.gi R L M).gc.l_bot

@[simp]

Depends on / 依赖: LieSubmodule, LieSubmodule.gi, gc.l_bot, l_bot
-/
theorem span_empty : lieSpan R L (∅ : Set M) = ⊥ :=
  (LieSubmodule.gi R L M).gc.l_bot

@[simp]
/--
theorem `span_univ` / 定理 `span_univ`

English:
theorem span_univ
  statement: lieSpan R L (Set.univ : Set M) = ⊤
  proof: eq_top_iff.2 SetLike.le_def.2 subset_lieSpan

中文:
定理 span_univ
  结论: lieSpan R L (Set.univ : Set M) = ⊤
  证明: eq_top_iff.2 SetLike.le_def.2 subset_lieSpan

Depends on / 依赖: SetLike, SetLike.le_def, eq_top_iff, le_def, subset_lieSpan
-/
theorem span_univ : lieSpan R L (Set.univ : Set M) = ⊤ :=
eq_top_iff.2 SetLike.le_def.2 subset_lieSpan

/--
theorem `lieSpan_eq_bot_iff` / 定理 `lieSpan_eq_bot_iff`

English:
theorem lieSpan_eq_bot_iff
  statement: lieSpan R L s = ⊥ ↔ forall m in s, m = (0 : M)
  proof: by
  rw [_root_.eq_bot_iff]; rw [lieSpan_le]; rw [bot_coe]; rw [subset_singleton_iff]

中文:
定理 lieSpan_eq_bot_iff
  结论: lieSpan R L s = ⊥ ↔ 对任意 m in s, m = (0 : M)
  证明: by
  rw [_root_.eq_bot_iff]; rw [lieSpan_le]; rw [bot_coe]; rw [subset_singleton_iff]

Depends on / 依赖: _root_, _root_.eq_bot_iff, bot_coe, eq_bot_iff, lieSpan_le, subset_singleton_iff
-/
theorem lieSpan_eq_bot_iff : lieSpan R L s = ⊥ ↔ forall m in s, m = (0 : M) := by
  rw [_root_.eq_bot_iff]; rw [lieSpan_le]; rw [bot_coe]; rw [subset_singleton_iff]

variable {M}

/--
theorem `span_union` / 定理 `span_union`

English:
theorem span_union
  given: (s t : Set M)
  statement: lieSpan R L (s union t) = lieSpan R L s ⊔ lieSpan R L t
  proof: (LieSubmodule.gi R L M).gc.l_sup

中文:
定理 span_union
  条件: (s t : Set M)
  结论: lieSpan R L (s union t) = lieSpan R L s ⊔ lieSpan R L t
  证明: (LieSubmodule.gi R L M).gc.l_sup

Depends on / 依赖: LieSubmodule, LieSubmodule.gi, gc.l_sup, l_sup
-/
theorem span_union (s t : Set M) : lieSpan R L (s union t) = lieSpan R L s ⊔ lieSpan R L t :=
  (LieSubmodule.gi R L M).gc.l_sup

/--
theorem `span_iUnion` / 定理 `span_iUnion`

English:
theorem span_iUnion
  given: {ι} (s : ι -> Set M)
  statement: lieSpan R L (⋃ i, s i) = ⨆ i, lieSpan R L (s i)
  proof: (LieSubmodule.gi R L M).gc.l_iSup

中文:
定理 span_iUnion
  条件: {ι} (s : ι -> Set M)
  结论: lieSpan R L (⋃ i, s i) = ⨆ i, lieSpan R L (s i)
  证明: (LieSubmodule.gi R L M).gc.l_iSup

Depends on / 依赖: Algebra, LieSubmodule, LieSubmodule.gi, Semiring, algebra, gc.l_iSup, l_iSup
-/
theorem span_iUnion {ι} (s : ι -> Set M) : lieSpan R L (⋃ i, s i) = ⨆ i, lieSpan R L (s i) :=
  (LieSubmodule.gi R L M).gc.l_iSup

/-- An induction principle for span membership. If `p` holds for 0 and all elements of `s`, and is
preserved under addition, scalar multiplication and the Lie bracket, then `p` holds for all
elements of the Lie submodule spanned by `s`. -/
@[elab_as_elim]
/--
theorem `lieSpan_induction` / 定理 `lieSpan_induction`

English:
theorem lieSpan_induction
  statement: {p : (x : M) -> x in lieSpan R L s -> Prop}
  proof: by
  let p : LieSubmodule R L M :=
    { carrier := { x | exists hx, p x hx }
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, add _ _ _ _ hpx hpy⟩
      zero_mem' := ⟨_, zero⟩
      smul_mem' := fun r => fun ⟨_, hpx⟩ => ⟨_, smul r _ _ hpx⟩
      lie_mem := fun ⟨_, hpy⟩ => ⟨_, lie _ _ _ hpy⟩ }
.elim f

中文:
定理 lieSpan_induction
  结论: {p : (x : M) -> x in lieSpan R L s -> 命题}
  证明: by
  let p : LieSubmodule R L M :=
    { carrier := { x | exists hx, p x hx }
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, add _ _ _ _ hpx hpy⟩
      zero_mem' := ⟨_, zero⟩
      smul_mem' := fun r => fun ⟨_, hpx⟩ => ⟨_, smul r _ _ hpx⟩
      lie_mem := fun ⟨_, hpy⟩ => ⟨_, lie _ _ _ hpy⟩ }
.elim f

Depends on / 依赖: LieSubmodule, add_mem, carrier, lieSpan_le, lie_mem, smul_mem, subset_lieSpan, zero_mem
-/
theorem lieSpan_induction {p : (x : M) -> x in lieSpan R L s -> Prop}
    (mem : forall (x) (h : x in s), p x (subset_lieSpan h))
    (zero : p 0 (LieSubmodule.zero_mem _))
    (add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem ‹_› ‹_›))
    (smul : forall (a : R) (x hx), p x hx -> p (a • x) (SMulMemClass.smul_mem _ hx)) {x}
    (lie : forall (x : L) (y hy), p y hy -> p (⁅x, y⁆) (LieSubmodule.lie_mem _ ‹_›))
    (hx : x in lieSpan R L s) : p x hx := by
  let p : LieSubmodule R L M :=
    { carrier := { x | exists hx, p x hx }
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ => ⟨_, add _ _ _ _ hpx hpy⟩
      zero_mem' := ⟨_, zero⟩
      smul_mem' := fun r => fun ⟨_, hpx⟩ => ⟨_, smul r _ _ hpx⟩
      lie_mem := fun ⟨_, hpy⟩ => ⟨_, lie _ _ _ hpy⟩ }
.elim fun _ => id .mpr (fun y hy => ⟨subset_lieSpan hy, mem y hy⟩) hx exact lieSpan_le (N := p)

/--
lemma `isCompactElement_lieSpan_singleton` / 引理 `isCompactElement_lieSpan_singleton`

English:
lemma isCompactElement_lieSpan_singleton
  given: (m : M)
  proof: by
  rw [CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le]
  intro s hne hdir hsup
  replace hsup : m in (↑(sSup s) : Set M) := (SetLike.le_def.mp hsup) (subset_lieSpan rfl)
  suffices (↑(sSup s) : Set M) = ⋃ N in s, ↑N by simp_all
  replace hne : Nonempty s := Set.nonempty_coe_sort.mpr h

中文:
引理 isCompactElement_lieSpan_singleton
  条件: (m : M)
  证明: by
  rw [CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le]
  intro s hne hdir hsup
  replace hsup : m in (↑(sSup s) : Set M) := (SetLike.le_def.mp hsup) (subset_lieSpan rfl)
  suffices (↑(sSup s) : Set M) = ⋃ N in s, ↑N by simp_all
  replace hne : Nonempty s := Set.nonempty_coe_sort.mpr h

Depends on / 依赖: CompleteLattice, CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le, Nonempty, Set.iUnion_coe_set, Set.nonempty_coe_sort.mpr, SetLike, SetLike.coe_set_eq, SetLike.le_def.mp, Submodule, Submodule.coe_iSup_of_directed, coe_iSup_of_directed, coe_set_eq, coe_toSubmodule, directed_val, hdir.directed_val, iSup_subtype, iSup_toSubmodule, iUnion_coe_set, isCompactElement_iff_le_of_directed_sSup_le, le_def
-/
lemma isCompactElement_lieSpan_singleton (m : M) :
    IsCompactElement (lieSpan R L {m}) := by
  rw [CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le]
  intro s hne hdir hsup
  replace hsup : m in (↑(sSup s) : Set M) := (SetLike.le_def.mp hsup) (subset_lieSpan rfl)
  suffices (↑(sSup s) : Set M) = ⋃ N in s, ↑N by simp_all
  replace hne : Nonempty s := Set.nonempty_coe_sort.mpr hne
  have := Submodule.coe_iSup_of_directed _ hdir.directed_val
  simp_rw [← iSup_toSubmodule, Set.iUnion_coe_set, coe_toSubmodule] at this
  rw [← this]; rw [SetLike.coe_set_eq]; rw [sSup_eq_iSup]; rw [iSup_subtype]

@[simp]
/--
lemma `sSup_image_lieSpan_singleton` / 引理 `sSup_image_lieSpan_singleton`

English:
lemma sSup_image_lieSpan_singleton
  statement: sSup ((fun x => lieSpan R L {x}) '' N) = N
  proof: by
  refine le_antisymm (sSup_le <| by simp) ?_
  simp_rw [← toSubmodule_le_toSubmodule, sSup_toSubmodule, Set.mem_image, SetLike.mem_coe]
  refine fun m hm => Submodule.mem_sSup.mpr fun N' hN' => ?_
  replace hN' : forall m in N, lieSpan R L {m} <= N' := by simpa using hN'
  exact hN' _ hm (subset_

中文:
引理 sSup_image_lieSpan_singleton
  结论: sSup ((fun x => lieSpan R L {x}) '' N) = N
  证明: by
  refine le_antisymm (sSup_le <| by simp) ?_
  simp_rw [← toSubmodule_le_toSubmodule, sSup_toSubmodule, Set.mem_image, SetLike.mem_coe]
  refine fun m hm => Submodule.mem_sSup.mpr fun N' hN' => ?_
  replace hN' : forall m in N, lieSpan R L {m} <= N' := by simpa using hN'
  exact hN' _ hm (subset_

Depends on / 依赖: Set.mem_image, SetLike, SetLike.mem_coe, Submodule, Submodule.mem_sSup.mpr, le_antisymm, lieSpan, mem_coe, mem_image, mem_sSup, replace, sSup_le, sSup_toSubmodule, simp_rw, subset_lieSpan, toSubmodule_le_toSubmodule
-/
lemma sSup_image_lieSpan_singleton : sSup ((fun x => lieSpan R L {x}) '' N) = N := by
  refine le_antisymm (sSup_le <| by simp) ?_
  simp_rw [← toSubmodule_le_toSubmodule, sSup_toSubmodule, Set.mem_image, SetLike.mem_coe]
  refine fun m hm => Submodule.mem_sSup.mpr fun N' hN' => ?_
  replace hN' : forall m in N, lieSpan R L {m} <= N' := by simpa using hN'
  exact hN' _ hm (subset_lieSpan rfl)

/--
Instance `instIsCompactlyGenerated` / 实例 `instIsCompactlyGenerated`

English:
instance instIsCompactlyGenerated
  signature: : IsCompactlyGenerated (LieSubmodule R L M)
  body: ⟨fun N => ⟨(fun x => lieSpan R L {x}) '' N, fun _ ⟨m, _, hm⟩ =>
    hm ▸ isCompactElement_lieSpan_singleton R L m, N.sSup_image_lieSpan_singleton⟩⟩

中文:
实例 instIsCompactlyGenerated
  签名: : IsCompactlyGenerated (LieSubmodule R L M)
  定义体: ⟨fun N => ⟨(fun x => lieSpan R L {x}) '' N, fun _ ⟨m, _, hm⟩ =>
    hm ▸ isCompactElement_lieSpan_singleton R L m, N.sSup_image_lieSpan_singleton⟩⟩

Depends on / 依赖: N.sSup_image_lieSpan_singleton, isCompactElement_lieSpan_singleton, lieSpan, sSup_image_lieSpan_singleton
-/
instance instIsCompactlyGenerated : IsCompactlyGenerated (LieSubmodule R L M) :=
  ⟨fun N => ⟨(fun x => lieSpan R L {x}) '' N, fun _ ⟨m, _, hm⟩ =>
    hm ▸ isCompactElement_lieSpan_singleton R L m, N.sSup_image_lieSpan_singleton⟩⟩

end LieSpan

end LatticeStructure

end LieSubmodule

section LieSubmoduleMapAndComap

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}
variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']
variable [AddCommGroup M] [Module R M] [LieRingModule L M]
variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

namespace LieSubmodule

variable (f : M ->ₗ⁅R,L⁆ M') (N N₂ : LieSubmodule R L M) (N' : LieSubmodule R L M')

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : LieSubmodule R L M'
  body: { (N : Submodule R M).map (f : M ->ₗ[R] M') with
    lie_mem := fun {x m'} h => by
      rcases h with ⟨m, hm, hfm⟩; use ⁅x, m⁆; constructor
      · apply N.lie_mem hm
      · norm_cast at hfm; simp [hfm] }

中文:
定义 map
  签名: : LieSubmodule R L M'
  定义体: { (N : Submodule R M).map (f : M ->ₗ[R] M') with
    lie_mem := fun {x m'} h => by
      rcases h with ⟨m, hm, hfm⟩; use ⁅x, m⁆; constructor
      · apply N.lie_mem hm
      · norm_cast at hfm; simp [hfm] }

Depends on / 依赖: N.lie_mem, Submodule, lie_mem
-/
def map : LieSubmodule R L M' :=
  { (N : Submodule R M).map (f : M ->ₗ[R] M') with
    lie_mem := fun {x m'} h => by
      rcases h with ⟨m, hm, hfm⟩; use ⁅x, m⁆; constructor
      · apply N.lie_mem hm
      · norm_cast at hfm; simp [hfm] }

/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  statement: (N.map f : Set M') = f '' N
  proof: rfl

@[simp]

中文:
定理 coe_map
  结论: (N.map f : Set M') = f '' N
  证明: rfl

@[simp]
-/
@[simp] theorem coe_map : (N.map f : Set M') = f '' N := rfl

@[simp]
/--
theorem `toSubmodule_map` / 定理 `toSubmodule_map`

English:
theorem toSubmodule_map
  statement: (N.map f : Submodule R M') = (N : Submodule R M).map (f : M ->ₗ[R] M')
  proof: rfl

中文:
定理 toSubmodule_map
  结论: (N.map f : Submodule R M') = (N : Submodule R M).map (f : M ->ₗ[R] M')
  证明: rfl
-/
theorem toSubmodule_map : (N.map f : Submodule R M') = (N : Submodule R M).map (f : M ->ₗ[R] M') :=
  rfl

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: : LieSubmodule R L M
  body: { (N' : Submodule R M').comap (f : M ->ₗ[R] M') with
    lie_mem := fun {x m} h => by
      suffices ⁅x, f m⁆ in N' by simp [this]
      apply N'.lie_mem h }

@[simp]

中文:
定义 comap
  签名: : LieSubmodule R L M
  定义体: { (N' : Submodule R M').comap (f : M ->ₗ[R] M') with
    lie_mem := fun {x m} h => by
      suffices ⁅x, f m⁆ in N' by simp [this]
      apply N'.lie_mem h }

@[simp]

Depends on / 依赖: Submodule, lie_mem
-/
def comap : LieSubmodule R L M :=
  { (N' : Submodule R M').comap (f : M ->ₗ[R] M') with
    lie_mem := fun {x m} h => by
      suffices ⁅x, f m⁆ in N' by simp [this]
      apply N'.lie_mem h }

@[simp]
/--
theorem `toSubmodule_comap` / 定理 `toSubmodule_comap`

English:
theorem toSubmodule_comap
  proof: rfl

中文:
定理 toSubmodule_comap
  证明: rfl
-/
theorem toSubmodule_comap :
    (N'.comap f : Submodule R M) = (N' : Submodule R M').comap (f : M ->ₗ[R] M') :=
  rfl

variable {f N N₂ N'}

/--
theorem `map_le_iff_le_comap` / 定理 `map_le_iff_le_comap`

English:
theorem map_le_iff_le_comap
  statement: map f N <= N' ↔ N <= comap f N'
  proof: Set.image_subset_iff

中文:
定理 map_le_iff_le_comap
  结论: map f N <= N' ↔ N <= comap f N'
  证明: Set.image_subset_iff

Depends on / 依赖: Set.image_subset_iff, image_subset_iff
-/
theorem map_le_iff_le_comap : map f N <= N' ↔ N <= comap f N' :=
  Set.image_subset_iff

variable (f) in
/--
theorem `gc_map_comap` / 定理 `gc_map_comap`

English:
theorem gc_map_comap
  statement: GaloisConnection (map f) (comap f)
  proof: fun _ _ => map_le_iff_le_comap

中文:
定理 gc_map_comap
  结论: GaloisConnection (map f) (comap f)
  证明: fun _ _ => map_le_iff_le_comap

Depends on / 依赖: map_le_iff_le_comap
-/
theorem gc_map_comap : GaloisConnection (map f) (comap f) := fun _ _ => map_le_iff_le_comap

/--
theorem `map_inf_le` / 定理 `map_inf_le`

English:
theorem map_inf_le
  statement: (N ⊓ N₂).map f <= N.map f ⊓ N₂.map f
  proof: Set.image_inter_subset f N N₂

中文:
定理 map_inf_le
  结论: (N ⊓ N₂).map f <= N.map f ⊓ N₂.map f
  证明: Set.image_inter_subset f N N₂

Depends on / 依赖: Set.image_inter_subset, image_inter_subset
-/
theorem map_inf_le : (N ⊓ N₂).map f <= N.map f ⊓ N₂.map f :=
  Set.image_inter_subset f N N₂

/--
theorem `map_inf` / 定理 `map_inf`

English:
theorem map_inf
  given: (hf : Function.Injective f)
  proof: SetLike.coe_injective Set.image_inter hf

@[simp]

中文:
定理 map_inf
  条件: (hf : Function.Injective f)
  证明: SetLike.coe_injective Set.image_inter hf

@[simp]

Depends on / 依赖: Set.image_inter, SetLike, SetLike.coe_injective, coe_injective, image_inter
-/
theorem map_inf (hf : Function.Injective f) :
    (N ⊓ N₂).map f = N.map f ⊓ N₂.map f :=
SetLike.coe_injective Set.image_inter hf

@[simp]
/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  statement: (N ⊔ N₂).map f = N.map f ⊔ N₂.map f
  proof: (gc_map_comap f).l_sup

@[simp]

中文:
定理 map_sup
  结论: (N ⊔ N₂).map f = N.map f ⊔ N₂.map f
  证明: (gc_map_comap f).l_sup

@[simp]

Depends on / 依赖: LinearMap, LinearMap.map_smul_of_tower, LocalizedModule, LocalizedModule.induction_on, LocalizedModule.lift, Module, Module.End.algebraMap_isUnit_in, Module.End.algebraMap_isUnit_inv_apply_eq_iff, Submonoid, Submonoid.coe_mul, Submonoid.smul_def, algebraMap_isUnit_in, algebraMap_isUnit_inv_apply_eq_iff, coe_mul, gc_map_comap, l_sup, map_add, map_smul, map_smul_of_tower, mk_add_mk
-/
theorem map_sup : (N ⊔ N₂).map f = N.map f ⊔ N₂.map f :=
  (gc_map_comap f).l_sup

@[simp]
/--
theorem `comap_inf` / 定理 `comap_inf`

English:
theorem comap_inf
  given: {N₂' : LieSubmodule R L M'}
  proof: rfl

@[simp]

中文:
定理 comap_inf
  条件: {N₂' : LieSubmodule R L M'}
  证明: rfl

@[simp]

Depends on / 依赖: LocalizedModule, LocalizedModule.lift, LocalizedModule.smul, g.map_smul, induction_on, m.induction_on, map_smul
-/
theorem comap_inf {N₂' : LieSubmodule R L M'} :
    (N' ⊓ N₂').comap f = N'.comap f ⊓ N₂'.comap f :=
  rfl

@[simp]
/--
theorem `map_iSup` / 定理 `map_iSup`

English:
theorem map_iSup
  given: {ι : Sort*} (N : ι -> LieSubmodule R L M)
  proof: (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup

@[simp]

中文:
定理 map_iSup
  条件: {ι : Sort*} (N : ι -> LieSubmodule R L M)
  证明: (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup

@[simp]

Depends on / 依赖: GaloisConnection, gc_map_comap, l_iSup
-/
theorem map_iSup {ι : Sort*} (N : ι -> LieSubmodule R L M) :
    (⨆ i, N i).map f = ⨆ i, (N i).map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: (m' : M')
  statement: m' in N.map f ↔ exists m, m in N ∧ f m = m'
  proof: Submodule.mem_map

中文:
定理 mem_map
  条件: (m' : M')
  结论: m' in N.map f ↔ 存在 m, m in N ∧ f m = m'
  证明: Submodule.mem_map

Depends on / 依赖: Submodule, Submodule.mem_map, mem_map
-/
theorem mem_map (m' : M') : m' in N.map f ↔ exists m, m in N ∧ f m = m' :=
  Submodule.mem_map

/--
theorem `mem_map_of_mem` / 定理 `mem_map_of_mem`

English:
theorem mem_map_of_mem
  given: {m : M} (h : m in N)
  statement: f m in N.map f
  proof: Set.mem_image_of_mem _ h

@[simp]

中文:
定理 mem_map_of_mem
  条件: {m : M} (h : m in N)
  结论: f m in N.map f
  证明: Set.mem_image_of_mem _ h

@[simp]

Depends on / 依赖: Set.mem_image_of_mem, mem_image_of_mem
-/
theorem mem_map_of_mem {m : M} (h : m in N) : f m in N.map f :=
  Set.mem_image_of_mem _ h

@[simp]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: {m : M}
  statement: m in comap f N' ↔ f m in N'
  proof: Iff.rfl

中文:
定理 mem_comap
  条件: {m : M}
  结论: m in comap f N' ↔ f m in N'
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_comap {m : M} : m in comap f N' ↔ f m in N' :=
  Iff.rfl

/--
theorem `comap_incl_eq_top` / 定理 `comap_incl_eq_top`

English:
theorem comap_incl_eq_top
  statement: N₂.comap N.incl = ⊤ ↔ N <= N₂
  proof: by
  rw [← LieSubmodule.toSubmodule_inj]; rw [LieSubmodule.toSubmodule_comap]; rw [LieSubmodule.incl_coe]; rw [LieSubmodule.top_toSubmodule]; rw [Submodule.comap_subtype_eq_top]; rw [toSubmodule_le_toSubmodule]

中文:
定理 comap_incl_eq_top
  结论: N₂.comap N.incl = ⊤ ↔ N <= N₂
  证明: by
  rw [← LieSubmodule.toSubmodule_inj]; rw [LieSubmodule.toSubmodule_comap]; rw [LieSubmodule.incl_coe]; rw [LieSubmodule.top_toSubmodule]; rw [Submodule.comap_subtype_eq_top]; rw [toSubmodule_le_toSubmodule]

Depends on / 依赖: LieSubmodule, LieSubmodule.incl_coe, LieSubmodule.toSubmodule_comap, LieSubmodule.toSubmodule_inj, LieSubmodule.top_toSubmodule, Submodule, Submodule.comap_subtype_eq_top, comap_subtype_eq_top, incl_coe, toSubmodule_comap, toSubmodule_inj, toSubmodule_le_toSubmodule, top_toSubmodule
-/
theorem comap_incl_eq_top : N₂.comap N.incl = ⊤ ↔ N <= N₂ := by
  rw [← LieSubmodule.toSubmodule_inj]; rw [LieSubmodule.toSubmodule_comap]; rw [LieSubmodule.incl_coe]; rw [LieSubmodule.top_toSubmodule]; rw [Submodule.comap_subtype_eq_top]; rw [toSubmodule_le_toSubmodule]

/--
theorem `comap_incl_eq_bot` / 定理 `comap_incl_eq_bot`

English:
theorem comap_incl_eq_bot
  statement: N₂.comap N.incl = ⊥ ↔ N ⊓ N₂ = ⊥
  proof: by
  simp only [← toSubmodule_inj, toSubmodule_comap, incl_coe, bot_toSubmodule,
    inf_toSubmodule]
  rw [← Submodule.disjoint_iff_comap_eq_bot]; rw [disjoint_iff]

@[gcongr, mono]

中文:
定理 comap_incl_eq_bot
  结论: N₂.comap N.incl = ⊥ ↔ N ⊓ N₂ = ⊥
  证明: by
  simp only [← toSubmodule_inj, toSubmodule_comap, incl_coe, bot_toSubmodule,
    inf_toSubmodule]
  rw [← Submodule.disjoint_iff_comap_eq_bot]; rw [disjoint_iff]

@[gcongr, mono]

Depends on / 依赖: Submodule, Submodule.disjoint_iff_comap_eq_bot, bot_toSubmodule, disjoint_iff, disjoint_iff_comap_eq_bot, incl_coe, inf_toSubmodule, toSubmodule_comap, toSubmodule_inj
-/
theorem comap_incl_eq_bot : N₂.comap N.incl = ⊥ ↔ N ⊓ N₂ = ⊥ := by
  simp only [← toSubmodule_inj, toSubmodule_comap, incl_coe, bot_toSubmodule,
    inf_toSubmodule]
  rw [← Submodule.disjoint_iff_comap_eq_bot]; rw [disjoint_iff]

@[gcongr, mono]
/--
theorem `map_mono` / 定理 `map_mono`

English:
theorem map_mono
  given: (h : N <= N₂)
  statement: N.map f <= N₂.map f
  proof: Set.image_mono h

中文:
定理 map_mono
  条件: (h : N <= N₂)
  结论: N.map f <= N₂.map f
  证明: Set.image_mono h

Depends on / 依赖: Set.image_mono, image_mono
-/
theorem map_mono (h : N <= N₂) : N.map f <= N₂.map f :=
  Set.image_mono h

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  proof: SetLike.coe_injective by
    simp only [← Set.image_comp, coe_map, LieModuleHom.coe_comp]

@[simp]

中文:
定理 map_comp
  证明: SetLike.coe_injective by
    simp only [← Set.image_comp, coe_map, LieModuleHom.coe_comp]

@[simp]

Depends on / 依赖: LieModuleHom, LieModuleHom.coe_comp, Set.image_comp, SetLike, SetLike.coe_injective, coe_comp, coe_injective, coe_map, image_comp
-/
theorem map_comp
    {M'' : Type*} [AddCommGroup M''] [Module R M''] [LieRingModule L M''] {g : M' ->ₗ⁅R,L⁆ M''} :
    N.map (g.comp f) = (N.map f).map g :=
SetLike.coe_injective by
    simp only [← Set.image_comp, coe_map, LieModuleHom.coe_comp]

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: N.map LieModuleHom.id = N
  proof: by ext; simp

中文:
定理 map_id
  结论: N.map LieModuleHom.id = N
  证明: by ext; simp
-/
theorem map_id : N.map LieModuleHom.id = N := by ext; simp

/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  proof: by
  ext m; simp [eq_comm]

中文:
定理 map_bot
  证明: by
  ext m; simp [eq_comm]
-/
@[simp] theorem map_bot :
    (⊥ : LieSubmodule R L M).map f = ⊥ := by
  ext m; simp [eq_comm]

/--
lemma `map_le_map_iff` / 引理 `map_le_map_iff`

English:
lemma map_le_map_iff
  given: (hf : Function.Injective f)
  proof: Set.image_subset_image_iff hf

中文:
引理 map_le_map_iff
  条件: (hf : Function.Injective f)
  证明: Set.image_subset_image_iff hf

Depends on / 依赖: Set.image_subset_image_iff, image_subset_image_iff
-/
lemma map_le_map_iff (hf : Function.Injective f) :
    N.map f <= N₂.map f ↔ N <= N₂ :=
  Set.image_subset_image_iff hf

/--
lemma `map_injective_of_injective` / 引理 `map_injective_of_injective`

English:
lemma map_injective_of_injective
  given: (hf : Function.Injective f)
  proof: fun {N N'} h =>
SetLike.coe_injective hf.image_injective by simp only [← coe_map, h]

中文:
引理 map_injective_of_injective
  条件: (hf : Function.Injective f)
  证明: fun {N N'} h =>
SetLike.coe_injective hf.image_injective by simp only [← coe_map, h]
-/
lemma map_injective_of_injective (hf : Function.Injective f) :
    Function.Injective (map f) := fun {N N'} h =>
SetLike.coe_injective hf.image_injective by simp only [← coe_map, h]

/--
Definition of `mapOrderEmbedding` / `mapOrderEmbedding` 的定义

English:
definition mapOrderEmbedding
  signature: {f : M ->ₗ⁅R,L⁆ M'} (hf : Function.Injective f)
  body: LieSubmodule.map f
  inj' := map_injective_of_injective hf
  map_rel_iff' := Set.image_subset_image_iff hf

中文:
定义 mapOrderEmbedding
  签名: {f : M ->ₗ⁅R,L⁆ M'} (hf : Function.Injective f)
  定义体: LieSubmodule.map f
  inj' := map_injective_of_injective hf
  map_rel_iff' := Set.image_subset_image_iff hf
-/
@[simps] def mapOrderEmbedding {f : M ->ₗ⁅R,L⁆ M'} (hf : Function.Injective f) :
    LieSubmodule R L M ↪o LieSubmodule R L M' where
  toFun := LieSubmodule.map f
  inj' := map_injective_of_injective hf
  map_rel_iff' := Set.image_subset_image_iff hf

variable (N) in
/--
Definition of `equivMapOfInjective` / `equivMapOfInjective` 的定义

English:
definition equivMapOfInjective
  signature: (hf : Function.Injective f)
  body: { Submodule.equivMapOfInjective (f : M ->ₗ[R] M') hf N with
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify `invFun` explicitly this way, otherwise we'd get a type mismatch
    invFun := by exact DFunLike.coe (Submodule.equivMapOfInjective (f : M ->ₗ[R] M') hf 

中文:
定义 equivMapOfInjective
  签名: (hf : Function.Injective f)
  定义体: { Submodule.equivMapOfInjective (f : M ->ₗ[R] M') hf N with
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify `invFun` explicitly this way, otherwise we'd get a type mismatch
    invFun := by exact DFunLike.coe (Submodule.equivMapOfInjective (f : M ->ₗ[R] M') hf 

Depends on / 依赖: LinearMap, LinearMap.map_smul_of_tower, LocalizedModule, LocalizedModule.induction_on, LocalizedModule.mk_add_mk, Module, Module.End.algebraMap_isUnit_inv_apply_eq_iff, Submodule, Submodule.equivMapOfInjective, Submonoid, Submonoid.coe_mul, Submonoid.smul_def, algebraMap_isUnit_inv_apply_eq_iff, all_goals, coe_mul, equivMapOfInjective, fromLocalizedModule, map_add, map_smul, map_smul_of_tower
-/
noncomputable def equivMapOfInjective (hf : Function.Injective f) :
    N ≃ₗ⁅R,L⁆ N.map f :=
  { Submodule.equivMapOfInjective (f : M ->ₗ[R] M') hf N with
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify `invFun` explicitly this way, otherwise we'd get a type mismatch
    invFun := by exact DFunLike.coe (Submodule.equivMapOfInjective (f : M ->ₗ[R] M') hf N).symm
    map_lie' := by rintro x ⟨m, hm : m in N⟩; ext; exact f.map_lie x m }

/--
Definition of `orderIsoMapComap` / `orderIsoMapComap` 的定义

English:
definition orderIsoMapComap
  signature: (e : M ≃ₗ⁅R,L⁆ M')
  body: map e
  invFun := comap e
  left_inv := fun N => by ext; simp
  right_inv := fun N => by ext; simp [← e.eq_symm_apply]
  map_rel_iff' := fun {_ _} => Set.image_subset_image_iff e.injective

中文:
定义 orderIsoMapComap
  签名: (e : M ≃ₗ⁅R,L⁆ M')
  定义体: map e
  invFun := comap e
  left_inv := fun N => by ext; simp
  right_inv := fun N => by ext; simp [← e.eq_symm_apply]
  map_rel_iff' := fun {_ _} => Set.image_subset_image_iff e.injective

Depends on / 依赖: LocalizedModule, LocalizedModule.induction_on, LocalizedModule.smul, f.map_smul, fromLocalizedModule, induction_on, map_smul
-/
@[simps] def orderIsoMapComap (e : M ≃ₗ⁅R,L⁆ M') :
    LieSubmodule R L M ≃o LieSubmodule R L M' where
  toFun := map e
  invFun := comap e
  left_inv := fun N => by ext; simp
  right_inv := fun N => by ext; simp [← e.eq_symm_apply]
  map_rel_iff' := fun {_ _} => Set.image_subset_image_iff e.injective

end LieSubmodule


end LieSubmoduleMapAndComap

namespace LieModuleHom

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}
variable [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N]
variable (f : M ->ₗ⁅R,L⁆ N)

/--
Definition of `ker` / `ker` 的定义

English:
definition ker
  signature: : LieSubmodule R L M
  body: LieSubmodule.comap f ⊥

@[simp]

中文:
定义 ker
  签名: : LieSubmodule R L M
  定义体: LieSubmodule.comap f ⊥

@[simp]

Depends on / 依赖: LieSubmodule, LieSubmodule.comap
-/
def ker : LieSubmodule R L M :=
  LieSubmodule.comap f ⊥

@[simp]
/--
theorem `ker_toSubmodule` / 定理 `ker_toSubmodule`

English:
theorem ker_toSubmodule
  statement: (f.ker : Submodule R M) = LinearMap.ker (f : M ->ₗ[R] N)
  proof: rfl

中文:
定理 ker_toSubmodule
  结论: (f.ker : Submodule R M) = LinearMap.ker (f : M ->ₗ[R] N)
  证明: rfl
-/
theorem ker_toSubmodule : (f.ker : Submodule R M) = LinearMap.ker (f : M ->ₗ[R] N) :=
  rfl

/--
theorem `ker_eq_bot` / 定理 `ker_eq_bot`

English:
theorem ker_eq_bot
  statement: f.ker = ⊥ ↔ Function.Injective f
  proof: by
  rw [← LieSubmodule.toSubmodule_inj]; rw [ker_toSubmodule]; rw [LieSubmodule.bot_toSubmodule]; rw [LinearMap.ker_eq_bot]; rw [coe_toLinearMap]

中文:
定理 ker_eq_bot
  结论: f.ker = ⊥ ↔ Function.Injective f
  证明: by
  rw [← LieSubmodule.toSubmodule_inj]; rw [ker_toSubmodule]; rw [LieSubmodule.bot_toSubmodule]; rw [LinearMap.ker_eq_bot]; rw [coe_toLinearMap]

Depends on / 依赖: LieSubmodule, LieSubmodule.bot_toSubmodule, LieSubmodule.toSubmodule_inj, LinearMap, LinearMap.ker_eq_bot, bot_toSubmodule, coe_toLinearMap, ker_eq_bot, ker_toSubmodule, toSubmodule_inj
-/
theorem ker_eq_bot : f.ker = ⊥ ↔ Function.Injective f := by
  rw [← LieSubmodule.toSubmodule_inj]; rw [ker_toSubmodule]; rw [LieSubmodule.bot_toSubmodule]; rw [LinearMap.ker_eq_bot]; rw [coe_toLinearMap]

variable {f}

@[simp]
/--
theorem `mem_ker` / 定理 `mem_ker`

English:
theorem mem_ker
  given: {m : M}
  statement: m in f.ker ↔ f m = 0
  proof: Iff.rfl

@[simp]

中文:
定理 mem_ker
  条件: {m : M}
  结论: m in f.ker ↔ f m = 0
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_ker {m : M} : m in f.ker ↔ f m = 0 :=
  Iff.rfl

@[simp]
/--
theorem `ker_id` / 定理 `ker_id`

English:
theorem ker_id
  statement: (LieModuleHom.id : M ->ₗ⁅R,L⁆ M).ker = ⊥
  proof: rfl

@[simp]

中文:
定理 ker_id
  结论: (LieModuleHom.id : M ->ₗ⁅R,L⁆ M).ker = ⊥
  证明: rfl

@[simp]
-/
theorem ker_id : (LieModuleHom.id : M ->ₗ⁅R,L⁆ M).ker = ⊥ :=
  rfl

@[simp]
/--
theorem `comp_ker_incl` / 定理 `comp_ker_incl`

English:
theorem comp_ker_incl
  statement: f.comp f.ker.incl = 0
  proof: by ext ⟨m, hm⟩; exact mem_ker.mp hm

中文:
定理 comp_ker_incl
  结论: f.comp f.ker.incl = 0
  证明: by ext ⟨m, hm⟩; exact mem_ker.mp hm

Depends on / 依赖: mem_ker, mem_ker.mp
-/
theorem comp_ker_incl : f.comp f.ker.incl = 0 := by ext ⟨m, hm⟩; exact mem_ker.mp hm

/--
theorem `le_ker_iff_map` / 定理 `le_ker_iff_map`

English:
theorem le_ker_iff_map
  given: (M' : LieSubmodule R L M)
  statement: M' <= f.ker ↔ LieSubmodule.map f M' = ⊥
  proof: by
  rw [ker]; rw [eq_bot_iff]; rw [LieSubmodule.map_le_iff_le_comap]

中文:
定理 le_ker_iff_map
  条件: (M' : LieSubmodule R L M)
  结论: M' <= f.ker ↔ LieSubmodule.map f M' = ⊥
  证明: by
  rw [ker]; rw [eq_bot_iff]; rw [LieSubmodule.map_le_iff_le_comap]

Depends on / 依赖: LieSubmodule, LieSubmodule.map_le_iff_le_comap, eq_bot_iff, map_le_iff_le_comap
-/
theorem le_ker_iff_map (M' : LieSubmodule R L M) : M' <= f.ker ↔ LieSubmodule.map f M' = ⊥ := by
  rw [ker]; rw [eq_bot_iff]; rw [LieSubmodule.map_le_iff_le_comap]

variable (f)

/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: : LieSubmodule R L N
  body: (LieSubmodule.map f ⊤).copy (Set.range f) Set.image_univ.symm

@[simp]

中文:
定义 range
  签名: : LieSubmodule R L N
  定义体: (LieSubmodule.map f ⊤).copy (Set.range f) Set.image_univ.symm

@[simp]

Depends on / 依赖: LieSubmodule, LieSubmodule.map, Set.image_univ.symm, Set.range, image_univ
-/
def range : LieSubmodule R L N :=
  (LieSubmodule.map f ⊤).copy (Set.range f) Set.image_univ.symm

@[simp]
/--
theorem `coe_range` / 定理 `coe_range`

English:
theorem coe_range
  statement: f.range = Set.range f
  proof: rfl

@[simp]

中文:
定理 coe_range
  结论: f.range = Set.range f
  证明: rfl

@[simp]
-/
theorem coe_range : f.range = Set.range f :=
  rfl

@[simp]
/--
theorem `toSubmodule_range` / 定理 `toSubmodule_range`

English:
theorem toSubmodule_range
  statement: f.range = LinearMap.range (f : M ->ₗ[R] N)
  proof: rfl

@[simp]

中文:
定理 toSubmodule_range
  结论: f.range = LinearMap.range (f : M ->ₗ[R] N)
  证明: rfl

@[simp]
-/
theorem toSubmodule_range : f.range = LinearMap.range (f : M ->ₗ[R] N) :=
  rfl

@[simp]
/--
theorem `mem_range` / 定理 `mem_range`

English:
theorem mem_range
  given: (n : N)
  statement: n in f.range ↔ exists m, f m = n
  proof: Iff.rfl

@[simp]

中文:
定理 mem_range
  条件: (n : N)
  结论: n in f.range ↔ 存在 m, f m = n
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_range (n : N) : n in f.range ↔ exists m, f m = n :=
  Iff.rfl

@[simp]
/--
theorem `map_top` / 定理 `map_top`

English:
theorem map_top
  statement: LieSubmodule.map f ⊤ = f.range
  proof: by ext; simp [LieSubmodule.mem_map]

中文:
定理 map_top
  结论: LieSubmodule.map f ⊤ = f.range
  证明: by ext; simp [LieSubmodule.mem_map]

Depends on / 依赖: LieSubmodule, LieSubmodule.mem_map, mem_map
-/
theorem map_top : LieSubmodule.map f ⊤ = f.range := by ext; simp [LieSubmodule.mem_map]

/--
theorem `range_eq_top` / 定理 `range_eq_top`

English:
theorem range_eq_top
  statement: f.range = ⊤ ↔ Function.Surjective f
  proof: by
  rw [SetLike.ext'_iff]; rw [coe_range]; rw [LieSubmodule.top_coe]; rw [Set.range_eq_univ]

中文:
定理 range_eq_top
  结论: f.range = ⊤ ↔ Function.Surjective f
  证明: by
  rw [SetLike.ext'_iff]; rw [coe_range]; rw [LieSubmodule.top_coe]; rw [Set.range_eq_univ]

Depends on / 依赖: LieSubmodule, LieSubmodule.top_coe, Set.range_eq_univ, SetLike, SetLike.ext, _iff, coe_range, range_eq_univ, top_coe
-/
theorem range_eq_top : f.range = ⊤ ↔ Function.Surjective f := by
  rw [SetLike.ext'_iff]; rw [coe_range]; rw [LieSubmodule.top_coe]; rw [Set.range_eq_univ]

/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (P : LieSubmodule R L N) (f : M ->ₗ⁅R,L⁆ N) (h : forall m, f m in P)
  body: f.toLinearMap.codRestrict P h
  __ := f.toLinearMap.codRestrict P h
  map_lie' {x m} := by ext; simp

@[simp]

中文:
定义 codRestrict
  签名: (P : LieSubmodule R L N) (f : M ->ₗ⁅R,L⁆ N) (h : 对任意 m, f m in P)
  定义体: f.toLinearMap.codRestrict P h
  __ := f.toLinearMap.codRestrict P h
  map_lie' {x m} := by ext; simp

@[simp]

Depends on / 依赖: codRestrict, f.toLinearMap.codRestrict, toLinearMap
-/
def codRestrict (P : LieSubmodule R L N) (f : M ->ₗ⁅R,L⁆ N) (h : forall m, f m in P) :
    M ->ₗ⁅R,L⁆ P where
  toFun := f.toLinearMap.codRestrict P h
  __ := f.toLinearMap.codRestrict P h
  map_lie' {x m} := by ext; simp

@[simp]
/--
lemma `codRestrict_apply` / 引理 `codRestrict_apply`

English:
lemma codRestrict_apply
  given: (P : LieSubmodule R L N) (f : M ->ₗ⁅R,L⁆ N) (h : forall m, f m in P) (m : M)
  proof: rfl

中文:
引理 codRestrict_apply
  条件: (P : LieSubmodule R L N) (f : M ->ₗ⁅R,L⁆ N) (h : 对任意 m, f m in P) (m : M)
  证明: rfl
-/
lemma codRestrict_apply (P : LieSubmodule R L N) (f : M ->ₗ⁅R,L⁆ N) (h : forall m, f m in P) (m : M) :
    (f.codRestrict P h m : N) = f m :=
  rfl

end LieModuleHom

namespace LieSubmodule

variable {R : Type u} {L : Type v} {M : Type w}
variable [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]
variable (N : LieSubmodule R L M)

@[simp]
/--
theorem `ker_incl` / 定理 `ker_incl`

English:
theorem ker_incl
  statement: N.incl.ker = ⊥
  proof: (LieModuleHom.ker_eq_bot N.incl).mpr injective_incl N

@[simp]

中文:
定理 ker_incl
  结论: N.incl.ker = ⊥
  证明: (LieModuleHom.ker_eq_bot N.incl).mpr injective_incl N

@[simp]

Depends on / 依赖: LieModuleHom, LieModuleHom.ker_eq_bot, N.incl, injective_incl, ker_eq_bot
-/
theorem ker_incl : N.incl.ker = ⊥ := (LieModuleHom.ker_eq_bot N.incl).mpr injective_incl N

@[simp]
/--
theorem `range_incl` / 定理 `range_incl`

English:
theorem range_incl
  statement: N.incl.range = N
  proof: by
  simp only [← toSubmodule_inj, LieModuleHom.toSubmodule_range, incl_coe]
  rw [Submodule.range_subtype]

@[simp]

中文:
定理 range_incl
  结论: N.incl.range = N
  证明: by
  simp only [← toSubmodule_inj, LieModuleHom.toSubmodule_range, incl_coe]
  rw [Submodule.range_subtype]

@[simp]

Depends on / 依赖: LieModuleHom, LieModuleHom.toSubmodule_range, Submodule, Submodule.range_subtype, incl_coe, range_subtype, toSubmodule_inj, toSubmodule_range
-/
theorem range_incl : N.incl.range = N := by
  simp only [← toSubmodule_inj, LieModuleHom.toSubmodule_range, incl_coe]
  rw [Submodule.range_subtype]

@[simp]
/--
theorem `comap_incl_self` / 定理 `comap_incl_self`

English:
theorem comap_incl_self
  statement: comap N.incl N = ⊤
  proof: by
  simp only [← toSubmodule_inj, toSubmodule_comap, incl_coe, top_toSubmodule]
  rw [Submodule.comap_subtype_self]

中文:
定理 comap_incl_self
  结论: comap N.incl N = ⊤
  证明: by
  simp only [← toSubmodule_inj, toSubmodule_comap, incl_coe, top_toSubmodule]
  rw [Submodule.comap_subtype_self]

Depends on / 依赖: Submodule, Submodule.comap_subtype_self, comap_subtype_self, incl_coe, toSubmodule_comap, toSubmodule_inj, top_toSubmodule
-/
theorem comap_incl_self : comap N.incl N = ⊤ := by
  simp only [← toSubmodule_inj, toSubmodule_comap, incl_coe, top_toSubmodule]
  rw [Submodule.comap_subtype_self]

/--
theorem `map_incl_top` / 定理 `map_incl_top`

English:
theorem map_incl_top
  statement: (⊤ : LieSubmodule R L N).map N.incl = N
  proof: by simp

中文:
定理 map_incl_top
  结论: (⊤ : LieSubmodule R L N).map N.incl = N
  证明: by simp
-/
theorem map_incl_top : (⊤ : LieSubmodule R L N).map N.incl = N := by simp

/--
theorem `map_restrictLie_incl_top` / 定理 `map_restrictLie_incl_top`

English:
theorem map_restrictLie_incl_top
  given: [LieAlgebra R L] (H : LieSubalgebra R L)
  proof: by
  ext; simp

中文:
定理 map_restrictLie_incl_top
  条件: [LieAlgebra R L] (H : LieSubalgebra R L)
  证明: by
  ext; simp
-/
theorem map_restrictLie_incl_top [LieAlgebra R L] (H : LieSubalgebra R L) :
    (⊤ : LieSubmodule R H N).map (N.incl.restrictLie H) = N.restr H := by
  ext; simp

variable {N}

@[simp]
/--
lemma `map_le_range` / 引理 `map_le_range`

English:
lemma map_le_range
  statement: {M' : Type*}
  proof: by
  rw [← LieModuleHom.map_top]
  exact LieSubmodule.map_mono le_top

中文:
引理 map_le_range
  结论: {M' : 类型}
  证明: by
  rw [← LieModuleHom.map_top]
  exact LieSubmodule.map_mono le_top

Depends on / 依赖: LieModuleHom, LieModuleHom.map_top, LieSubmodule, LieSubmodule.map_mono, le_top, map_mono, map_top
-/
lemma map_le_range {M' : Type*}
    [AddCommGroup M'] [Module R M'] [LieRingModule L M'] (f : M ->ₗ⁅R,L⁆ M') :
    N.map f <= f.range := by
  rw [← LieModuleHom.map_top]
  exact LieSubmodule.map_mono le_top

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `map_incl_lt_iff_lt_top` / 引理 `map_incl_lt_iff_lt_top`

English:
lemma map_incl_lt_iff_lt_top
  given: {N' : LieSubmodule R L N}
  proof: by
  convert! (LieSubmodule.mapOrderEmbedding (f := N.incl) Subtype.coe_injective).lt_iff_lt
  simp

@[simp]

中文:
引理 map_incl_lt_iff_lt_top
  条件: {N' : LieSubmodule R L N}
  证明: by
  convert! (LieSubmodule.mapOrderEmbedding (f := N.incl) Subtype.coe_injective).lt_iff_lt
  simp

@[simp]

Depends on / 依赖: LieSubmodule, LieSubmodule.mapOrderEmbedding, N.incl, Subtype, Subtype.coe_injective, coe_injective, convert, lt_iff_lt, mapOrderEmbedding
-/
lemma map_incl_lt_iff_lt_top {N' : LieSubmodule R L N} :
    N'.map (LieSubmodule.incl N) < N ↔ N' < ⊤ := by
  convert! (LieSubmodule.mapOrderEmbedding (f := N.incl) Subtype.coe_injective).lt_iff_lt
  simp

@[simp]
/--
lemma `map_incl_le` / 引理 `map_incl_le`

English:
lemma map_incl_le
  given: {N' : LieSubmodule R L N}
  proof: by
  conv_rhs => rw [← N.map_incl_top]
  exact LieSubmodule.map_mono le_top

中文:
引理 map_incl_le
  条件: {N' : LieSubmodule R L N}
  证明: by
  conv_rhs => rw [← N.map_incl_top]
  exact LieSubmodule.map_mono le_top

Depends on / 依赖: LieSubmodule, LieSubmodule.map_mono, N.map_incl_top, conv_rhs, le_top, map_incl_top, map_mono
-/
lemma map_incl_le {N' : LieSubmodule R L N} :
    N'.map N.incl <= N := by
  conv_rhs => rw [← N.map_incl_top]
  exact LieSubmodule.map_mono le_top

end LieSubmodule

section TopEquiv

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L]

variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M]

/--
Definition of `LieModuleEquiv.ofTop` / `LieModuleEquiv.ofTop` 的定义

English:
definition LieModuleEquiv.ofTop
  signature: : (⊤ : LieSubmodule R L M) ≃ₗ⁅R,L⁆ M
  body: { LinearEquiv.ofTop ⊤ rfl with
    map_lie' := rfl }

中文:
定义 LieModuleEquiv.ofTop
  签名: : (⊤ : LieSubmodule R L M) ≃ₗ⁅R,L⁆ M
  定义体: { LinearEquiv.ofTop ⊤ rfl with
    map_lie' := rfl }

Depends on / 依赖: LinearEquiv, LinearEquiv.ofTop, map_lie
-/
def LieModuleEquiv.ofTop : (⊤ : LieSubmodule R L M) ≃ₗ⁅R,L⁆ M :=
  { LinearEquiv.ofTop ⊤ rfl with
    map_lie' := rfl }

variable {R L}

/--
lemma `LieModuleEquiv.ofTop_apply` / 引理 `LieModuleEquiv.ofTop_apply`

English:
lemma LieModuleEquiv.ofTop_apply
  given: (x : (⊤ : LieSubmodule R L M))
  proof: rfl

中文:
引理 LieModuleEquiv.ofTop_apply
  条件: (x : (⊤ : LieSubmodule R L M))
  证明: rfl
-/
lemma LieModuleEquiv.ofTop_apply (x : (⊤ : LieSubmodule R L M)) :
    LieModuleEquiv.ofTop R L M x = x :=
  rfl

/--
lemma `LieModuleEquiv.range_coe` / 引理 `LieModuleEquiv.range_coe`

English:
lemma LieModuleEquiv.range_coe
  statement: {M' : Type*}
  proof: by
  rw [LieModuleHom.range_eq_top]
  exact e.surjective

中文:
引理 LieModuleEquiv.range_coe
  结论: {M' : 类型}
  证明: by
  rw [LieModuleHom.range_eq_top]
  exact e.surjective
-/
@[simp] lemma LieModuleEquiv.range_coe {M' : Type*}
    [AddCommGroup M'] [Module R M'] [LieRingModule L M'] (e : M ≃ₗ⁅R,L⁆ M') :
    LieModuleHom.range (e : M ->ₗ⁅R,L⁆ M') = ⊤ := by
  rw [LieModuleHom.range_eq_top]
  exact e.surjective

variable [LieAlgebra R L] [LieModule R L M]

/--
Definition of `LieSubalgebra.topEquiv` / `LieSubalgebra.topEquiv` 的定义

English:
definition LieSubalgebra.topEquiv
  signature: : (⊤ : LieSubalgebra R L) ≃ₗ⁅R⁆ L
  body: { (⊤ : LieSubalgebra R L).incl with
    invFun := fun x => ⟨x, Set.mem_univ x⟩ }

@[simp]

中文:
定义 LieSubalgebra.topEquiv
  签名: : (⊤ : LieSubalgebra R L) ≃ₗ⁅R⁆ L
  定义体: { (⊤ : LieSubalgebra R L).incl with
    invFun := fun x => ⟨x, Set.mem_univ x⟩ }

@[simp]

Depends on / 依赖: LieSubalgebra, Set.mem_univ, invFun, mem_univ
-/
def LieSubalgebra.topEquiv : (⊤ : LieSubalgebra R L) ≃ₗ⁅R⁆ L :=
  { (⊤ : LieSubalgebra R L).incl with
    invFun := fun x => ⟨x, Set.mem_univ x⟩ }

@[simp]
/--
theorem `LieSubalgebra.topEquiv_apply` / 定理 `LieSubalgebra.topEquiv_apply`

English:
theorem LieSubalgebra.topEquiv_apply
  given: (x : (⊤ : LieSubalgebra R L))
  statement: LieSubalgebra.topEquiv x = x
  proof: rfl

中文:
定理 LieSubalgebra.topEquiv_apply
  条件: (x : (⊤ : LieSubalgebra R L))
  结论: LieSubalgebra.topEquiv x = x
  证明: rfl
-/
theorem LieSubalgebra.topEquiv_apply (x : (⊤ : LieSubalgebra R L)) : LieSubalgebra.topEquiv x = x :=
  rfl

end TopEquiv
