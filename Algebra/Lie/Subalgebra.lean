/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.RingTheory.Artinian.Module

/-!
# Lie subalgebras

This file defines Lie subalgebras of a Lie algebra and provides basic related definitions and
results.

## Main definitions

  * `LieSubalgebra`
  * `LieSubalgebra.incl`
  * `LieSubalgebra.map`
  * `LieHom.range`
  * `LieEquiv.ofInjective`
  * `LieEquiv.ofEq`
  * `LieEquiv.ofSubalgebras`

## Tags

lie algebra, lie subalgebra
-/

@[expose] public section


universe u v w w₁ w₂

section LieSubalgebra

open Set

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- A Lie subalgebra of a Lie algebra is submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie algebra. -/
/-
**LieSubalgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → (L : Type v) → [inst : CommRing R] → [inst_1 : LieRing L] →
 [LieAlgebra R L] → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie subalgebra of a Lie algebra is submodule that is closed under the Lie brac
ket.
This is a sufficient condition for the subset itself to form a Lie algebra.
-/
structure LieSubalgebra extends Submodule R L where
  /-- A Lie subalgebra is closed under Lie bracket. -/
  lie_mem' : ∀ {x y}, x ∈ carrier → y ∈ carrier → ⁅x, y⁆ ∈ carrier

/-- The zero algebra is a subalgebra of any Lie algebra. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The zero algebra is a subalgebra of any Lie algebra.
-/
instance : Zero (LieSubalgebra R L) :=
  ⟨⟨0, @fun x y hx _hy ↦ by
    rw [(Submodule.mem_bot R).1 hx, zero_lie]
    exact Submodule.zero_mem 0⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (LieSubalgebra R L) :=
  ⟨0⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (LieSubalgebra R L) (Submodule R L) :=
  ⟨LieSubalgebra.toSubmodule⟩

namespace LieSubalgebra

/-
**LieSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (LieSubalgebra R L) L where
  coe L' := L'.carrier
  coe_injective L' L'' h := by
    rcases L' with ⟨⟨⟩⟩
    rcases L'' with ⟨⟨⟩⟩
    congr
    exact SetLike.coe_injective h
/-
**LieSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (LieSubalgebra R L) := .ofSetLike (LieSubalgebra R L) L
/-
**LieSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddSubgroupClass (LieSubalgebra R L) L where
  add_mem := Submodule.add_mem _
  zero_mem L' := L'.zero_mem'
  neg_mem {L'} x hx := show -x ∈ (L' : Submodule R L) from neg_mem hx
/-
**LieSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulMemClass (LieSubalgebra R L) R L where
  smul_mem {s} := SMulMemClass.smul_mem (s := s.toSubmodule)

/-- A Lie subalgebra forms a new Lie ring. -/
/-
**LieSubalgebra.lieRing** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
形式化陈述：lieRing (L' : LieSubalgebra R L) : LieRing L' where bracket x y
参数：L' : LieSubalgebra R L。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L

--- 原说明 ---
A Lie subalgebra forms a new Lie ring.
-/
instance lieRing (L' : LieSubalgebra R L) : LieRing L' where
  bracket x y := ⟨⁅x.val, y.val⁆, L'.lie_mem' x.property y.property⟩
  lie_add := by
    intros
    apply SetCoe.ext
    apply lie_add
  add_lie := by
    intros
    apply SetCoe.ext
    apply add_lie
  lie_self := by
    intros
    apply SetCoe.ext
    apply lie_self
  leibniz_lie := by
    intros
    apply SetCoe.ext
    apply leibniz_lie

section

variable {R₁ : Type*} [Semiring R₁]

/-- A Lie subalgebra inherits module structures from `L`. -/
/-
**LieSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie subalgebra inherits module structures from `L`.
-/
instance [SMul R₁ R] [Module R₁ L] [IsScalarTower R₁ R L] (L' : LieSubalgebra R L) : Module R₁ L' :=
  L'.toSubmodule.module'
/-
**LieSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R₁ R] [SMul R₁ᵐᵒᵖ R] [Module R₁ L] [Module R₁ᵐᵒᵖ L] [IsScalarTower R₁ R L]
    [IsScalarTower R₁ᵐᵒᵖ R L] [IsCentralScalar R₁ L] (L' : LieSubalgebra R L) :
    IsCentralScalar R₁ L' :=
  L'.toSubmodule.isCentralScalar
/-
**LieSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R₁ R] [Module R₁ L] [IsScalarTower R₁ R L] (L' : LieSubalgebra R L) :
    IsScalarTower R₁ R L' :=
  L'.toSubmodule.isScalarTower
/-
**LieSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L' : LieSubalgebra R L) [IsNoetherian R L] : IsNoetherian R L' :=
  isNoetherian_submodule' _
/-
**LieSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L' : LieSubalgebra R L) [IsArtinian R L] : IsArtinian R L' :=
  isArtinian_submodule' _

end

/-- A Lie subalgebra forms a new Lie algebra. -/
/-
**LieSubalgebra.lieAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
形式化陈述：lieAlgebra (L' : LieSubalgebra R L) : LieAlgebra R L' where lie_smul
参数：L' : LieSubalgebra R L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie subalgebra forms a new Lie algebra.
-/
instance lieAlgebra (L' : LieSubalgebra R L) : LieAlgebra R L' where
  lie_smul := by
    { intros
      apply SetCoe.ext
      apply lie_smul }

variable {R L}
variable (L' : LieSubalgebra R L)
/-
**LieSubalgebra.zero_mem** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：∀ {R : Type u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst
_2 : LieAlgebra R L] (L' : LieSubalgebra R L),   0 ∈ L'
参数：L' : LieSubalgebra R L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
-/
protected theorem zero_mem : (0 : L) ∈ L' :=
  zero_mem L'
/-
**LieSubalgebra.add_mem** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：∀ {R : Type u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst
_2 : LieAlgebra R L] (L' : LieSubalgebra R L)   {x y : L}, x ∈ L' → y ∈ L' → x +
 y ∈ L'
参数：L' : LieSubalgebra R L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
-/
protected theorem add_mem {x y : L} : x ∈ L' → y ∈ L' → (x + y : L) ∈ L' :=
  add_mem
/-
**LieSubalgebra.sub_mem** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：∀ {R : Type u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst
_2 : LieAlgebra R L] (L' : LieSubalgebra R L)   {x y : L}, x ∈ L' → y ∈ L' → x -
 y ∈ L'
参数：L' : LieSubalgebra R L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
-/
protected theorem sub_mem {x y : L} : x ∈ L' → y ∈ L' → (x - y : L) ∈ L' :=
  sub_mem
/-
**LieSubalgebra.smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：∀ {R : Type u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst
_2 : LieAlgebra R L] (L' : LieSubalgebra R L)   (t : R) {x : L}, x ∈ L' → t • x 
∈ L'
参数：L' : LieSubalgebra R L；t : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `LieSubalgebra.instSMulMemClass`：∀ (R : Type u) (L : Type v) [inst : Comm
Ring R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   SMulMemClass (LieSubal
gebra R L) R L
-/
protected theorem smul_mem (t : R) {x : L} (h : x ∈ L') : t • x ∈ L' :=
  SMulMemClass.smul_mem _ h
/-
**LieSubalgebra.lie_mem** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：lie_mem {x y : L} (hx : x in L') (hy : y in L') : (⁅x, y⁆ : L) in L'
参数：hx : x in L'；hy : y in L'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.lie_mem'`：∀ {R : Type u} {L : Type v} [inst : CommRing R] 
[inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   (self : LieSubalgebra R L) {x y
 : L}, x ∈ s…
-/
theorem lie_mem {x y : L} (hx : x ∈ L') (hy : y ∈ L') : (⁅x, y⁆ : L) ∈ L' :=
  L'.lie_mem' hx hy
/-
**LieSubalgebra.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：mem_carrier {x : L} : x in L'.carrier ↔ x in (L' : Set L)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier {x : L} : x ∈ L'.carrier ↔ x ∈ (L' : Set L) :=
  Iff.rfl
/-
**LieSubalgebra.mem_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：mem_mk_iff (S : Set L) (h₁ h₂ h₃ h₄) {x : L} : x in (⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩,
 h₄⟩ : LieSubalgebra R L) ↔ x in S
参数：S : Set L；h₁ h₂ h₃ h₄。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk_iff (S : Set L) (h₁ h₂ h₃ h₄) {x : L} :
    x ∈ (⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieSubalgebra R L) ↔ x ∈ S :=
  Iff.rfl

@[simp]
/-
**LieSubalgebra.mem_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：mem_toSubmodule {x : L} : x in (L' : Submodule R L) ↔ x in L'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toSubmodule {x : L} : x ∈ (L' : Submodule R L) ↔ x ∈ L' :=
  Iff.rfl

@[simp]
/-
**LieSubalgebra.mem_mk_iff'** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：mem_mk_iff' (p : Submodule R L) (h) {x : L} : x in (⟨p, h⟩ : LieSubalgebra
 R L) ↔ x in p
参数：p : Submodule R L；h。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk_iff' (p : Submodule R L) (h) {x : L} :
    x ∈ (⟨p, h⟩ : LieSubalgebra R L) ↔ x ∈ p :=
  Iff.rfl
/-
**LieSubalgebra.mem_coe** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：mem_coe {x : L} : x in (L' : Set L) ↔ x in L'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_coe {x : L} : x ∈ (L' : Set L) ↔ x ∈ L' :=
  Iff.rfl

@[simp, norm_cast]
/-
**LieSubalgebra.coe_bracket** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：coe_bracket (x y : L') : (↑⁅x, y⁆ : L) = ⁅(↑x : L), ↑y⁆
参数：x y : L'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bracket (x y : L') : (↑⁅x, y⁆ : L) = ⁅(↑x : L), ↑y⁆ :=
  rfl
/-
**LieSubalgebra.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：ext_iff (x y : L') : x = y ↔ (x : L) = y
参数：x y : L'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem ext_iff (x y : L') : x = y ↔ (x : L) = y :=
  Subtype.ext_iff
/-
**LieSubalgebra.coe_zero_iff_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：coe_zero_iff_zero (x : L') : (x : L) = 0 ↔ x = 0
参数：x : L'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `LieSubalgebra.ext_iff`：ext_iff (x y : L') : x = y ↔ (x : L) = y
-/
theorem coe_zero_iff_zero (x : L') : (x : L) = 0 ↔ x = 0 :=
  (ext_iff L' x 0).symm

@[ext]
/-
**LieSubalgebra.ext** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：ext (L₁' L₂' : LieSubalgebra R L) (h : forall x, x in L₁' ↔ x in L₂') : L₁
' = L₂'
参数：L₁' L₂' : LieSubalgebra R L；h : forall x, x in L₁' ↔ x in L₂'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
theorem ext (L₁' L₂' : LieSubalgebra R L) (h : ∀ x, x ∈ L₁' ↔ x ∈ L₂') : L₁' = L₂' :=
  SetLike.ext h
/-
**LieSubalgebra.ext_iff'** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：ext_iff' (L₁' L₂' : LieSubalgebra R L) : L₁' = L₂' ↔ forall x, x in L₁' ↔ 
x in L₂'
参数：L₁' L₂' : LieSubalgebra R L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
-/
theorem ext_iff' (L₁' L₂' : LieSubalgebra R L) : L₁' = L₂' ↔ ∀ x, x ∈ L₁' ↔ x ∈ L₂' :=
  SetLike.ext_iff

@[simp]
/-
**LieSubalgebra.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：mk_coe (S : Set L) (h₁ h₂ h₃ h₄) : ((⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieSubalg
ebra R L) : Set L) = S
参数：S : Set L；h₁ h₂ h₃ h₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_coe (S : Set L) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieSubalgebra R L) : Set L) = S :=
  rfl
/-
**LieSubalgebra.toSubmodule_mk** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：toSubmodule_mk (p : Submodule R L) (h) : (({ p with lie_mem'
参数：p : Submodule R L；h。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubmodule_mk (p : Submodule R L) (h) :
    (({ p with lie_mem' := h } : LieSubalgebra R L) : Submodule R L) = p := rfl
/-
**LieSubalgebra.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：coe_injective : Function.Injective ((↑) : LieSubalgebra R L -> Set L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem coe_injective : Function.Injective ((↑) : LieSubalgebra R L → Set L) :=
  SetLike.coe_injective

@[norm_cast]
/-
**LieSubalgebra.coe_set_eq** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：coe_set_eq (L₁' L₂' : LieSubalgebra R L) : (L₁' : Set L) = L₂' ↔ L₁' = L₂'
参数：L₁' L₂' : LieSubalgebra R L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_set_eq`：coe_set_eq : (p : Set B) = q ↔ p = q
-/
theorem coe_set_eq (L₁' L₂' : LieSubalgebra R L) : (L₁' : Set L) = L₂' ↔ L₁' = L₂' :=
  SetLike.coe_set_eq
/-
**LieSubalgebra.toSubmodule_injective** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：toSubmodule_injective : Function.Injective ((↑) : LieSubalgebra R L -> Sub
module R L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubalgebra.coe_set_eq`：coe_set_eq (L₁' L₂' : LieSubalgebra R L) : (L₁
' : Set L) = L₂' ↔ L₁' = L₂'
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
-/
theorem toSubmodule_injective : Function.Injective ((↑) : LieSubalgebra R L → Submodule R L) :=
  fun L₁' L₂' h ↦ by
  rw [SetLike.ext'_iff] at h
  rw [← coe_set_eq]
  exact h

@[simp]
/-
**LieSubalgebra.toSubmodule_inj** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：toSubmodule_inj (L₁' L₂' : LieSubalgebra R L) : (L₁' : Submodule R L) = (L
₂' : Submodule R L) ↔ L₁' = L₂'
参数：L₁' L₂' : LieSubalgebra R L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LieSubalgebra.toSubmodule_injective`：toSubmodule_injective : Function.In
jective ((↑) : LieSubalgebra R L -> Submodule R L)
-/
theorem toSubmodule_inj (L₁' L₂' : LieSubalgebra R L) :
    (L₁' : Submodule R L) = (L₂' : Submodule R L) ↔ L₁' = L₂' :=
  toSubmodule_injective.eq_iff
/-
**LieSubalgebra.coe_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：coe_toSubmodule : ((L' : Submodule R L) : Set L) = L'
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSubmodule : ((L' : Submodule R L) : Set L) = L' :=
  rfl

section LieModule

variable {M : Type w} [AddCommGroup M] [LieRingModule L M]
variable {N : Type w₁} [AddCommGroup N] [LieRingModule L N] [Module R N]

/-
**LieSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bracket L' M where
  bracket x m := ⁅(x : L), m⁆

@[simp]
/-
**LieSubalgebra.coe_bracket_of_module** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：coe_bracket_of_module (x : L') (m : M) : ⁅x, m⁆ = ⁅(x : L), m⁆
参数：x : L'；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bracket_of_module (x : L') (m : M) : ⁅x, m⁆ = ⁅(x : L), m⁆ :=
  rfl
/-
**LieSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLieTower L' L M where
  leibniz_lie x y m := leibniz_lie x.val y m

/-- Given a Lie algebra `L` containing a Lie subalgebra `L' ⊆ L`, together with a Lie ring module
`M` of `L`, we may regard `M` as a Lie ring module of `L'` by restriction. -/
/-
**LieSubalgebra.lieRingModule** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
形式化陈述：lieRingModule : LieRingModule L' M where add_lie x y m
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a Lie algebra `L` containing a Lie subalgebra `L' ⊆ L`, together with a Li
e ring module
`M` of `L`, we may regard `M` as a Lie ring module of `L'` by restriction.
-/
instance lieRingModule : LieRingModule L' M where
  add_lie x y m := add_lie (x : L) y m
  lie_add x y m := lie_add (x : L) y m
  leibniz_lie x y m := leibniz_lie x (y : L) m

variable [Module R M]

/-- Given a Lie algebra `L` containing a Lie subalgebra `L' ⊆ L`, together with a Lie module `M` of
`L`, we may regard `M` as a Lie module of `L'` by restriction. -/
/-
**LieSubalgebra.lieModule** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
形式化陈述：lieModule [LieModule R L M] : LieModule R L' M where smul_lie t x m
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubalgebra.coe_bracket_of_module`：coe_bracket_of_module (x : L') (m :
 M) : ⁅x, m⁆ = ⁅(x : L), m⁆
· 使用定理 `Submodule.coe_smul_of_tower`：coe_smul_of_tower [SMul S R] [SMul S M] [Is
ScalarTower S R M] (r : S) (x : p) : ((r • x : p) : M) = r • (x : M)
· 使用定理 `smul_lie`：smul_lie : ⁅t • x, m⁆ = t • ⁅x, m⁆
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `lie_smul`：lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given a Lie algebra `L` containing a Lie subalgebra `L' ⊆ L`, together with a Li
e module `M` of
`L`, we may regard `M` as a Lie module of `L'` by restriction.
-/
instance lieModule [LieModule R L M] : LieModule R L' M where
  smul_lie t x m := by
    rw [coe_bracket_of_module, Submodule.coe_smul_of_tower, smul_lie, coe_bracket_of_module]
  lie_smul t x m := by simp only [coe_bracket_of_module, lie_smul]

/-- An `L`-equivariant map of Lie modules `M → N` is `L'`-equivariant for any Lie subalgebra
`L' ⊆ L`. -/
/-
**LieSubalgebra._root_.LieModuleHom.restrictLie** 是 Mathlib 中的一个定义，位于命名空间 `LieSu
balgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `L`-equivariant map of Lie modules `M → N` is `L'`-equivariant for any Lie su
balgebra
`L' ⊆ L`.
-/
def _root_.LieModuleHom.restrictLie (f : M →ₗ⁅R,L⁆ N) (L' : LieSubalgebra R L) : M →ₗ⁅R,L'⁆ N :=
  { (f : M →ₗ[R] N) with map_lie' := @fun x m ↦ f.map_lie (↑x) m }

@[simp]
/-
**LieSubalgebra._root_.LieModuleHom.coe_restrictLie** 是 Mathlib 中的一个定理，位于命名空间 `L
ieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LieModuleHom.coe_restrictLie (f : M →ₗ⁅R,L⁆ N) : ⇑(f.restrictLie L') = f :=
  rfl

end LieModule

/-- The embedding of a Lie subalgebra into the ambient space as a morphism of Lie algebras. -/
/-
**LieSubalgebra.incl** 是 Mathlib 中的一个定义，位于命名空间 `LieSubalgebra`。
形式化陈述：incl : L' ->ₗ⁅R⁆ L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding of a Lie subalgebra into the ambient space as a morphism of Lie al
gebras.
-/
def incl : L' →ₗ⁅R⁆ L :=
  { (L' : Submodule R L).subtype with
    map_lie' := rfl }

@[simp]
/-
**LieSubalgebra.coe_incl** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：coe_incl : ⇑L'.incl = ((↑) : L' -> L)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_incl : ⇑L'.incl = ((↑) : L' → L) :=
  rfl

/-- The embedding of a Lie subalgebra into the ambient space as a morphism of Lie modules. -/
/-
**LieSubalgebra.incl'** 是 Mathlib 中的一个定义，位于命名空间 `LieSubalgebra`。
形式化陈述：incl' : L' ->ₗ⁅R,L'⁆ L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding of a Lie subalgebra into the ambient space as a morphism of Lie mo
dules.
-/
def incl' : L' →ₗ⁅R,L'⁆ L :=
  { (L' : Submodule R L).subtype with
    map_lie' := rfl }

@[simp]
/-
**LieSubalgebra.coe_incl'** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：coe_incl' : ⇑L'.incl' = ((↑) : L' -> L)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_incl' : ⇑L'.incl' = ((↑) : L' → L) :=
  rfl

end LieSubalgebra

variable {R L}
variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]
variable (f : L →ₗ⁅R⁆ L₂)

namespace LieHom

/-- The range of a morphism of Lie algebras is a Lie subalgebra. -/
/-
**LieHom.range** 是 Mathlib 中的一个定义，位于命名空间 `LieHom`。
形式化陈述：range : LieSubalgebra R L₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a morphism of Lie algebras is a Lie subalgebra.
-/
def range : LieSubalgebra R L₂ :=
  { LinearMap.range (f : L →ₗ[R] L₂) with
      lie_mem' := by
        rintro - - ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨⁅x, y⁆, f.map_lie x y⟩ }

@[simp]
/-
**LieHom.coe_range** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：coe_range : (f.range : Set L₂) = Set.range f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.coe_range`：coe_range [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] 
M₂) : (range f : Set M₂) = Set.range f
-/
theorem coe_range : (f.range : Set L₂) = Set.range f :=
  LinearMap.coe_range (f : L →ₗ[R] L₂)

@[simp]
/-
**LieHom.mem_range** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：mem_range (x : L₂) : x in f.range ↔ exists y : L, f y = x
参数：x : L₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mem_range`：mem_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] 
M₂} {x} : x in range f ↔ exists y, f y = x
-/
theorem mem_range (x : L₂) : x ∈ f.range ↔ ∃ y : L, f y = x :=
  LinearMap.mem_range
/-
**LieHom.mem_range_self** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：mem_range_self (x : L) : f x in f.range
参数：x : L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
-/
theorem mem_range_self (x : L) : f x ∈ f.range :=
  LinearMap.mem_range_self (f : L →ₗ[R] L₂) x

/-- We can restrict a morphism to a (surjective) map to its range. -/
/-
**LieHom.rangeRestrict** 是 Mathlib 中的一个定义，位于命名空间 `LieHom`。
形式化陈述：rangeRestrict : L ->ₗ⁅R⁆ f.range
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can restrict a morphism to a (surjective) map to its range.
-/
def rangeRestrict : L →ₗ⁅R⁆ f.range :=
  { (f : L →ₗ[R] L₂).rangeRestrict with
    map_lie' := @fun x y ↦ by
      apply Subtype.ext
      exact f.map_lie x y }

@[simp]
/-
**LieHom.rangeRestrict_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：rangeRestrict_apply (x : L) : f.rangeRestrict x = ⟨f x, f.mem_range_self x
⟩
参数：x : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rangeRestrict_apply (x : L) : f.rangeRestrict x = ⟨f x, f.mem_range_self x⟩ :=
  rfl
/-
**LieHom.surjective_rangeRestrict** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：surjective_rangeRestrict : Function.Surjective f.rangeRestrict
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieHom.mem_range`：mem_range (x : L₂) : x in f.range ↔ exists y : L, f y 
= x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LieHom.mem_range_self`：mem_range_self (x : L) : f x in f.range
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem surjective_rangeRestrict : Function.Surjective f.rangeRestrict := by
  rintro ⟨y, hy⟩
  rw [mem_range] at hy; obtain ⟨x, rfl⟩ := hy
  use x
  simp only [rangeRestrict_apply]

/-- A Lie algebra is equivalent to its range under an injective Lie algebra morphism. -/
/-
**LieHom.equivRangeOfInjective** 是 Mathlib 中的一个定义，位于命名空间 `LieHom`。
形式化陈述：equivRangeOfInjective (h : Function.Injective f) : L ≃ₗ⁅R⁆ f.range
参数：h : Function.Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie algebra is equivalent to its range under an injective Lie algebra morphism
.
-/
noncomputable def equivRangeOfInjective (h : Function.Injective f) : L ≃ₗ⁅R⁆ f.range :=
  LieEquiv.ofBijective f.rangeRestrict
    ⟨fun x y hxy ↦ by
      simp only [Subtype.mk_eq_mk, rangeRestrict_apply] at hxy
      exact h hxy, f.surjective_rangeRestrict⟩

@[simp]
/-
**LieHom.equivRangeOfInjective_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：equivRangeOfInjective_apply (h : Function.Injective f) (x : L) : f.equivRa
ngeOfInjective h x = ⟨f x, mem_range_self f x⟩
参数：h : Function.Injective f；x : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivRangeOfInjective_apply (h : Function.Injective f) (x : L) :
    f.equivRangeOfInjective h x = ⟨f x, mem_range_self f x⟩ :=
  rfl

end LieHom

/-
**Submodule.exists_lieSubalgebra_coe_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.exists_lieSubalgebra_coe_eq_iff (p : Submodule R L) : (exists K 
: LieSubalgebra R L, ↑K = p) ↔ forall x y : L, x in p -> y in p -> ⁅x, y⁆ in p
参数：p : Submodule R L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.lie_mem'`：∀ {R : Type u} {L : Type v} [inst : CommRing R] 
[inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   (self : LieSubalgebra R L) {x y
 : L}, x ∈ s…
-/
theorem Submodule.exists_lieSubalgebra_coe_eq_iff (p : Submodule R L) :
    (∃ K : LieSubalgebra R L, ↑K = p) ↔ ∀ x y : L, x ∈ p → y ∈ p → ⁅x, y⁆ ∈ p := by
  constructor
  · rintro ⟨K, rfl⟩ _ _
    exact K.lie_mem'
  · intro h
    use { p with lie_mem' := h _ _ }

namespace LieSubalgebra

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

@[simp]
/-
**LieSubalgebra.incl_range** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：incl_range : K.incl.range = K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubalgebra.toSubmodule_inj`：toSubmodule_inj (L₁' L₂' : LieSubalgebra 
R L) : (L₁' : Submodule R L) = (L₂' : Submodule R L) ↔ L₁' = L₂'
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
-/
theorem incl_range : K.incl.range = K := by
  rw [← toSubmodule_inj]
  exact (K : Submodule R L).range_subtype

/-- The image of a Lie subalgebra under a Lie algebra morphism is a Lie subalgebra of the
codomain. -/
/-
**LieSubalgebra.map** 是 Mathlib 中的一个定义，位于命名空间 `LieSubalgebra`。
形式化陈述：map : LieSubalgebra R L₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a Lie subalgebra under a Lie algebra morphism is a Lie subalgebra o
f the
codomain.
-/
def map : LieSubalgebra R L₂ :=
  { (K : Submodule R L).map (f : L →ₗ[R] L₂) with
    lie_mem' {x y} hx hy := by
      simp only [AddSubsemigroup.mem_carrier] at hx hy
      rcases hx with ⟨x', hx', rfl⟩
      rcases hy with ⟨y', hy', rfl⟩
      simpa using ⟨⁅x', y'⁆, K.lie_mem hx' hy', f.map_lie x' y'⟩ }

@[simp]
/-
**LieSubalgebra.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：mem_map (x : L₂) : x in K.map f ↔ exists y : L, y in K ∧ f y = x
参数：x : L₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_map`：mem_map {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x :
 M₂} : x in map f p ↔ exists y, y in p ∧ f y = x
-/
theorem mem_map (x : L₂) : x ∈ K.map f ↔ ∃ y : L, y ∈ K ∧ f y = x :=
  Submodule.mem_map

-- TODO Rename and state for homs instead of equivs.
/-
**LieSubalgebra.mem_map_submodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：mem_map_submodule (e : L ≃ₗ⁅R⁆ L₂) (x : L₂) : x in K.map (e : L ->ₗ⁅R⁆ L₂)
 ↔ x in (K : Submodule R L).map (e : L ->ₗ[R] L₂)
参数：e : L ≃ₗ⁅R⁆ L₂；x : L₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_map_submodule (e : L ≃ₗ⁅R⁆ L₂) (x : L₂) :
    x ∈ K.map (e : L →ₗ⁅R⁆ L₂) ↔ x ∈ (K : Submodule R L).map (e : L →ₗ[R] L₂) :=
  Iff.rfl

/-- The preimage of a Lie subalgebra under a Lie algebra morphism is a Lie subalgebra of the
domain. -/
/-
**LieSubalgebra.comap** 是 Mathlib 中的一个定义，位于命名空间 `LieSubalgebra`。
形式化陈述：comap : LieSubalgebra R L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of a Lie subalgebra under a Lie algebra morphism is a Lie subalgebr
a of the
domain.
-/
def comap : LieSubalgebra R L :=
  { (K₂ : Submodule R L₂).comap (f : L →ₗ[R] L₂) with
    lie_mem' := @fun x y hx hy ↦ by
      suffices ⁅f x, f y⁆ ∈ K₂ by simp [this]
      exact K₂.lie_mem hx hy }
/-
**LieSubalgebra.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：∀ {R : Type u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst
_2 : LieAlgebra R L] {L₂ : Type w}   [inst_3 : LieRing L₂] [inst_4 : LieAlgebra 
R L₂] (f : L →ₗ⁅R⁆ L₂) (K₂ : LieSubalgebra R L₂) {x : L},   x ∈ LieSubalgebra.co
map f K₂ ↔ f x ∈ K₂
参数：f : L →ₗ⁅R⁆ L₂；K₂ : LieSubalgebra R L₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_comap {x : L} : x ∈ K₂.comap f ↔ f x ∈ K₂ := Iff.rfl

/-- A Lie subalgebra is equivalent to its push forward along an injective linear map. -/
/-
**LieSubalgebra.equivMapOfInjective** 是 Mathlib 中的一个定义，位于命名空间 `LieSubalgebra`。
形式化陈述：{R : Type u} →   {L : Type v} →     [inst : CommRing R] →       [inst_1 : 
LieRing L] →         [inst_2 : LieAlgebra R L] →           {L₂ : Type w} →      
       [inst_3 : LieRing L₂] →               [inst_4 : LieAlgebra R L₂] →       
          (f : L →ₗ⁅R⁆ L₂) → (K : LieSubalgebra R L) → Function.Injective ⇑f → ↥
K ≃ₗ⁅R⁆ ↥(LieSubalgebra.map f K)
参数：f : L →ₗ⁅R⁆ L₂；K : LieSubalgebra R L；LieSubalgebra.map f K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie subalgebra is equivalent to its push forward along an injective linear map
.
-/
@[simps!] noncomputable def equivMapOfInjective (hf : Function.Injective f) :
    K ≃ₗ⁅R⁆ K.map f where
  __ := Submodule.equivMapOfInjective f.toLinearMap hf K
  map_lie' {x y} := by
    ext
    change f ⁅(x : L), (y : L)⁆ = ⁅f (x : L), f (y : L)⁆
    simp

section LatticeStructure

open Set

/-
**LieSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (LieSubalgebra R L) :=
  { PartialOrder.lift ((↑) : LieSubalgebra R L → Set L) coe_injective with
    le := fun N N' ↦ ∀ ⦃x⦄, x ∈ N → x ∈ N' }
/-
**LieSubalgebra.le_def** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：le_def : K <= K' ↔ (K : Set L) subseteq K'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def : K ≤ K' ↔ (K : Set L) ⊆ K' :=
  Iff.rfl

@[simp]
/-
**LieSubalgebra.toSubmodule_le_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalge
bra`。
形式化陈述：toSubmodule_le_toSubmodule : (K : Submodule R L) <= K' ↔ K <= K'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSubmodule_le_toSubmodule : (K : Submodule R L) ≤ K' ↔ K ≤ K' :=
  Iff.rfl
/-
**LieSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (LieSubalgebra R L) :=
  ⟨0⟩

@[simp]
/-
**LieSubalgebra.bot_coe** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：bot_coe : ((⊥ : LieSubalgebra R L) : Set L) = {0}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_coe : ((⊥ : LieSubalgebra R L) : Set L) = {0} :=
  rfl

@[simp]
/-
**LieSubalgebra.bot_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：bot_toSubmodule : ((⊥ : LieSubalgebra R L) : Submodule R L) = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_toSubmodule : ((⊥ : LieSubalgebra R L) : Submodule R L) = ⊥ :=
  rfl
/-
**LieSubalgebra.toSubmodule_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：∀ {R : Type u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst
_2 : LieAlgebra R L] (K : LieSubalgebra R L),   K.toSubmodule = ⊥ ↔ K = ⊥
参数：K : LieSubalgebra R L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toSubmodule_eq_bot (K : LieSubalgebra R L) : K.toSubmodule = ⊥ ↔ K = ⊥ := by
  simp [← toSubmodule_inj]

@[simp]
/-
**LieSubalgebra.mem_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：mem_bot (x : L) : x in (⊥ : LieSubalgebra R L) ↔ x = 0
参数：x : L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem mem_bot (x : L) : x ∈ (⊥ : LieSubalgebra R L) ↔ x = 0 :=
  mem_singleton_iff
/-
**LieSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Top (LieSubalgebra R L) :=
  ⟨{ (⊤ : Submodule R L) with lie_mem' := @fun x y _ _ ↦ mem_univ ⁅x, y⁆ }⟩

@[simp]
/-
**LieSubalgebra.top_coe** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：top_coe : ((⊤ : LieSubalgebra R L) : Set L) = univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_coe : ((⊤ : LieSubalgebra R L) : Set L) = univ :=
  rfl

@[simp]
/-
**LieSubalgebra.top_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：top_toSubmodule : ((⊤ : LieSubalgebra R L) : Submodule R L) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_toSubmodule : ((⊤ : LieSubalgebra R L) : Submodule R L) = ⊤ :=
  rfl
/-
**LieSubalgebra.toSubmodule_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：∀ {R : Type u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst
_2 : LieAlgebra R L] (K : LieSubalgebra R L),   K.toSubmodule = ⊤ ↔ K = ⊤
参数：K : LieSubalgebra R L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toSubmodule_eq_top (K : LieSubalgebra R L) : K.toSubmodule = ⊤ ↔ K = ⊤ := by
  simp [← toSubmodule_inj]

@[simp]
/-
**LieSubalgebra.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：mem_top (x : L) : x in (⊤ : LieSubalgebra R L)
参数：x : L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem mem_top (x : L) : x ∈ (⊤ : LieSubalgebra R L) :=
  mem_univ x
/-
**LieSubalgebra._root_.LieHom.range_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalge
bra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LieHom.range_eq_map : f.range = map f ⊤ := by
  ext
  simp
/-
**LieSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (LieSubalgebra R L) :=
  ⟨fun K K' ↦
    { (K ⊓ K' : Submodule R L) with
      lie_mem' := fun hx hy ↦ mem_inter (K.lie_mem hx.1 hy.1) (K'.lie_mem hx.2 hy.2) }⟩
/-
**LieSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (LieSubalgebra R L) :=
  ⟨fun S ↦
    { sInf {(s : Submodule R L) | s ∈ S} with
      lie_mem' := @fun x y hx hy ↦ by
        simp only [Submodule.mem_carrier, mem_iInter, Submodule.coe_sInf, mem_ofPred_eq,
          forall_apply_eq_imp_iff₂, exists_imp, and_imp] at hx hy ⊢
        intro K hK
        exact K.lie_mem (hx K hK) (hy K hK) }⟩

@[simp]
/-
**LieSubalgebra.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：coe_inf : (↑(K ⊓ K') : Set L) = (K : Set L) inter (K' : Set L)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf : (↑(K ⊓ K') : Set L) = (K : Set L) ∩ (K' : Set L) :=
  rfl

@[simp]
/-
**LieSubalgebra.sInf_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：sInf_toSubmodule (S : Set (LieSubalgebra R L)) : (↑(sInf S) : Submodule R 
L) = sInf {(s : Submodule R L) | s in S}
参数：S : Set (LieSubalgebra R L)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sInf_toSubmodule (S : Set (LieSubalgebra R L)) :
    (↑(sInf S) : Submodule R L) = sInf {(s : Submodule R L) | s ∈ S} :=
  rfl

@[simp]
/-
**LieSubalgebra.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：coe_sInf (S : Set (LieSubalgebra R L)) : (↑(sInf S) : Set L) = ⋂ s in S, (
s : Set L)
参数：S : Set (LieSubalgebra R L)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubalgebra.coe_toSubmodule`：coe_toSubmodule : ((L' : Submodule R L) :
 Set L) = L'
· 使用定理 `LieSubalgebra.sInf_toSubmodule`：sInf_toSubmodule (S : Set (LieSubalgebra
 R L)) : (↑(sInf S) : Submodule R L) = sInf {(s : Submodule R L) | s in S}
· 使用定理 `Submodule.coe_sInf`：coe_sInf (P : Set (Submodule R M)) : (↑(sInf P) : Se
t M) = ⋂ p in P, ↑p
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biInter_and'`：biInter_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_iInter_eq_right`：iInter_iInter_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋂ (x) (h : b = x), s x h = s b rfl
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_sInf (S : Set (LieSubalgebra R L)) : (↑(sInf S) : Set L) = ⋂ s ∈ S, (s : Set L) := by
  rw [← coe_toSubmodule, sInf_toSubmodule, Submodule.coe_sInf]
  ext x
  simp
/-
**LieSubalgebra.sInf_glb** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：sInf_glb (S : Set (LieSubalgebra R L)) : IsGLB S (sInf S)
参数：S : Set (LieSubalgebra R L)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `IsGLB.of_image`：IsGLB.of_image [Preorder α] [Preorder β] {f : α -> β} (h
f : forall {x y}, f x <= f y ↔ x <= y) {s : Set α} {x : α} (hx : IsGLB (f '' s) 
(f x…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubalgebra.coe_sInf`：coe_sInf (S : Set (LieSubalgebra R L)) : (↑(sInf
 S) : Set L) = ⋂ s in S, (s : Set L)
· 使用定理 `isGLB_biInf`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] 
{s : Set β} {f : β → α}, IsGLB (f '' s) (⨅ x ∈ s, f x)
-/
theorem sInf_glb (S : Set (LieSubalgebra R L)) : IsGLB S (sInf S) := by
  have h : ∀ K K' : LieSubalgebra R L, (K : Set L) ≤ K' ↔ K ≤ K' := by
    intros
    exact Iff.rfl
  apply IsGLB.of_image @h
  simp only [coe_sInf]
  exact isGLB_biInf

/-- The set of Lie subalgebras of a Lie algebra form a complete lattice.

We provide explicit values for the fields `bot`, `top`, `inf` to get more convenient definitions
than we would otherwise obtain from `completeLatticeOfInf`. -/
/-
**LieSubalgebra.completeLattice** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
形式化陈述：completeLattice : CompleteLattice (LieSubalgebra R L)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.sInf_glb`：sInf_glb (S : Set (LieSubalgebra R L)) : IsGLB S
 (sInf S)
· 使用定理 `trivial`：True

--- 原说明 ---
The set of Lie subalgebras of a Lie algebra form a complete lattice.

We provide explicit values for the fields `bot`, `top`, `inf` to get more conven
ient definitions
than we would otherwise obtain from `completeLatticeOfInf`.
-/
instance completeLattice : CompleteLattice (LieSubalgebra R L) :=
  { completeLatticeOfInf _ sInf_glb with
    bot := ⊥
    bot_le := fun N _ h ↦ by
      rw [mem_bot] at h
      rw [h]
      exact N.zero_mem'
    top := ⊤
    le_top := fun _ _ _ ↦ trivial
    inf := (· ⊓ ·)
    le_inf := fun _ _ _ h₁₂ h₁₃ _ hm ↦ ⟨h₁₂ hm, h₁₃ hm⟩
    inf_le_left := fun _ _ _ ↦ And.left
    inf_le_right := fun _ _ _ ↦ And.right }
/-
**LieSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (LieSubalgebra R L) where add := max
/-
**LieSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (LieSubalgebra R L) where zero := ⊥
/-
**LieSubalgebra.addCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
形式化陈述：addCommMonoid : AddCommMonoid (LieSubalgebra R L) where add_assoc
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommMonoid : AddCommMonoid (LieSubalgebra R L) where
  add_assoc := sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  nsmul := nsmulRec
/-
**LieSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderedAddMonoid (LieSubalgebra R L) where
  add_le_add_left _ _ := sup_le_sup_right
/-
**LieSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CanonicallyOrderedAdd (LieSubalgebra R L) where
  exists_add_of_le {_a b} h := ⟨b, (sup_eq_right.2 h).symm⟩
  le_add_self _ _ := le_sup_right
  le_self_add _ _ := le_sup_left

@[simp]
/-
**LieSubalgebra.add_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：add_eq_sup : K + K' = K ⊔ K'
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_eq_sup : K + K' = K ⊔ K' :=
  rfl

@[simp]
/-
**LieSubalgebra.inf_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：inf_toSubmodule : (↑(K ⊓ K') : Submodule R L) = (K : Submodule R L) ⊓ (K' 
: Submodule R L)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_toSubmodule :
    (↑(K ⊓ K') : Submodule R L) = (K : Submodule R L) ⊓ (K' : Submodule R L) :=
  rfl

@[simp]
/-
**LieSubalgebra.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：mem_inf (x : L) : x in K ⊓ K' ↔ x in K ∧ x in K'
参数：x : L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubalgebra.mem_toSubmodule`：mem_toSubmodule {x : L} : x in (L' : Subm
odule R L) ↔ x in L'
· 使用定理 `LieSubalgebra.inf_toSubmodule`：inf_toSubmodule : (↑(K ⊓ K') : Submodule 
R L) = (K : Submodule R L) ⊓ (K' : Submodule R L)
· 使用定理 `Submodule.mem_inf`：mem_inf {p q : Submodule R M} {x : M} : x in p ⊓ q ↔ 
x in p ∧ x in q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inf (x : L) : x ∈ K ⊓ K' ↔ x ∈ K ∧ x ∈ K' := by
  rw [← mem_toSubmodule, ← mem_toSubmodule, ← mem_toSubmodule, inf_toSubmodule,
    Submodule.mem_inf]
/-
**LieSubalgebra.eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：eq_bot_iff : K = ⊥ ↔ forall x : L, x in K -> x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_bot_iff : K = ⊥ ↔ ∀ x : L, x ∈ K → x = 0 := by
  rw [_root_.eq_bot_iff]
  exact Iff.rfl
/-
**LieSubalgebra.subsingleton_of_bot** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalgebra`。
形式化陈述：subsingleton_of_bot : Subsingleton (LieSubalgebra R (⊥ : LieSubalgebra R L
))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_of_bot_eq_top`：subsingleton_of_bot_eq_top (hα : (⊥ : α) = (
⊤ : α)) : Subsingleton α
· 使用定理 `LieSubalgebra.ext`：ext (L₁' L₂' : LieSubalgebra R L) (h : forall x, x in
 L₁' ↔ x in L₂') : L₁' = L₂'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubalgebra.mem_bot`：mem_bot (x : L) : x in (⊥ : LieSubalgebra R L) ↔ 
x = 0
-/
instance subsingleton_of_bot : Subsingleton (LieSubalgebra R (⊥ : LieSubalgebra R L)) := by
  apply subsingleton_of_bot_eq_top
  ext ⟨x, hx⟩; change x ∈ ⊥ at hx; rw [LieSubalgebra.mem_bot] at hx; subst hx
  simp only [mem_bot, mem_top, iff_true]
  rfl
/-
**LieSubalgebra.subsingleton_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：subsingleton_bot : Subsingleton (⊥ : LieSubalgebra R L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem subsingleton_bot : Subsingleton (⊥ : LieSubalgebra R L) :=
  show Subsingleton ((⊥ : LieSubalgebra R L) : Set L) by simp

variable {K K'} in
/-
**LieSubalgebra.disjoint_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：∀ {R : Type u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst
_2 : LieAlgebra R L]   {K K' : LieSubalgebra R L}, Disjoint K.toSubmodule K'.toS
ubmodule ↔ Disjoint K K'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma disjoint_toSubmodule :
    Disjoint (K : Submodule R L) (K' : Submodule R L) ↔ Disjoint K K' := by
  simp [disjoint_iff, ← toSubmodule_inj]

variable (R L)
/-
**LieSubalgebra.wellFoundedGT_of_noetherian** 是 Mathlib 中的一个实例，位于命名空间 `LieSubalg
ebra`。
形式化陈述：wellFoundedGT_of_noetherian [IsNoetherian R L] : WellFoundedGT (LieSubalge
bra R L)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHomClass.isWellFounded`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → 
Prop} {s : β → β → Prop} {F : Type u_5} [inst : FunLike F α β]   [RelHomClass F 
r s] (f : F) [I…
· 使用定理 `RelHom.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pro
p} {s : β → β → Prop}, RelHomClass (r →r s) r s
-/
instance wellFoundedGT_of_noetherian [IsNoetherian R L] : WellFoundedGT (LieSubalgebra R L) :=
  RelHomClass.isWellFounded (⟨toSubmodule, @fun _ _ h ↦ h⟩ : _ →r (· > ·))
/-
**LieSubalgebra.map_top** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：map_top : f.range = LieSubalgebra.map f ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.ext`：ext (L₁' L₂' : LieSubalgebra R L) (h : forall x, x in
 L₁' ↔ x in L₂') : L₁' = L₂'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_top : f.range = LieSubalgebra.map f ⊤ := by ext; simp

variable {R L K K' f}

section NestedSubalgebras

variable (h : K ≤ K')

/-- Given two nested Lie subalgebras `K ⊆ K'`, the inclusion `K ↪ K'` is a morphism of Lie
algebras. -/
/-
**LieSubalgebra.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `LieSubalgebra`。
形式化陈述：inclusion : K ->ₗ⁅R⁆ K'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two nested Lie subalgebras `K ⊆ K'`, the inclusion `K ↪ K'` is a morphism 
of Lie
algebras.
-/
def inclusion : K →ₗ⁅R⁆ K' :=
  { Submodule.inclusion h with map_lie' := @fun _ _ ↦ rfl }

@[simp]
/-
**LieSubalgebra.coe_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：coe_inclusion (x : K) : (inclusion h x : L) = x
参数：x : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inclusion (x : K) : (inclusion h x : L) = x :=
  rfl
/-
**LieSubalgebra.inclusion_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：inclusion_apply (x : K) : inclusion h x = ⟨x.1, h x.2⟩
参数：x : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusion_apply (x : K) : inclusion h x = ⟨x.1, h x.2⟩ :=
  rfl
/-
**LieSubalgebra.inclusion_injective** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：inclusion_injective : Function.Injective (inclusion h)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem inclusion_injective : Function.Injective (inclusion h) := fun x y ↦ by
  simp only [inclusion_apply, imp_self, Subtype.mk_eq_mk, SetLike.coe_eq_coe]

/-- Given two nested Lie subalgebras `K ⊆ K'`, we can view `K` as a Lie subalgebra of `K'`,
regarded as Lie algebra in its own right. -/
/-
**LieSubalgebra.ofLe** 是 Mathlib 中的一个定义，位于命名空间 `LieSubalgebra`。
形式化陈述：ofLe : LieSubalgebra R K'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two nested Lie subalgebras `K ⊆ K'`, we can view `K` as a Lie subalgebra o
f `K'`,
regarded as Lie algebra in its own right.
-/
def ofLe : LieSubalgebra R K' :=
  (inclusion h).range

@[simp]
/-
**LieSubalgebra.mem_ofLe** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：mem_ofLe (x : K') : x in ofLe h ↔ (x : L) in K
参数：x : K'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem mem_ofLe (x : K') : x ∈ ofLe h ↔ (x : L) ∈ K := by
  simp only [ofLe, inclusion_apply, LieHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro h
    use ⟨(x : L), h⟩
/-
**LieSubalgebra.ofLe_eq_comap_incl** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：ofLe_eq_comap_incl : ofLe h = K.comap K'.incl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.ext`：ext (L₁' L₂' : LieSubalgebra R L) (h : forall x, x in
 L₁' ↔ x in L₂') : L₁' = L₂'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubalgebra.mem_ofLe`：mem_ofLe (x : K') : x in ofLe h ↔ (x : L) in K
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofLe_eq_comap_incl : ofLe h = K.comap K'.incl := by
  ext
  rw [mem_ofLe]
  rfl

@[simp]
/-
**LieSubalgebra.coe_ofLe** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：coe_ofLe : (ofLe h : Submodule R K') = LinearMap.range (Submodule.inclusio
n h)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofLe : (ofLe h : Submodule R K') = LinearMap.range (Submodule.inclusion h) :=
  rfl

/-- Given nested Lie subalgebras `K ⊆ K'`, there is a natural equivalence from `K` to its image in
`K'`. -/
/-
**LieSubalgebra.equivOfLe** 是 Mathlib 中的一个定义，位于命名空间 `LieSubalgebra`。
形式化陈述：equivOfLe : K ≃ₗ⁅R⁆ ofLe h
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.inclusion_injective`：inclusion_injective : Function.Inject
ive (inclusion h)

--- 原说明 ---
Given nested Lie subalgebras `K ⊆ K'`, there is a natural equivalence from `K` t
o its image in
`K'`.
-/
noncomputable def equivOfLe : K ≃ₗ⁅R⁆ ofLe h :=
  (inclusion h).equivRangeOfInjective (inclusion_injective h)

@[simp]
/-
**LieSubalgebra.equivOfLe_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：equivOfLe_apply (x : K) : equivOfLe h x = ⟨inclusion h x, (inclusion h).me
m_range_self x⟩
参数：x : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivOfLe_apply (x : K) : equivOfLe h x = ⟨inclusion h x, (inclusion h).mem_range_self x⟩ :=
  rfl

end NestedSubalgebras

/-
**LieSubalgebra.map_le_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：map_le_iff_le_comap {K : LieSubalgebra R L} {K' : LieSubalgebra R L₂} : ma
p f K <= K' ↔ K <= comap f K'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_le_iff_le_comap {K : LieSubalgebra R L} {K' : LieSubalgebra R L₂} :
    map f K ≤ K' ↔ K ≤ comap f K' :=
  Set.image_subset_iff
/-
**LieSubalgebra.gc_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：gc_map_comap : GaloisConnection (map f) (comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.map_le_iff_le_comap`：map_le_iff_le_comap {K : LieSubalgebr
a R L} {K' : LieSubalgebra R L₂} : map f K <= K' ↔ K <= comap f K'
-/
theorem gc_map_comap : GaloisConnection (map f) (comap f) := fun _ _ ↦ map_le_iff_le_comap

end LatticeStructure

section LieSpan

variable (R L) (s : Set L)

/-- The Lie subalgebra of a Lie algebra `L` generated by a subset `s ⊆ L`. -/
/-
**LieSubalgebra.lieSpan** 是 Mathlib 中的一个定义，位于命名空间 `LieSubalgebra`。
形式化陈述：lieSpan : LieSubalgebra R L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Lie subalgebra of a Lie algebra `L` generated by a subset `s ⊆ L`.
-/
def lieSpan : LieSubalgebra R L :=
  sInf { N | s ⊆ N }

variable {R L s}
/-
**LieSubalgebra.mem_lieSpan** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：mem_lieSpan {x : L} : x in lieSpan R L s ↔ forall K : LieSubalgebra R L, s
 subseteq K -> x in K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `LieSubalgebra.lieSpan.eq_1`：∀ (R : Type u) (L : Type v) [inst : CommRing
 R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (s : Set L),   LieSubalgebra.
lieSpan R L s = …
· 使用定理 `LieSubalgebra.coe_sInf`：coe_sInf (S : Set (LieSubalgebra R L)) : (↑(sInf
 S) : Set L) = ⋂ s in S, (s : Set L)
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
-/
theorem mem_lieSpan {x : L} : x ∈ lieSpan R L s ↔ ∀ K : LieSubalgebra R L, s ⊆ K → x ∈ K := by
  rw [← SetLike.mem_coe, lieSpan, coe_sInf]
  exact Set.mem_iInter₂
/-
**LieSubalgebra.subset_lieSpan** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：subset_lieSpan : s subseteq lieSpan R L s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `LieSubalgebra.mem_lieSpan`：mem_lieSpan {x : L} : x in lieSpan R L s ↔ fo
rall K : LieSubalgebra R L, s subseteq K -> x in K
-/
theorem subset_lieSpan : s ⊆ lieSpan R L s := by
  intro m hm
  rw [SetLike.mem_coe, mem_lieSpan]
  intro K hK
  exact hK hm
/-
**LieSubalgebra.submodule_span_le_lieSpan** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgeb
ra`。
形式化陈述：submodule_span_le_lieSpan : Submodule.span R s <= lieSpan R L s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `LieSubalgebra.coe_toSubmodule`：coe_toSubmodule : ((L' : Submodule R L) :
 Set L) = L'
· 使用定理 `LieSubalgebra.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
-/
theorem submodule_span_le_lieSpan : Submodule.span R s ≤ lieSpan R L s := by
  rw [Submodule.span_le, coe_toSubmodule]
  apply subset_lieSpan
/-
**LieSubalgebra.lieSpan_le** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：lieSpan_le {K} : lieSpan R L s <= K ↔ s subseteq K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `LieSubalgebra.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubalgebra.mem_lieSpan`：mem_lieSpan {x : L} : x in lieSpan R L s ↔ fo
rall K : LieSubalgebra R L, s subseteq K -> x in K
-/
theorem lieSpan_le {K} : lieSpan R L s ≤ K ↔ s ⊆ K := by
  constructor
  · exact Set.Subset.trans subset_lieSpan
  · intro hs m hm
    rw [mem_lieSpan] at hm
    exact hm _ hs
/-
**LieSubalgebra.lieSpan_mono** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：lieSpan_mono {t : Set L} (h : s subseteq t) : lieSpan R L s <= lieSpan R L
 t
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubalgebra.lieSpan_le`：lieSpan_le {K} : lieSpan R L s <= K ↔ s subset
eq K
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `LieSubalgebra.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
-/
theorem lieSpan_mono {t : Set L} (h : s ⊆ t) : lieSpan R L s ≤ lieSpan R L t := by
  rw [lieSpan_le]
  exact Set.Subset.trans h subset_lieSpan
/-
**LieSubalgebra.lieSpan_eq** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：lieSpan_eq : lieSpan R L (K : Set L) = K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieSubalgebra.lieSpan_le`：lieSpan_le {K} : lieSpan R L s <= K ↔ s subset
eq K
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `LieSubalgebra.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
-/
theorem lieSpan_eq : lieSpan R L (K : Set L) = K :=
  le_antisymm (lieSpan_le.mpr rfl.subset) subset_lieSpan
/-
**LieSubalgebra.coe_lieSpan_submodule_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieSubal
gebra`。
形式化陈述：coe_lieSpan_submodule_eq_iff {p : Submodule R L} : (lieSpan R L (p : Set L
) : Submodule R L) = p ↔ exists K : LieSubalgebra R L, ↑K = p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.exists_lieSubalgebra_coe_eq_iff`：Submodule.exists_lieSubalgebr
a_coe_eq_iff (p : Submodule R L) : (exists K : LieSubalgebra R L, ↑K = p) ↔ fora
ll x y : L, x in p -> y in p ->…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubalgebra.mem_toSubmodule`：mem_toSubmodule {x : L} : x in (L' : Subm
odule R L) ↔ x in L'
· 使用定理 `LieSubalgebra.lie_mem`：lie_mem {x y : L} (hx : x in L') (hy : y in L') :
 (⁅x, y⁆ : L) in L'
· 使用定理 `LieSubalgebra.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
· 使用定理 `LieSubalgebra.toSubmodule_mk`：toSubmodule_mk (p : Submodule R L) (h) : (
({ p with lie_mem'
· 使用定理 `LieSubalgebra.coe_toSubmodule`：coe_toSubmodule : ((L' : Submodule R L) :
 Set L) = L'
· 使用定理 `LieSubalgebra.toSubmodule_inj`：toSubmodule_inj (L₁' L₂' : LieSubalgebra 
R L) : (L₁' : Submodule R L) = (L₂' : Submodule R L) ↔ L₁' = L₂'
· 使用定理 `LieSubalgebra.lieSpan_eq`：lieSpan_eq : lieSpan R L (K : Set L) = K
-/
theorem coe_lieSpan_submodule_eq_iff {p : Submodule R L} :
    (lieSpan R L (p : Set L) : Submodule R L) = p ↔ ∃ K : LieSubalgebra R L, ↑K = p := by
  rw [p.exists_lieSubalgebra_coe_eq_iff]; constructor <;> intro h
  · intro x m hm
    rw [← h, mem_toSubmodule]
    exact lie_mem _ (subset_lieSpan hm)
  · rw [← toSubmodule_mk p @h, coe_toSubmodule, toSubmodule_inj, lieSpan_eq]

open Submodule in
/-
**LieSubalgebra.coe_lieSpan_eq_span_of_forall_lie_eq_zero** 是 Mathlib 中的一个定理，位于命
名空间 `LieSubalgebra`。
形式化陈述：coe_lieSpan_eq_span_of_forall_lie_eq_zero {s : Set L} (hs : forallᵉ (x in 
s) (y in s), ⁅x, y⁆ = 0) : lieSpan R L s = span R s
参数：hs : forallᵉ (x in s) (y in s), ⁅x, y⁆ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_induction₂`：span_induction₂ {N : Type*} [AddCommMonoid N]
 [Module R N] {t : Set N} {p : (x : M) -> (y : N) -> x in span R s -> y in span 
R t -> Prop} (m…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `zero_lie`：zero_lie : ⁅(0 : L), m⁆ = 0
· 使用定理 `lie_zero`：lie_zero : ⁅x, 0⁆ = (0 : M)
· 使用定理 `add_lie`：add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `lie_add`：lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
· 使用定理 `smul_lie`：smul_lie : ⁅t • x, m⁆ = t • ⁅x, m⁆
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `lie_smul`：lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LieSubalgebra.lieSpan_le`：lieSpan_le {K} : lieSpan R L s <= K ↔ s subset
eq K
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `LieSubalgebra.submodule_span_le_lieSpan`：submodule_span_le_lieSpan : Sub
module.span R s <= lieSpan R L s
-/
theorem coe_lieSpan_eq_span_of_forall_lie_eq_zero
    {s : Set L} (hs : ∀ᵉ (x ∈ s) (y ∈ s), ⁅x, y⁆ = 0) :
    lieSpan R L s = span R s := by
  suffices ∀ {x y}, x ∈ span R s → y ∈ span R s → ⁅x, y⁆ ∈ span R s by
    refine le_antisymm ?_ submodule_span_le_lieSpan
    change _ ≤ ({ span R s with lie_mem' := this } : LieSubalgebra R L)
    rw [lieSpan_le]
    exact subset_span
  intro x y hx hy
  induction hx, hy using span_induction₂ with
  | mem_mem x y hx hy => simp [hs x hx y hy]
  | zero_left y hy => simp
  | zero_right x hx => simp
  | add_left x y z _ _ _ hx hy => simp [add_mem hx hy]
  | add_right x y z _ _ _ hx hy => simp [add_mem hx hy]
  | smul_left r x y _ _ h => simp [smul_mem _ r h]
  | smul_right r x y _ _ h => simp [smul_mem _ r h]
/-
**LieSubalgebra.map_lieSpan** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：map_lieSpan : (lieSpan R L s).map f = lieSpan R L₂ (f '' s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubalgebra.map_le_iff_le_comap`：map_le_iff_le_comap {K : LieSubalgebr
a R L} {K' : LieSubalgebra R L₂} : map f K <= K' ↔ K <= comap f K'
· 使用定理 `LieSubalgebra.lieSpan_le`：lieSpan_le {K} : lieSpan R L s <= K ↔ s subset
eq K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `LieSubalgebra.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem map_lieSpan :
    (lieSpan R L s).map f = lieSpan R L₂ (f '' s) := by
  refine le_antisymm ?_ (lieSpan_le.mpr <| Set.image_mono subset_lieSpan)
  rw [map_le_iff_le_comap, lieSpan_le]
  change s ⊆ f ⁻¹' (lieSpan R L₂ (f '' s))
  exact image_subset_iff.mp <| subset_lieSpan

variable (R L)

/-- `lieSpan` forms a Galois insertion with the coercion from `LieSubalgebra` to `Set`. -/
/-
**LieSubalgebra.gi** 是 Mathlib 中的一个定义，位于命名空间 `LieSubalgebra`。
形式化陈述：(R : Type u) →   (L : Type v) →     [inst : CommRing R] →       [inst_1 : 
LieRing L] → [inst_2 : LieAlgebra R L] → GaloisInsertion (LieSubalgebra.lieSpan 
R L) SetLike.coe
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.lieSpan_le`：lieSpan_le {K} : lieSpan R L s <= K ↔ s subset
eq K

--- 原说明 ---
`lieSpan` forms a Galois insertion with the coercion from `LieSubalgebra` to `Se
t`.
-/
protected def gi : GaloisInsertion (lieSpan R L : Set L → LieSubalgebra R L) (↑) where
  choice s _ := lieSpan R L s
  gc _ _ := lieSpan_le
  le_l_u _ := subset_lieSpan
  choice_eq _ _ := rfl

@[simp]
/-
**LieSubalgebra.span_empty** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：span_empty : lieSpan R L (∅ : Set L) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem span_empty : lieSpan R L (∅ : Set L) = ⊥ :=
  (LieSubalgebra.gi R L).gc.l_bot

@[simp]
/-
**LieSubalgebra.span_univ** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：span_univ : lieSpan R L (Set.univ : Set L) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `LieSubalgebra.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
-/
theorem span_univ : lieSpan R L (Set.univ : Set L) = ⊤ :=
  eq_top_iff.2 <| SetLike.le_def.2 <| subset_lieSpan

variable {L}
/-
**LieSubalgebra.span_union** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：span_union (s t : Set L) : lieSpan R L (s union t) = lieSpan R L s ⊔ lieSp
an R L t
参数：s t : Set L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem span_union (s t : Set L) : lieSpan R L (s ∪ t) = lieSpan R L s ⊔ lieSpan R L t :=
  (LieSubalgebra.gi R L).gc.l_sup
/-
**LieSubalgebra.span_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：span_iUnion {ι} (s : ι -> Set L) : lieSpan R L (⋃ i, s i) = ⨆ i, lieSpan R
 L (s i)
参数：s : ι -> Set L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem span_iUnion {ι} (s : ι → Set L) : lieSpan R L (⋃ i, s i) = ⨆ i, lieSpan R L (s i) :=
  (LieSubalgebra.gi R L).gc.l_iSup

/-- An induction principle for span membership. If `p` holds for 0 and all elements of `s`, and is
preserved under addition, scalar multiplication and the Lie bracket, then `p` holds for all
elements of the Lie algebra spanned by `s`. -/
@[elab_as_elim]
/-
**LieSubalgebra.lieSpan_induction** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：lieSpan_induction {p : (x : L) -> x in lieSpan R L s -> Prop} (mem : foral
l (x) (h : x in s), p x (subset_lieSpan h)) (zero : p 0 (LieSubalgebra.zero_mem 
_)) (add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (LieSubalgebra.add_me
m _ ‹_› ‹_›)) (smul : forall (a : R) (x hx), p x hx -> p (a • x) (LieSubalgebra.
smul_mem _ _ ‹_›)) {x} (lie : forall x y hx hy, p x hx -> p y hy -> p (⁅x, y⁆) (
LieSubalgebra.lie_mem _ ‹_› ‹_›)) (hx : x in lieSpan R L s) : p x hx
参数：x : L；mem : forall (x) (h : x in s), p x (subset_lieSpan h)；zero : p 0 (LieSu
balgebra.zero_mem _)；add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (LieS
ubalgebra.add_mem _ ‹_› ‹_›)；smul : forall (a : R) (x hx), p x hx -> p (a • x) (
LieSubalgebra.smul_mem _ _ ‹_›)；lie : forall x y hx hy, p x hx -> p y hy -> p (⁅
x, y⁆) (LieSubalgebra.lie_mem _ ‹_› ‹_›)；hx : x in lieSpan R L s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
· 使用定理 `LieSubalgebra.zero_mem`：∀ {R : Type u} {L : Type v} [inst : CommRing R] 
[inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (L' : LieSubalgebra R L),   0 ∈ L
'
· 使用定理 `LieSubalgebra.add_mem`：∀ {R : Type u} {L : Type v} [inst : CommRing R] [
inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (L' : LieSubalgebra R L)   {x y : 
L}, x ∈ L' …
· 使用定理 `LieSubalgebra.smul_mem`：∀ {R : Type u} {L : Type v} [inst : CommRing R] 
[inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (L' : LieSubalgebra R L)   (t : R
) {x : L}, x…
· 使用定理 `LieSubalgebra.lie_mem`：lie_mem {x y : L} (hx : x in L') (hy : y in L') :
 (⁅x, y⁆ : L) in L'
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieSubalgebra.lieSpan_le`：lieSpan_le {K} : lieSpan R L s <= K ↔ s subset
eq K

--- 原说明 ---
An induction principle for span membership. If `p` holds for 0 and all elements 
of `s`, and is
preserved under addition, scalar multiplication and the Lie bracket, then `p` ho
lds for all
elements of the Lie algebra spanned by `s`.
-/
theorem lieSpan_induction {p : (x : L) → x ∈ lieSpan R L s → Prop}
    (mem : ∀ (x) (h : x ∈ s), p x (subset_lieSpan h))
    (zero : p 0 (LieSubalgebra.zero_mem _))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (LieSubalgebra.add_mem _ ‹_› ‹_›))
    (smul : ∀ (a : R) (x hx), p x hx → p (a • x) (LieSubalgebra.smul_mem _ _ ‹_›)) {x}
    (lie : ∀ x y hx hy, p x hx → p y hy → p (⁅x, y⁆) (LieSubalgebra.lie_mem _ ‹_› ‹_›))
    (hx : x ∈ lieSpan R L s) : p x hx := by
  let p : LieSubalgebra R L :=
    { carrier := { x | ∃ hx, p x hx }
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, add _ _ _ _ hpx hpy⟩
      zero_mem' := ⟨_, zero⟩
      smul_mem' := fun r ↦ fun ⟨_, hpx⟩ ↦ ⟨_, smul r _ _ hpx⟩
      lie_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, lie _ _ _ _ hpx hpy⟩ }
  exact lieSpan_le (K := p) |>.mpr (fun y hy ↦ ⟨subset_lieSpan hy, mem y hy⟩) hx |>.elim fun _ ↦ id
/-
**LieSubalgebra.lieSpan_neg** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：∀ (R : Type u) {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst
_2 : LieAlgebra R L] {s : Set L},   LieSubalgebra.lieSpan R L (-s) = LieSubalgeb
ra.lieSpan R L s
参数：R : Type u；-s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.lieSpan_induction`：lieSpan_induction {p : (x : L) -> x in 
lieSpan R L s -> Prop} (mem : forall (x) (h : x in s), p x (subset_lieSpan h)) (
zero : p 0 (LieSubalg…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neg_mem_iff`：∀ {S : Type u_3} {G : Type u_4} [inst : InvolutiveNeg G] {x
 : SetLike S G} [NegMemClass S G] {H : S} {x_1 : G},   -x_1 ∈ H ↔ x_1 ∈ H
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `LieSubalgebra.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
· 使用定理 `Set.mem_neg`：∀ {α : Type u_2} [inst : Neg α] {s : Set α} {a : α}, a ∈ -s
 ↔ -a ∈ s
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `LieSubalgebra.instSMulMemClass`：∀ (R : Type u) (L : Type v) [inst : Comm
Ring R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   SMulMemClass (LieSubal
gebra R L) R L
· 使用定理 `LieSubalgebra.lie_mem`：lie_mem {x y : L} (hx : x in L') (hy : y in L') :
 (⁅x, y⁆ : L) in L'
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
@[simp] lemma lieSpan_neg : lieSpan R L (-s) = lieSpan R L s := by
  suffices ∀ s : Set L, lieSpan R L (-s) ≤ lieSpan R L s from
    le_antisymm (this s) <| by simpa using (this (-s))
  intro s x hx
  induction hx using lieSpan_induction with
  | mem y h => exact neg_mem_iff.mp <| subset_lieSpan <| Set.mem_neg.mp h
  | zero => exact zero_mem _
  | add _ _ _ _ hu hv => exact add_mem hu hv
  | smul t _ _ hu => exact SMulMemClass.smul_mem t hu
  | lie _ _ _ _ hu hv => exact lie_mem _ hu hv

variable {R} in
/-
**LieSubalgebra.lieSpan_lieSpan_coe_preimage** 是 Mathlib 中的一个定理，位于命名空间 `LieSubal
gebra`。
形式化陈述：∀ {R : Type u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst
_2 : LieAlgebra R L] {s : Set L},   LieSubalgebra.lieSpan R (↥(LieSubalgebra.lie
Span R L s)) (Subtype.val ⁻¹' s) = ⊤
参数：↥(LieSubalgebra.lieSpan R L s)；Subtype.val ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `LieSubalgebra.lieSpan_induction`：lieSpan_induction {p : (x : L) -> x in 
lieSpan R L s -> Prop} (mem : forall (x) (h : x in s), p x (subset_lieSpan h)) (
zero : p 0 (LieSubalg…
· 使用定理 `LieSubalgebra.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `LieSubalgebra.smul_mem`：∀ {R : Type u} {L : Type v} [inst : CommRing R] 
[inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (L' : LieSubalgebra R L)   (t : R
) {x : L}, x…
· 使用定理 `LieSubalgebra.lie_mem`：lie_mem {x y : L} (hx : x in L') (hy : y in L') :
 (⁅x, y⁆ : L) in L'
-/
@[simp] lemma lieSpan_lieSpan_coe_preimage : lieSpan R _ (((↑) : lieSpan R L s → L) ⁻¹' s) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  induction hx using lieSpan_induction with
  | mem u hu => exact subset_lieSpan <| by simpa
  | zero => exact zero_mem _
  | add u v _ _ hu hv => revert hu hv; exact add_mem
  | smul t u _ hu => revert hu; exact LieSubalgebra.smul_mem _ _
  | lie u v _ _ hu hv => revert hu hv; exact LieSubalgebra.lie_mem _
/-
**LieSubalgebra.comap_lieSpan_range_eq** 是 Mathlib 中的一个引理，位于命名空间 `LieSubalgebra`
。
形式化陈述：comap_lieSpan_range_eq {ι : Type*} (f : ι -> K) : (lieSpan R L (range ((↑)
 ∘ f))).comap K.incl = lieSpan R K (range f)
参数：f : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LieSubalgebra.lieSpan_induction`：lieSpan_induction {p : (x : L) -> x in 
lieSpan R L s -> Prop} (mem : forall (x) (h : x in s), p x (subset_lieSpan h)) (
zero : p 0 (LieSubalg…
· 使用定理 `LieSubalgebra.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `LieSubalgebra.smul_mem`：∀ {R : Type u} {L : Type v} [inst : CommRing R] 
[inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (L' : LieSubalgebra R L)   (t : R
) {x : L}, x…
· 使用定理 `LieSubalgebra.lie_mem`：lie_mem {x y : L} (hx : x in L') (hy : y in L') :
 (⁅x, y⁆ : L) in L'
· 使用定理 `LieSubalgebra.lieSpan_le`：lieSpan_le {K} : lieSpan R L s <= K ↔ s subset
eq K
-/
lemma comap_lieSpan_range_eq {ι : Type*} (f : ι → K) :
    (lieSpan R L (range ((↑) ∘ f))).comap K.incl = lieSpan R K (range f) := by
  apply le_antisymm
  · intro ⟨x, hx⟩ hx'
    simp only [mem_comap, coe_incl] at hx'
    suffices x ∈ (lieSpan R K (range f)).map K.incl by aesop
    clear hx
    induction hx' using lieSpan_induction with
    | mem u hu =>
      have (i : ι) : f i ∈ lieSpan R K (range f) := subset_lieSpan <| mem_range_self i
      aesop
    | zero => exact zero_mem _
    | add u v _ _ hu hv => revert hu hv; exact add_mem
    | smul t u _ hu => revert hu; exact LieSubalgebra.smul_mem _ _
    | lie u v _ _ hu hv => revert hu hv; exact lie_mem _
  · rw [lieSpan_le]
    rintro - ⟨i, rfl⟩
    simp only [SetLike.mem_coe, mem_comap, coe_incl]
    exact subset_lieSpan <| by simp

end LieSpan

end LieSubalgebra

end LieSubalgebra

namespace LieEquiv

variable {R : Type u} {L₁ : Type v} {L₂ : Type w}
variable [CommRing R] [LieRing L₁] [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂]

/-- An injective Lie algebra morphism is an equivalence onto its range. -/
/-
**LieEquiv.ofInjective** 是 Mathlib 中的一个定义，位于命名空间 `LieEquiv`。
形式化陈述：ofInjective (f : L₁ ->ₗ⁅R⁆ L₂) (h : Function.Injective f) : L₁ ≃ₗ⁅R⁆ f.ran
ge
参数：f : L₁ ->ₗ⁅R⁆ L₂；h : Function.Injective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An injective Lie algebra morphism is an equivalence onto its range.
-/
noncomputable def ofInjective (f : L₁ →ₗ⁅R⁆ L₂) (h : Function.Injective f) : L₁ ≃ₗ⁅R⁆ f.range :=
  { LinearEquiv.ofInjective (f : L₁ →ₗ[R] L₂) <| by rwa [LieHom.coe_toLinearMap] with
    map_lie' {x y} := SetCoe.ext <| f.map_lie x y }

@[simp]
/-
**LieEquiv.ofInjective_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：ofInjective_apply (f : L₁ ->ₗ⁅R⁆ L₂) (h : Function.Injective f) (x : L₁) :
 ↑(ofInjective f h x) = f x
参数：f : L₁ ->ₗ⁅R⁆ L₂；h : Function.Injective f；x : L₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofInjective_apply (f : L₁ →ₗ⁅R⁆ L₂) (h : Function.Injective f) (x : L₁) :
    ↑(ofInjective f h x) = f x :=
  rfl

variable (L₁' L₁'' : LieSubalgebra R L₁) (L₂' : LieSubalgebra R L₂)

/-- Lie subalgebras that are equal as sets are equivalent as Lie algebras. -/
/-
**LieEquiv.ofEq** 是 Mathlib 中的一个定义，位于命名空间 `LieEquiv`。
形式化陈述：ofEq (h : (L₁' : Set L₁) = L₁'') : L₁' ≃ₗ⁅R⁆ L₁''
参数：h : (L₁' : Set L₁) = L₁''。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lie subalgebras that are equal as sets are equivalent as Lie algebras.
-/
def ofEq (h : (L₁' : Set L₁) = L₁'') : L₁' ≃ₗ⁅R⁆ L₁'' :=
  { LinearEquiv.ofEq (L₁' : Submodule R L₁) (L₁'' : Submodule R L₁) (by
      ext x
      change x ∈ (L₁' : Set L₁) ↔ x ∈ (L₁'' : Set L₁)
      rw [h]) with
    map_lie' {_ _} := rfl }

@[simp]
/-
**LieEquiv.ofEq_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：ofEq_apply (L L' : LieSubalgebra R L₁) (h : (L : Set L₁) = L') (x : L) : (
↑(ofEq L L' h x) : L₁) = x
参数：L L' : LieSubalgebra R L₁；h : (L : Set L₁) = L'；x : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofEq_apply (L L' : LieSubalgebra R L₁) (h : (L : Set L₁) = L') (x : L) :
    (↑(ofEq L L' h x) : L₁) = x :=
  rfl

variable (e : L₁ ≃ₗ⁅R⁆ L₂)

/-- An equivalence of Lie algebras restricts to an equivalence from any Lie subalgebra onto its
image. -/
/-
**LieEquiv.lieSubalgebraMap** 是 Mathlib 中的一个定义，位于命名空间 `LieEquiv`。
形式化陈述：lieSubalgebraMap : L₁'' ≃ₗ⁅R⁆ (L₁''.map e : LieSubalgebra R L₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of Lie algebras restricts to an equivalence from any Lie subalgeb
ra onto its
image.
-/
def lieSubalgebraMap : L₁'' ≃ₗ⁅R⁆ (L₁''.map e : LieSubalgebra R L₂) :=
  { LinearEquiv.submoduleMap (e : L₁ ≃ₗ[R] L₂) ↑L₁'' with
    map_lie' := @fun x y ↦ by
      apply SetCoe.ext
      exact LieHom.map_lie (↑e : L₁ →ₗ⁅R⁆ L₂) ↑x ↑y }

@[simp]
/-
**LieEquiv.lieSubalgebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：lieSubalgebraMap_apply (x : L₁'') : ↑(e.lieSubalgebraMap _ x) = e x
参数：x : L₁''。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lieSubalgebraMap_apply (x : L₁'') : ↑(e.lieSubalgebraMap _ x) = e x :=
  rfl

/-- An equivalence of Lie algebras restricts to an equivalence from any Lie subalgebra onto its
image. -/
/-
**LieEquiv.ofSubalgebras** 是 Mathlib 中的一个定义，位于命名空间 `LieEquiv`。
形式化陈述：ofSubalgebras (h : L₁'.map ↑e = L₂') : L₁' ≃ₗ⁅R⁆ L₂'
参数：h : L₁'.map ↑e = L₂'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of Lie algebras restricts to an equivalence from any Lie subalgeb
ra onto its
image.
-/
def ofSubalgebras (h : L₁'.map ↑e = L₂') : L₁' ≃ₗ⁅R⁆ L₂' :=
  { LinearEquiv.ofSubmodules (e : L₁ ≃ₗ[R] L₂) (↑L₁') (↑L₂') (by
      rw [← h]
      rfl) with
    map_lie' := @fun x y ↦ by
      apply SetCoe.ext
      exact LieHom.map_lie (↑e : L₁ →ₗ⁅R⁆ L₂) ↑x ↑y }

@[simp]
/-
**LieEquiv.ofSubalgebras_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：ofSubalgebras_apply (h : L₁'.map ↑e = L₂') (x : L₁') : ↑(e.ofSubalgebras _
 _ h x) = e x
参数：h : L₁'.map ↑e = L₂'；x : L₁'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSubalgebras_apply (h : L₁'.map ↑e = L₂') (x : L₁') : ↑(e.ofSubalgebras _ _ h x) = e x :=
  rfl

@[simp]
/-
**LieEquiv.ofSubalgebras_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：ofSubalgebras_symm_apply (h : L₁'.map ↑e = L₂') (x : L₂') : ↑((e.ofSubalge
bras _ _ h).symm x) = e.symm x
参数：h : L₁'.map ↑e = L₂'；x : L₂'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSubalgebras_symm_apply (h : L₁'.map ↑e = L₂') (x : L₂') :
    ↑((e.ofSubalgebras _ _ h).symm x) = e.symm x :=
  rfl

end LieEquiv

