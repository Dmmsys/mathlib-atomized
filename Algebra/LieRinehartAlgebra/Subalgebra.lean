/-
Copyright (c) 2026 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin
-/

module

public import Mathlib.Algebra.LieRinehartAlgebra.Defs

/-!
# Lie-Rinehart subalgebras

This file defines Lie-Rinehart subalgebras of a Lie-Rinehart algebra and provides basic related
definitions and results.

## Main definitions/ statements:

* `LieRinehartSubalgebra` as an `A`-submodule of `L` stable under the Lie bracket. (This is also
applicable to Lie-Rinehart rings and more generally any `A`-module with a Lie ring structure).

* A Lie-Rinehart subalgebra of a Lie-Rinehart ring is a Lie-Rinehart ring

* A Lie-Rinehart subalgebra of a Lie-Rinehart algebra is a Lie-Rinehart algebra over the same ring.

-/

public section

open scoped LieRinehartAlgebra

variable (A L : Type*) [CommRing A] [LieRing L] [Module A L]

/-- A Lie-Rinehart subalgebra of a Lie-Rinehart algebra `(R A L)` is an `A`-submodule of `L`, which
is stable under the Lie bracket. (This can be defined independently of `R` and most
Lie-Rinehart algebra axioms). -/
/-
**LieRinehartSubalgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u_1) → (L : Type u_2) → [inst : CommRing A] → [inst_1 : LieRing 
L] → [_root_.Module A L] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie-Rinehart subalgebra of a Lie-Rinehart algebra `(R A L)` is an `A`-submodul
e of `L`, which
is stable under the Lie bracket. (This can be defined independently of `R` and m
ost
Lie-Rinehart algebra axioms).
-/
structure LieRinehartSubalgebra extends Submodule A L where
  lie_mem' {a b} : a ∈ carrier → b ∈ carrier → ⁅a, b⁆ ∈ carrier
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (LieRinehartSubalgebra A L) :=
  ⟨⟨0, fun {x y hx _hy} ↦ by simp [(Submodule.mem_bot A).mp hx]⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (LieRinehartSubalgebra A L) :=
  ⟨0⟩

namespace LieRinehartSubalgebra

/-
**LieRinehartSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieRinehartSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (LieRinehartSubalgebra A L) L where
  coe L' := L'.carrier
  coe_injective L' L'' h := by
    rcases L'
    rcases L''
    congr
    exact SetLike.coe_injective h
/-
**LieRinehartSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieRinehartSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (LieRinehartSubalgebra A L) := .ofSetLike (LieRinehartSubalgebra A L) L
/-
**LieRinehartSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieRinehartSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddSubgroupClass (LieRinehartSubalgebra A L) L where
  add_mem := Submodule.add_mem _
  zero_mem L' := L'.zero_mem'
  neg_mem {L'} x hx := show -x ∈ L'.toSubmodule from neg_mem hx
/-
**LieRinehartSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieRinehartSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulMemClass (LieRinehartSubalgebra A L) A L where
  smul_mem {s} := SMulMemClass.smul_mem (s := s.toSubmodule)

/-- A Lie-Rinehart subalgebra forms a Lie ring. -/
/-
**LieRinehartSubalgebra.lieRing** 是 Mathlib 中的一个实例，位于命名空间 `LieRinehartSubalgebra
`。
形式化陈述：lieRing (L' : LieRinehartSubalgebra A L) : LieRing L' where bracket x y
参数：L' : LieRinehartSubalgebra A L。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieRinehartSubalgebra.instAddSubgroupClass`：∀ (A : Type u_1) (L : Type u
_2) [inst : CommRing A] [inst_1 : LieRing L] [inst_2 : _root_.Module A L],   Add
SubgroupClass (LieRinehartSubalg…

--- 原说明 ---
A Lie-Rinehart subalgebra forms a Lie ring.
-/
instance lieRing (L' : LieRinehartSubalgebra A L) : LieRing L' where
  bracket x y := ⟨⁅x.val, y.val⁆, L'.lie_mem' x.property y.property⟩
  lie_add x y z := by aesop
  add_lie x y z := by aesop
  lie_self x := by aesop
  leibniz_lie x y z := by aesop

variable {A L}
variable (L' : LieRinehartSubalgebra A L)
/-
**LieRinehartSubalgebra.zero_mem** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartSubalgebr
a`。
形式化陈述：∀ {A : Type u_1} {L : Type u_2} [inst : CommRing A] [inst_1 : LieRing L] [
inst_2 : _root_.Module A L]   (L' : LieRinehartSubalgebra A L), 0 ∈ L'
参数：L' : LieRinehartSubalgebra A L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieRinehartSubalgebra.instAddSubgroupClass`：∀ (A : Type u_1) (L : Type u
_2) [inst : CommRing A] [inst_1 : LieRing L] [inst_2 : _root_.Module A L],   Add
SubgroupClass (LieRinehartSubalg…
-/
protected theorem zero_mem : (0 : L) ∈ L' :=
  zero_mem L'
/-
**LieRinehartSubalgebra.add_mem** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartSubalgebra
`。
形式化陈述：∀ {A : Type u_1} {L : Type u_2} [inst : CommRing A] [inst_1 : LieRing L] [
inst_2 : _root_.Module A L]   (L' : LieRinehartSubalgebra A L) {x y : L}, x ∈ L'
 → y ∈ L' → x + y ∈ L'
参数：L' : LieRinehartSubalgebra A L。
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
· 使用定理 `LieRinehartSubalgebra.instAddSubgroupClass`：∀ (A : Type u_1) (L : Type u
_2) [inst : CommRing A] [inst_1 : LieRing L] [inst_2 : _root_.Module A L],   Add
SubgroupClass (LieRinehartSubalg…
-/
protected theorem add_mem {x y : L} : x ∈ L' → y ∈ L' → (x + y : L) ∈ L' :=
  add_mem
/-
**LieRinehartSubalgebra.sub_mem** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartSubalgebra
`。
形式化陈述：∀ {A : Type u_1} {L : Type u_2} [inst : CommRing A] [inst_1 : LieRing L] [
inst_2 : _root_.Module A L]   (L' : LieRinehartSubalgebra A L) {x y : L}, x ∈ L'
 → y ∈ L' → x - y ∈ L'
参数：L' : LieRinehartSubalgebra A L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
· 使用定理 `LieRinehartSubalgebra.instAddSubgroupClass`：∀ (A : Type u_1) (L : Type u
_2) [inst : CommRing A] [inst_1 : LieRing L] [inst_2 : _root_.Module A L],   Add
SubgroupClass (LieRinehartSubalg…
-/
protected theorem sub_mem {x y : L} : x ∈ L' → y ∈ L' → (x - y : L) ∈ L' :=
  sub_mem
/-
**LieRinehartSubalgebra.smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartSubalgebr
a`。
形式化陈述：∀ {A : Type u_1} {L : Type u_2} [inst : CommRing A] [inst_1 : LieRing L] [
inst_2 : _root_.Module A L]   (L' : LieRinehartSubalgebra A L) (t : A) {x : L}, 
x ∈ L' → t • x ∈ L'
参数：L' : LieRinehartSubalgebra A L；t : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `LieRinehartSubalgebra.instSMulMemClass`：∀ (A : Type u_1) (L : Type u_2) 
[inst : CommRing A] [inst_1 : LieRing L] [inst_2 : _root_.Module A L],   SMulMem
Class (LieRinehartSubalgebra…
-/
protected theorem smul_mem (t : A) {x : L} (h : x ∈ L') : t • x ∈ L' :=
  SMulMemClass.smul_mem _ h
/-
**LieRinehartSubalgebra.lie_mem** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartSubalgebra
`。
形式化陈述：lie_mem {x y : L} (hx : x in L') (hy : y in L') : (⁅x, y⁆ : L) in L'
参数：hx : x in L'；hy : y in L'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieRinehartSubalgebra.lie_mem'`：∀ {A : Type u_1} {L : Type u_2} [inst : 
CommRing A] [inst_1 : LieRing L] [inst_2 : _root_.Module A L]   (self : LieRineh
artSubalgebra A L) {…
-/
theorem lie_mem {x y : L} (hx : x ∈ L') (hy : y ∈ L') : (⁅x, y⁆ : L) ∈ L' :=
  L'.lie_mem' hx hy
/-
**LieRinehartSubalgebra.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartSubalg
ebra`。
形式化陈述：mem_carrier {x : L} : x in L'.carrier ↔ x in (L' : Set L)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier {x : L} : x ∈ L'.carrier ↔ x ∈ (L' : Set L) :=
  Iff.rfl
/-
**LieRinehartSubalgebra.mem_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartSubalge
bra`。
形式化陈述：mem_mk_iff (S : Set L) (h₁ h₂ h₃ h₄) {x : L} : x in (⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩,
 h₄⟩ : LieRinehartSubalgebra A L) ↔ x in S
参数：S : Set L；h₁ h₂ h₃ h₄。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk_iff (S : Set L) (h₁ h₂ h₃ h₄) {x : L} :
    x ∈ (⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieRinehartSubalgebra A L) ↔ x ∈ S :=
  Iff.rfl

@[simp]
/-
**LieRinehartSubalgebra.mem_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartSu
balgebra`。
形式化陈述：mem_toSubmodule {x : L} : x in L'.toSubmodule ↔ x in L'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toSubmodule {x : L} : x ∈ L'.toSubmodule ↔ x ∈ L' :=
  Iff.rfl

@[simp]
/-
**LieRinehartSubalgebra.mem_mk_iff'** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartSubalg
ebra`。
形式化陈述：mem_mk_iff' (p : Submodule A L) (h) {x : L} : x in (⟨p, h⟩ : LieRinehartSu
balgebra A L) ↔ x in p
参数：p : Submodule A L；h。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk_iff' (p : Submodule A L) (h) {x : L} :
    x ∈ (⟨p, h⟩ : LieRinehartSubalgebra A L) ↔ x ∈ p :=
  Iff.rfl
/-
**LieRinehartSubalgebra.mem_coe** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartSubalgebra
`。
形式化陈述：mem_coe {x : L} : x in (L' : Set L) ↔ x in L'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_coe {x : L} : x ∈ (L' : Set L) ↔ x ∈ L' :=
  Iff.rfl

@[simp, norm_cast]
/-
**LieRinehartSubalgebra.coe_bracket** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartSubalg
ebra`。
形式化陈述：coe_bracket (x y : L') : (↑⁅x, y⁆ : L) = ⁅(↑x : L), ↑y⁆
参数：x y : L'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bracket (x y : L') : (↑⁅x, y⁆ : L) = ⁅(↑x : L), ↑y⁆ :=
  rfl
/-
**LieRinehartSubalgebra.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartSubalgebra
`。
形式化陈述：ext_iff (x y : L') : x = y ↔ (x : L) = y
参数：x y : L'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem ext_iff (x y : L') : x = y ↔ (x : L) = y := Subtype.ext_iff
/-
**LieRinehartSubalgebra.coe_zero_iff_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehart
Subalgebra`。
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
· 使用定理 `LieRinehartSubalgebra.instAddSubgroupClass`：∀ (A : Type u_1) (L : Type u
_2) [inst : CommRing A] [inst_1 : LieRing L] [inst_2 : _root_.Module A L],   Add
SubgroupClass (LieRinehartSubalg…
· 使用定理 `LieRinehartSubalgebra.ext_iff`：ext_iff (x y : L') : x = y ↔ (x : L) = y
-/
theorem coe_zero_iff_zero (x : L') : (x : L) = 0 ↔ x = 0 := (ext_iff L' x 0).symm

@[ext]
/-
**LieRinehartSubalgebra.ext** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartSubalgebra`。
形式化陈述：ext (L₁' L₂' : LieRinehartSubalgebra A L) (h : forall x, x in L₁' ↔ x in L
₂') : L₁' = L₂'
参数：L₁' L₂' : LieRinehartSubalgebra A L；h : forall x, x in L₁' ↔ x in L₂'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
theorem ext (L₁' L₂' : LieRinehartSubalgebra A L) (h : ∀ x, x ∈ L₁' ↔ x ∈ L₂') : L₁' = L₂' :=
  SetLike.ext h
/-
**LieRinehartSubalgebra.ext_iff'** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartSubalgebr
a`。
形式化陈述：ext_iff' (L₁' L₂' : LieRinehartSubalgebra A L) : L₁' = L₂' ↔ forall x, x i
n L₁' ↔ x in L₂'
参数：L₁' L₂' : LieRinehartSubalgebra A L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
-/
theorem ext_iff' (L₁' L₂' : LieRinehartSubalgebra A L) : L₁' = L₂' ↔ ∀ x, x ∈ L₁' ↔ x ∈ L₂' :=
  SetLike.ext_iff

@[simp]
/-
**LieRinehartSubalgebra.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartSubalgebra`
。
形式化陈述：mk_coe (S : Set L) (h₁ h₂ h₃ h₄) : ((⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieRineha
rtSubalgebra A L) : Set L) = S
参数：S : Set L；h₁ h₂ h₃ h₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_coe (S : Set L) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieRinehartSubalgebra A L) : Set L) = S :=
  rfl
/-
**LieRinehartSubalgebra.toSubmodule_mk** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartSub
algebra`。
形式化陈述：toSubmodule_mk (p : Submodule A L) (h) : ({ p with lie_mem'
参数：p : Submodule A L；h。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubmodule_mk (p : Submodule A L) (h) :
    ({ p with lie_mem' := h } : LieRinehartSubalgebra A L).toSubmodule = p := rfl
/-
**LieRinehartSubalgebra.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartSuba
lgebra`。
形式化陈述：coe_injective : Function.Injective ((↑) : LieRinehartSubalgebra A L -> Set
 L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem coe_injective : Function.Injective ((↑) : LieRinehartSubalgebra A L → Set L) :=
  SetLike.coe_injective

@[norm_cast]
/-
**LieRinehartSubalgebra.coe_set_eq** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartSubalge
bra`。
形式化陈述：coe_set_eq (L₁' L₂' : LieRinehartSubalgebra A L) : (L₁' : Set L) = L₂' ↔ L
₁' = L₂'
参数：L₁' L₂' : LieRinehartSubalgebra A L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_set_eq`：coe_set_eq : (p : Set B) = q ↔ p = q
-/
theorem coe_set_eq (L₁' L₂' : LieRinehartSubalgebra A L) : (L₁' : Set L) = L₂' ↔ L₁' = L₂' :=
  SetLike.coe_set_eq
/-
**LieRinehartSubalgebra.toSubmodule_injective** 是 Mathlib 中的一个定理，位于命名空间 `LieRine
hartSubalgebra`。
形式化陈述：toSubmodule_injective : Function.Injective (toSubmodule (A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieRinehartSubalgebra.coe_set_eq`：coe_set_eq (L₁' L₂' : LieRinehartSubal
gebra A L) : (L₁' : Set L) = L₂' ↔ L₁' = L₂'
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
-/
theorem toSubmodule_injective : Function.Injective (toSubmodule (A := A) (L := L)) := by
  intro L₁' L₂' h
  rw [SetLike.ext'_iff] at h
  rw [← coe_set_eq]
  exact h
/-
**LieRinehartSubalgebra.coe_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartSu
balgebra`。
形式化陈述：coe_toSubmodule : (L'.toSubmodule : Set L) = L'
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSubmodule : (L'.toSubmodule : Set L) = L' :=
  rfl

section LieModule

variable {M : Type*} [AddCommGroup M] [LieRingModule L M]

/-
**LieRinehartSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieRinehartSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bracket L' M where
  bracket x m := ⁅(x : L), m⁆

@[simp]
/-
**LieRinehartSubalgebra.coe_bracket_of_module** 是 Mathlib 中的一个定理，位于命名空间 `LieRine
hartSubalgebra`。
形式化陈述：coe_bracket_of_module (x : L') (m : M) : ⁅x, m⁆ = ⁅(x : L), m⁆
参数：x : L'；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bracket_of_module (x : L') (m : M) : ⁅x, m⁆ = ⁅(x : L), m⁆ :=
  rfl
/-
**LieRinehartSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieRinehartSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLieTower L' L M where
  leibniz_lie x y m := leibniz_lie x.val y m

/-- Given a Lie-Rinehart algebra `L` containing a LieRinehart subalgebra `L' ⊆ L`, together with a
Lie ring module `M` of `L`, we may regard `M` as a Lie ring module of `L'` by restriction. -/
/-
**LieRinehartSubalgebra.lieRingModule** 是 Mathlib 中的一个实例，位于命名空间 `LieRinehartSuba
lgebra`。
形式化陈述：lieRingModule : LieRingModule L' M where add_lie x y m
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a Lie-Rinehart algebra `L` containing a LieRinehart subalgebra `L' ⊆ L`, t
ogether with a
Lie ring module `M` of `L`, we may regard `M` as a Lie ring module of `L'` by re
striction.
-/
instance lieRingModule : LieRingModule L' M where
  add_lie x y m := add_lie (x : L) y m
  lie_add x y m := lie_add (x : L) y m
  leibniz_lie x y m := leibniz_lie x (y : L) m

end LieModule

variable [LieRingModule L A] [LieRinehartRing A L]

/-- A Lie-Rinehart subalgebra of a Lie-Rinehart ring forms a new Lie-Rinehart ring. -/
/-
**LieRinehartSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieRinehartSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie-Rinehart subalgebra of a Lie-Rinehart ring forms a new Lie-Rinehart ring.
-/
instance : LieRinehartRing A L' where
  lie_smul_eq_mul' a b x := LieRinehartRing.lie_smul_eq_mul a b (x : L)
  leibniz_mul_right' x a b := LieRinehartRing.leibniz_mul_right (x : L) a b
  leibniz_smul_right' _ _ _ := by simp [ext_iff]

variable (R : Type*) [CommRing R] [Algebra R A] [LieAlgebra R L] [LieRinehartAlgebra R A L]

/-- A Lie-Rinehart subalgebra of a Lie-Rinehart algebra forms a Lie algebra. -/
/-
**LieRinehartSubalgebra.lieAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `LieRinehartSubalge
bra`。
形式化陈述：lieAlgebra : LieAlgebra R L' where lie_smul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieRinehartAlgebra.toIsScalarTower`：∀ {R : Type u_1} {A : Type u_2} {L :
 Type u_3} {inst : CommRing A} {inst_1 : LieRing L} {inst_2 : _root_.Module A L}
   {inst_3 : LieRingModu…
· 使用定理 `LieRinehartSubalgebra.instSMulMemClass`：∀ (A : Type u_1) (L : Type u_2) 
[inst : CommRing A] [inst_1 : LieRing L] [inst_2 : _root_.Module A L],   SMulMem
Class (LieRinehartSubalgebra…

--- 原说明 ---
A Lie-Rinehart subalgebra of a Lie-Rinehart algebra forms a Lie algebra.
-/
instance lieAlgebra : LieAlgebra R L' where
  lie_smul := by aesop

/-- Converts a Lie-Rinehart subalgebra to the corresponding Lie subalgebra. -/
/-
**LieRinehartSubalgebra.toLieSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 `LieRinehartSu
balgebra`。
形式化陈述：{A : Type u_1} →   {L : Type u_2} →     [inst : CommRing A] →       [inst_
1 : LieRing L] →         [inst_2 : _root_.Module A L] →           LieRinehartSub
algebra A L →             [inst_3 : LieRingModule L A] →               [inst_4 :
 LieRinehartRing A L] →                 (R : Type u_3) →                   [inst
_5 : CommRing R] →                     [inst_6 : Algebra R A] → [inst_7 : LieAlg
ebra R L] → [LieRinehartAlgebra R A L] → LieSubalgebra R L
参数：R : Type u_3。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieRinehartAlgebra.toIsScalarTower`：∀ {R : Type u_1} {A : Type u_2} {L :
 Type u_3} {inst : CommRing A} {inst_1 : LieRing L} {inst_2 : _root_.Module A L}
   {inst_3 : LieRingModu…
· 使用定理 `LieRinehartSubalgebra.lie_mem'`：∀ {A : Type u_1} {L : Type u_2} [inst : 
CommRing A] [inst_1 : LieRing L] [inst_2 : _root_.Module A L]   (self : LieRineh
artSubalgebra A L) {…

--- 原说明 ---
Converts a Lie-Rinehart subalgebra to the corresponding Lie subalgebra.
-/
@[expose] def toLieSubalgebra : LieSubalgebra R L where
  toSubmodule := L'.toSubmodule.restrictScalars R
  lie_mem' := L'.lie_mem'
/-
**LieRinehartSubalgebra.toLieSubalgebra_injective** 是 Mathlib 中的一个定理，位于命名空间 `Lie
RinehartSubalgebra`。
形式化陈述：toLieSubalgebra_injective : Function.Injective (fun L' => L'.toLieSubalgeb
ra R : LieRinehartSubalgebra A L -> LieSubalgebra R L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieRinehartSubalgebra.coe_set_eq`：coe_set_eq (L₁' L₂' : LieRinehartSubal
gebra A L) : (L₁' : Set L) = L₂' ↔ L₁' = L₂'
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
-/
theorem toLieSubalgebra_injective : Function.Injective (fun L' =>
    L'.toLieSubalgebra R : LieRinehartSubalgebra A L → LieSubalgebra R L) :=  fun L₁' L₂' h ↦ by
  rw [SetLike.ext'_iff] at h
  rw [← coe_set_eq]
  exact h

@[simp]
/-
**LieRinehartSubalgebra.toLieSubalgebra_inj** 是 Mathlib 中的一个定理，位于命名空间 `LieRineha
rtSubalgebra`。
形式化陈述：toLieSubalgebra_inj (L₁' L₂' : LieRinehartSubalgebra A L) : (L₁'.toLieSuba
lgebra R) = (L₂'.toLieSubalgebra R) ↔ L₁' = L₂'
参数：L₁' L₂' : LieRinehartSubalgebra A L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LieRinehartSubalgebra.toLieSubalgebra_injective`：toLieSubalgebra_injecti
ve : Function.Injective (fun L' => L'.toLieSubalgebra R : LieRinehartSubalgebra 
A L -> LieSubalgebra R L)
-/
theorem toLieSubalgebra_inj (L₁' L₂' : LieRinehartSubalgebra A L) :
    (L₁'.toLieSubalgebra R) = (L₂'.toLieSubalgebra R) ↔ L₁' = L₂' :=
  (toLieSubalgebra_injective R).eq_iff
/-
**LieRinehartSubalgebra.coe_toLieSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `LieRineha
rtSubalgebra`。
形式化陈述：coe_toLieSubalgebra : ((L'.toLieSubalgebra R) : Set L) = L'
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLieSubalgebra : ((L'.toLieSubalgebra R) : Set L) = L' := rfl

section LieModule

variable {M : Type*} [AddCommGroup M] [LieRingModule L M] [Module R M]

/-- Given a Lie-Rinehart algebra  `L` containing a LieRinehart subalgebra `L' ⊆ L`, together with a
Lie module `M` of `L`, we may regard `M` as a Lie module of `L'` by restriction. -/
/-
**LieRinehartSubalgebra.lieModule** 是 Mathlib 中的一个实例，位于命名空间 `LieRinehartSubalgeb
ra`。
形式化陈述：lieModule [LieModule R L M] : LieModule R L' M where smul_lie t x m
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieRinehartSubalgebra.coe_bracket_of_module`：coe_bracket_of_module (x : 
L') (m : M) : ⁅x, m⁆ = ⁅(x : L), m⁆
· 使用定理 `LieRinehartAlgebra.toIsScalarTower`：∀ {R : Type u_1} {A : Type u_2} {L :
 Type u_3} {inst : CommRing A} {inst_1 : LieRing L} {inst_2 : _root_.Module A L}
   {inst_3 : LieRingModu…
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
Given a Lie-Rinehart algebra  `L` containing a LieRinehart subalgebra `L' ⊆ L`, 
together with a
Lie module `M` of `L`, we may regard `M` as a Lie module of `L'` by restriction.
-/
instance lieModule [LieModule R L M] : LieModule R L' M where
  smul_lie t x m := by
    rw [coe_bracket_of_module, Submodule.coe_smul_of_tower, smul_lie, coe_bracket_of_module]
  lie_smul t x m := by simp only [coe_bracket_of_module, lie_smul]

end LieModule

/-- A Lie-Rinehart subalgebra forms a new Lie-Rinehart algebra. -/
/-
**LieRinehartSubalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieRinehartSubalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie-Rinehart subalgebra forms a new Lie-Rinehart algebra.
-/
instance : LieRinehartAlgebra R A L' where

/-- The embedding of a Lie-Rinehart subalgebra into the ambient space as a morphism of
Lie-Rinehart algebras. -/
/-
**LieRinehartSubalgebra.incl** 是 Mathlib 中的一个定义，位于命名空间 `LieRinehartSubalgebra`。
形式化陈述：{A : Type u_1} →   {L : Type u_2} →     [inst : CommRing A] →       [inst_
1 : LieRing L] →         [inst_2 : _root_.Module A L] →           (L' : LieRineh
artSubalgebra A L) →             [inst_3 : LieRingModule L A] →               [i
nst_4 : LieRinehartRing A L] →                 (R : Type u_3) →                 
  [inst_5 : CommRing R] →                     [inst_6 : Algebra R A] →          
             [inst_7 : LieAlgebra R L] →                         [inst_8 : LieRi
nehartAlgebra R A L] → LieRinehartAlgebra.Hom (AlgHom.id R A) (↥L') L
参数：L' : LieRinehartSubalgebra A L；R : Type u_3；AlgHom.id R A；↥L'。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieRinehartAlgebra.toIsScalarTower`：∀ {R : Type u_1} {A : Type u_2} {L :
 Type u_3} {inst : CommRing A} {inst_1 : LieRing L} {inst_2 : _root_.Module A L}
   {inst_3 : LieRingModu…
· 使用定理 `LieRinehartSubalgebra.instSMulMemClass`：∀ (A : Type u_1) (L : Type u_2) 
[inst : CommRing A] [inst_1 : LieRing L] [inst_2 : _root_.Module A L],   SMulMem
Class (LieRinehartSubalgebra…
· 使用定理 `LieRinehartSubalgebra.coe_bracket`：coe_bracket (x y : L') : (↑⁅x, y⁆ : L
) = ⁅(↑x : L), ↑y⁆

--- 原说明 ---
The embedding of a Lie-Rinehart subalgebra into the ambient space as a morphism 
of
Lie-Rinehart algebras.
-/
@[expose] def incl : L' →ₗ⁅(AlgHom.id R A)⁆ L where
  __ := L'.toSubmodule.subtype.restrictScalars R
  map_lie' {x y} := coe_bracket L' x y
  map_smul_apply' a x := L'.toSubmodule.subtype.map_smul a x
  apply_lie' a x := AlgHom.id_apply ⁅x, a⁆

@[simp]
/-
**LieRinehartSubalgebra.coe_incl** 是 Mathlib 中的一个定理，位于命名空间 `LieRinehartSubalgebr
a`。
形式化陈述：coe_incl : ⇑(L'.incl R) = ((↑) : L' -> L)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieRinehartSubalgebra.instAddSubgroupClass`：∀ (A : Type u_1) (L : Type u
_2) [inst : CommRing A] [inst_1 : LieRing L] [inst_2 : _root_.Module A L],   Add
SubgroupClass (LieRinehartSubalg…
· 使用定理 `LieRinehartSubalgebra.instSMulMemClass`：∀ (A : Type u_1) (L : Type u_2) 
[inst : CommRing A] [inst_1 : LieRing L] [inst_2 : _root_.Module A L],   SMulMem
Class (LieRinehartSubalgebra…
-/
theorem coe_incl : ⇑(L'.incl R) = ((↑) : L' → L) := rfl

end LieRinehartSubalgebra

