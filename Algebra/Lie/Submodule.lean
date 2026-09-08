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

/-- A Lie submodule of a Lie module is a submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie module. -/
/-
**LieSubmodule** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) →   (L : Type v) →     (M : Type w) →       [inst : CommRing 
R] →         [inst_1 : LieRing L] → [inst_2 : AddCommGroup M] → [_root_.Module R
 M] → [LieRingModule L M] → Type w
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie submodule of a Lie module is a submodule that is closed under the Lie brac
ket.
This is a sufficient condition for the subset itself to form a Lie module.
-/
structure LieSubmodule extends Submodule R M where
  lie_mem : ∀ {x : L} {m : M}, m ∈ carrier → ⁅x, m⁆ ∈ carrier

attribute [nolint docBlame] LieSubmodule.toSubmodule
attribute [coe] LieSubmodule.toSubmodule

namespace LieSubmodule

variable {R L M}
variable (N N' : LieSubmodule R L M)

/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (LieSubmodule R L M) M where
  coe s := s.carrier
  coe_injective N O h := by cases N; cases O; congr; exact SetLike.coe_injective h
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (LieSubmodule R L M) := .ofSetLike (LieSubmodule R L M) M
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddSubgroupClass (LieSubmodule R L M) M where
  add_mem {N} _ _ := N.add_mem'
  zero_mem N := N.zero_mem'
  neg_mem {N} x hx := show -x ∈ N.toSubmodule from neg_mem hx
/-
**LieSubmodule.instSMulMemClass** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
形式化陈述：instSMulMemClass : SMulMemClass (LieSubmodule R L M) R M where smul_mem {s
} c _ h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smul_mem'`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (self : Submodule R M) (c
 : R) {x …
-/
instance instSMulMemClass : SMulMemClass (LieSubmodule R L M) R M where
  smul_mem {s} c _ h := s.smul_mem' c h

/-- The zero module is a Lie submodule of any Lie module. -/
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The zero module is a Lie submodule of any Lie module.
-/
instance : Zero (LieSubmodule R L M) :=
  ⟨{ (0 : Submodule R M) with
      lie_mem := fun {x m} h ↦ by rw [(Submodule.mem_bot R).1 h]; apply lie_zero }⟩
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (LieSubmodule R L M) :=
  ⟨0⟩
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := mid) coeSubmodule : CoeOut (LieSubmodule R L M) (Submodule R M) :=
  ⟨toSubmodule⟩
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CanLift (Submodule R M) (LieSubmodule R L M) (·)
    (fun N ↦ ∀ {x : L} {m : M}, m ∈ N → ⁅x, m⁆ ∈ N) where
  prf N hN := ⟨⟨N, hN⟩, rfl⟩

@[norm_cast]
/-
**LieSubmodule.coe_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：coe_toSubmodule : ((N : Submodule R M) : Set M) = N
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSubmodule : ((N : Submodule R M) : Set M) = N :=
  rfl
/-
**LieSubmodule.mem_carrier** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：mem_carrier {x : M} : x in N.carrier ↔ x in (N : Set M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier {x : M} : x ∈ N.carrier ↔ x ∈ (N : Set M) :=
  Iff.rfl
/-
**LieSubmodule.mem_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：mem_mk_iff (S : Set M) (h₁ h₂ h₃ h₄) {x : M} : x in (⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩,
 h₄⟩ : LieSubmodule R L M) ↔ x in S
参数：S : Set M；h₁ h₂ h₃ h₄。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk_iff (S : Set M) (h₁ h₂ h₃ h₄) {x : M} :
    x ∈ (⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieSubmodule R L M) ↔ x ∈ S :=
  Iff.rfl

@[simp]
/-
**LieSubmodule.mem_mk_iff'** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：mem_mk_iff' (p : Submodule R M) (h) {x : M} : x in (⟨p, h⟩ : LieSubmodule 
R L M) ↔ x in p
参数：p : Submodule R M；h。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk_iff' (p : Submodule R M) (h) {x : M} :
    x ∈ (⟨p, h⟩ : LieSubmodule R L M) ↔ x ∈ p :=
  Iff.rfl

@[simp]
/-
**LieSubmodule.mem_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：mem_toSubmodule {x : M} : x in (N : Submodule R M) ↔ x in N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toSubmodule {x : M} : x ∈ (N : Submodule R M) ↔ x ∈ N :=
  Iff.rfl
/-
**LieSubmodule.mem_coe** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：mem_coe {x : M} : x in (N : Set M) ↔ x in N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_coe {x : M} : x ∈ (N : Set M) ↔ x ∈ N :=
  Iff.rfl
/-
**LieSubmodule.zero_mem** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：∀ {R : Type u} {L : Type v} {M : Type w} [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] [inst_4 : LieRi
ngModule L M] (N : LieSubmodule R L M), 0 ∈ N
参数：N : LieSubmodule R L M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
protected theorem zero_mem : (0 : M) ∈ N :=
  zero_mem N

@[simp]
/-
**LieSubmodule.mk_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：mk_eq_zero {x} (h : x in N) : (⟨x, h⟩ : N) = 0 ↔ x = 0
参数：h : x in N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
theorem mk_eq_zero {x} (h : x ∈ N) : (⟨x, h⟩ : N) = 0 ↔ x = 0 :=
  Subtype.ext_iff

@[simp]
/-
**LieSubmodule.coe_toSet_mk** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：coe_toSet_mk (S : Set M) (h₁ h₂ h₃ h₄) : ((⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : Lie
Submodule R L M) : Set M) = S
参数：S : Set M；h₁ h₂ h₃ h₄。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toSet_mk (S : Set M) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieSubmodule R L M) : Set M) = S :=
  rfl
/-
**LieSubmodule.toSubmodule_mk** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：toSubmodule_mk (p : Submodule R M) (h) : (({ p with lie_mem
参数：p : Submodule R M；h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem toSubmodule_mk (p : Submodule R M) (h) :
    (({ p with lie_mem := h } : LieSubmodule R L M) : Submodule R M) = p := by cases p; rfl
/-
**LieSubmodule.toSubmodule_injective** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：toSubmodule_injective : Function.Injective (toSubmodule : LieSubmodule R L
 M -> Submodule R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem toSubmodule_injective :
    Function.Injective (toSubmodule : LieSubmodule R L M → Submodule R M) := fun x y h ↦ by
  cases x; cases y; congr

@[ext]
/-
**LieSubmodule.ext** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：ext (h : forall m, m in N ↔ m in N') : N = N'
参数：h : forall m, m in N ↔ m in N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
theorem ext (h : ∀ m, m ∈ N ↔ m ∈ N') : N = N' :=
  SetLike.ext h

@[simp]
/-
**LieSubmodule.toSubmodule_inj** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：toSubmodule_inj : (N : Submodule R M) = (N' : Submodule R M) ↔ N = N'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LieSubmodule.toSubmodule_injective`：toSubmodule_injective : Function.Inj
ective (toSubmodule : LieSubmodule R L M -> Submodule R M)
-/
theorem toSubmodule_inj : (N : Submodule R M) = (N' : Submodule R M) ↔ N = N' :=
  toSubmodule_injective.eq_iff

/-- Copy of a `LieSubmodule` with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
/-
**LieSubmodule.copy** 是 Mathlib 中的一个定义，位于命名空间 `LieSubmodule`。
形式化陈述：{R : Type u} →   {L : Type v} →     {M : Type w} →       [inst : CommRing 
R] →         [inst_1 : LieRing L] →           [inst_2 : AddCommGroup M] →       
      [inst_3 : _root_.Module R M] →               [inst_4 : LieRingModule L M] 
→ (N : LieSubmodule R L M) → (s : Set M) → s = ↑N → LieSubmodule R L M
参数：N : LieSubmodule R L M；s : Set M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `LieSubmodule` with a new `carrier` equal to the old one. Useful to fi
x definitional
equalities.
-/
protected def copy (s : Set M) (hs : s = ↑N) : LieSubmodule R L M where
  carrier := s
  zero_mem' := by simp [hs]
  add_mem' x y := by rw [hs] at x y ⊢; exact N.add_mem' x y
  smul_mem' := by exact hs.symm ▸ N.smul_mem'
  lie_mem := by exact hs.symm ▸ N.lie_mem

@[simp, norm_cast]
/-
**LieSubmodule.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：coe_copy (S : LieSubmodule R L M) (s : Set M) (hs : s = ↑S) : (S.copy s hs
 : Set M) = s
参数：S : LieSubmodule R L M；s : Set M；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (S : LieSubmodule R L M) (s : Set M) (hs : s = ↑S) : (S.copy s hs : Set M) = s :=
  rfl
/-
**LieSubmodule.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：copy_eq (S : LieSubmodule R L M) (s : Set M) (hs : s = ↑S) : S.copy s hs =
 S
参数：S : LieSubmodule R L M；s : Set M；hs : s = ↑S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem copy_eq (S : LieSubmodule R L M) (s : Set M) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieRingModule L N where
  bracket (x : L) (m : N) := ⟨⁅x, m.val⁆, N.lie_mem m.property⟩
  add_lie := by intro x y m; apply SetCoe.ext; apply add_lie
  lie_add := by intro x m n; apply SetCoe.ext; apply lie_add
  leibniz_lie := by intro x y m; apply SetCoe.ext; apply leibniz_lie

@[simp, norm_cast]
/-
**LieSubmodule.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：coe_zero : ((0 : N) : M) = (0 : M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
theorem coe_zero : ((0 : N) : M) = (0 : M) :=
  rfl

@[simp, norm_cast]
/-
**LieSubmodule.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：coe_add (m m' : N) : (↑(m + m') : M) = (m : M) + (m' : M)
参数：m m' : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
theorem coe_add (m m' : N) : (↑(m + m') : M) = (m : M) + (m' : M) :=
  rfl

@[simp, norm_cast]
/-
**LieSubmodule.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：coe_neg (m : N) : (↑(-m) : M) = -(m : M)
参数：m : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
theorem coe_neg (m : N) : (↑(-m) : M) = -(m : M) :=
  rfl

@[simp, norm_cast]
/-
**LieSubmodule.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：coe_sub (m m' : N) : (↑(m - m') : M) = (m : M) - (m' : M)
参数：m m' : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
theorem coe_sub (m m' : N) : (↑(m - m') : M) = (m : M) - (m' : M) :=
  rfl

@[simp, norm_cast]
/-
**LieSubmodule.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：coe_smul (t : R) (m : N) : (↑(t • m) : M) = t • (m : M)
参数：t : R；m : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
theorem coe_smul (t : R) (m : N) : (↑(t • m) : M) = t • (m : M) :=
  rfl

@[simp, norm_cast]
/-
**LieSubmodule.coe_bracket** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：coe_bracket (x : L) (m : N) : (↑⁅x, m⁆ : M) = ⁅x, ↑m⁆
参数：x : L；m : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
theorem coe_bracket (x : L) (m : N) :
    (↑⁅x, m⁆ : M) = ⁅x, ↑m⁆ :=
  rfl

-- Copying instances from `Submodule` for correct discrimination keys
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsNoetherian R M] (N : LieSubmodule R L M) : IsNoetherian R N :=
  inferInstanceAs <| IsNoetherian R N.toSubmodule
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsArtinian R M] (N : LieSubmodule R L M) : IsArtinian R N :=
  inferInstanceAs <| IsArtinian R N.toSubmodule
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module.IsTorsionFree R M] : Module.IsTorsionFree R N :=
  inferInstanceAs <| Module.IsTorsionFree R N.toSubmodule

variable [LieAlgebra R L]

/-- Given a Lie submodule `N` of a Lie module `M` over a Lie algebra `L`, and a Lie subalgebra
`H ≤ L`, `N.restr H` is the same submodule but viewed as a Lie submodule over `H`. -/
/-
**LieSubmodule.restr** 是 Mathlib 中的一个定义，位于命名空间 `LieSubmodule`。
形式化陈述：restr (N : LieSubmodule R L M) (H : LieSubalgebra R L) : LieSubmodule R H 
M where carrier
参数：N : LieSubmodule R L M；H : LieSubalgebra R L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a Lie submodule `N` of a Lie module `M` over a Lie algebra `L`, and a Lie 
subalgebra
`H ≤ L`, `N.restr H` is the same submodule but viewed as a Lie submodule over `H
`.
-/
def restr (N : LieSubmodule R L M) (H : LieSubalgebra R L) : LieSubmodule R H M where
  carrier := N
  add_mem' := N.add_mem'
  zero_mem' := N.zero_mem'
  smul_mem' := SMulMemClass.smul_mem
  lie_mem hm := N.lie_mem hm
/-
**LieSubmodule.mem_restr** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：∀ {R : Type u} {L : Type v} {M : Type w} [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] [inst_4 : LieRi
ngModule L M] [inst_5 : LieAlgebra R L] {N : LieSubmodule R L M}   {H : LieSubal
gebra R L} {m : M}, m ∈ N.restr H ↔ m ∈ N
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_restr {N : LieSubmodule R L M} {H : LieSubalgebra R L} {m : M} :
    m ∈ N.restr H ↔ m ∈ N := Iff.rfl
/-
**LieSubmodule.restr_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：∀ {R : Type u} {L : Type v} {M : Type w} [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] [inst_4 : LieRi
ngModule L M] [inst_5 : LieAlgebra R L] (N : LieSubmodule R L M)   (H : LieSubal
gebra R L), ↑(N.restr H) = ↑N
参数：N : LieSubmodule R L M；H : LieSubalgebra R L；N.restr H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma restr_toSubmodule (N : LieSubmodule R L M) (H : LieSubalgebra R L) :
    (N.restr H).toSubmodule = N.toSubmodule := rfl

variable [LieModule R L M]
/-
**LieSubmodule.instLieModule** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
形式化陈述：instLieModule : LieModule R L N where lie_smul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `SetCoe.ext`：SetCoe.ext {s : Set α} {a b : s} : (a : α) = b -> a = b
· 使用定理 `smul_lie`：smul_lie : ⁅t • x, m⁆ = t • ⁅x, m⁆
· 使用定理 `lie_smul`：lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆
-/
instance instLieModule : LieModule R L N where
  lie_smul := by intro t x y; apply SetCoe.ext; apply lie_smul
  smul_lie := by intro t x y; apply SetCoe.ext; apply smul_lie
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton M] : Unique (LieSubmodule R L M) :=
  ⟨⟨0⟩, fun _ ↦ (toSubmodule_inj _ _).mp (Subsingleton.elim _ _)⟩

end LieSubmodule

variable {R M}

/-
**Submodule.exists_lieSubmodule_coe_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.exists_lieSubmodule_coe_eq_iff (p : Submodule R M) : (exists N :
 LieSubmodule R L M, ↑N = p) ↔ forall (x : L) (m : M), m in p -> ⁅x, m⁆ in p
参数：p : Submodule R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […
-/
theorem Submodule.exists_lieSubmodule_coe_eq_iff (p : Submodule R M) :
    (∃ N : LieSubmodule R L M, ↑N = p) ↔ ∀ (x : L) (m : M), m ∈ p → ⁅x, m⁆ ∈ p := by
  constructor
  · rintro ⟨N, rfl⟩ _ _; exact N.lie_mem
  · intro h; use { p with lie_mem := @h }

namespace LieSubalgebra

variable {L}
variable [LieAlgebra R L]
variable (K : LieSubalgebra R L)

/-- Given a Lie subalgebra `K ⊆ L`, if we view `L` as a `K`-module by restriction, it contains
a distinguished Lie submodule for the action of `K`, namely `K` itself. -/
/-
**LieSubalgebra.toLieSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `LieSubalgebra`。
形式化陈述：toLieSubmodule : LieSubmodule R K L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a Lie subalgebra `K ⊆ L`, if we view `L` as a `K`-module by restriction, i
t contains
a distinguished Lie submodule for the action of `K`, namely `K` itself.
-/
def toLieSubmodule : LieSubmodule R K L :=
  { (K : Submodule R L) with lie_mem := fun {x _} hy ↦ K.lie_mem x.property hy }

@[simp]
/-
**LieSubalgebra.coe_toLieSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：coe_toLieSubmodule : (K.toLieSubmodule : Submodule R L) = K
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLieSubmodule : (K.toLieSubmodule : Submodule R L) = K := rfl

variable {K}

@[simp]
/-
**LieSubalgebra.mem_toLieSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebra`。
形式化陈述：mem_toLieSubmodule (x : L) : x in K.toLieSubmodule ↔ x in K
参数：x : L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toLieSubmodule (x : L) : x ∈ K.toLieSubmodule ↔ x ∈ K :=
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

/-
**LieSubmodule.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：coe_injective : Function.Injective ((↑) : LieSubmodule R L M -> Set M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem coe_injective : Function.Injective ((↑) : LieSubmodule R L M → Set M) :=
  SetLike.coe_injective

@[simp, norm_cast]
/-
**LieSubmodule.toSubmodule_le_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodul
e`。
形式化陈述：toSubmodule_le_toSubmodule : (N : Submodule R M) <= N' ↔ N <= N'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSubmodule_le_toSubmodule : (N : Submodule R M) ≤ N' ↔ N ≤ N' :=
  Iff.rfl
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (LieSubmodule R L M) :=
  ⟨0⟩
/-
**LieSubmodule.instUniqueBot** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
形式化陈述：instUniqueBot : Unique (⊥ : LieSubmodule R L M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instUniqueBot : Unique (⊥ : LieSubmodule R L M) :=
  inferInstanceAs <| Unique (⊥ : Submodule R M)

@[simp]
/-
**LieSubmodule.bot_coe** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：bot_coe : ((⊥ : LieSubmodule R L M) : Set M) = {0}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_coe : ((⊥ : LieSubmodule R L M) : Set M) = {0} :=
  rfl

@[simp]
/-
**LieSubmodule.bot_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：bot_toSubmodule : ((⊥ : LieSubmodule R L M) : Submodule R M) = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_toSubmodule : ((⊥ : LieSubmodule R L M) : Submodule R M) = ⊥ :=
  rfl

@[simp]
/-
**LieSubmodule.toSubmodule_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：toSubmodule_eq_bot : (N : Submodule R M) = ⊥ ↔ N = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieSubmodule.bot_toSubmodule`：bot_toSubmodule : ((⊥ : LieSubmodule R L M
) : Submodule R M) = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSubmodule_eq_bot : (N : Submodule R M) = ⊥ ↔ N = ⊥ := by
  rw [← toSubmodule_inj, bot_toSubmodule]
/-
**LieSubmodule.mk_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：∀ {R : Type u} {L : Type v} {M : Type w} [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] [inst_4 : LieRi
ngModule L M] {N : Submodule R M}   {h : ∀ {x : L} {m : M}, m ∈ N.carrier → ⁅x, 
m⁆ ∈ N.carrier}, { toSubmodule := N, lie_mem := h } = ⊥ ↔ N = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieSubmodule.bot_toSubmodule`：bot_toSubmodule : ((⊥ : LieSubmodule R L M
) : Submodule R M) = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mk_eq_bot_iff {N : Submodule R M} {h} :
    (⟨N, h⟩ : LieSubmodule R L M) = ⊥ ↔ N = ⊥ := by
  rw [← toSubmodule_inj, bot_toSubmodule]

@[simp]
/-
**LieSubmodule.mem_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：mem_bot (x : M) : x in (⊥ : LieSubmodule R L M) ↔ x = 0
参数：x : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem mem_bot (x : M) : x ∈ (⊥ : LieSubmodule R L M) ↔ x = 0 :=
  mem_singleton_iff
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Top (LieSubmodule R L M) :=
  ⟨{ (⊤ : Submodule R M) with lie_mem := fun {x m} _ ↦ mem_univ ⁅x, m⁆ }⟩

@[simp]
/-
**LieSubmodule.top_coe** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：top_coe : ((⊤ : LieSubmodule R L M) : Set M) = univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_coe : ((⊤ : LieSubmodule R L M) : Set M) = univ :=
  rfl

@[simp]
/-
**LieSubmodule.top_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：top_toSubmodule : ((⊤ : LieSubmodule R L M) : Submodule R M) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_toSubmodule : ((⊤ : LieSubmodule R L M) : Submodule R M) = ⊤ :=
  rfl

@[simp]
/-
**LieSubmodule.toSubmodule_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：toSubmodule_eq_top : (N : Submodule R M) = ⊤ ↔ N = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieSubmodule.top_toSubmodule`：top_toSubmodule : ((⊤ : LieSubmodule R L M
) : Submodule R M) = ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toSubmodule_eq_top : (N : Submodule R M) = ⊤ ↔ N = ⊤ := by
  rw [← toSubmodule_inj, top_toSubmodule]
/-
**LieSubmodule.mk_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：∀ {R : Type u} {L : Type v} {M : Type w} [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] [inst_4 : LieRi
ngModule L M] {N : Submodule R M}   {h : ∀ {x : L} {m : M}, m ∈ N.carrier → ⁅x, 
m⁆ ∈ N.carrier}, { toSubmodule := N, lie_mem := h } = ⊤ ↔ N = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieSubmodule.top_toSubmodule`：top_toSubmodule : ((⊤ : LieSubmodule R L M
) : Submodule R M) = ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mk_eq_top_iff {N : Submodule R M} {h} :
    (⟨N, h⟩ : LieSubmodule R L M) = ⊤ ↔ N = ⊤ := by
  rw [← toSubmodule_inj, top_toSubmodule]

@[simp]
/-
**LieSubmodule.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：mem_top (x : M) : x in (⊤ : LieSubmodule R L M)
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem mem_top (x : M) : x ∈ (⊤ : LieSubmodule R L M) :=
  mem_univ x
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (LieSubmodule R L M) :=
  ⟨fun N N' ↦
    { (N ⊓ N' : Submodule R M) with
      lie_mem := fun h ↦ mem_inter (N.lie_mem h.1) (N'.lie_mem h.2) }⟩
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (LieSubmodule R L M) :=
  ⟨fun S ↦
    { toSubmodule := sInf {(s : Submodule R M) | s ∈ S}
      lie_mem := fun {x m} h ↦ by
        simp only [Submodule.mem_carrier, mem_iInter, Submodule.coe_sInf, mem_ofPred_eq,
          forall_apply_eq_imp_iff₂, forall_exists_index, and_imp] at h ⊢
        intro N hN; apply N.lie_mem (h N hN) }⟩

@[simp]
/-
**LieSubmodule.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：coe_inf : (↑(N ⊓ N') : Set M) = ↑N inter ↑N'
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf : (↑(N ⊓ N') : Set M) = ↑N ∩ ↑N' :=
  rfl

@[norm_cast, simp]
/-
**LieSubmodule.inf_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：inf_toSubmodule : (↑(N ⊓ N') : Submodule R M) = (N : Submodule R M) ⊓ (N' 
: Submodule R M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_toSubmodule :
    (↑(N ⊓ N') : Submodule R M) = (N : Submodule R M) ⊓ (N' : Submodule R M) :=
  rfl

@[simp]
/-
**LieSubmodule.sInf_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：sInf_toSubmodule (S : Set (LieSubmodule R L M)) : (↑(sInf S) : Submodule R
 M) = sInf {(s : Submodule R M) | s in S}
参数：S : Set (LieSubmodule R L M)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sInf_toSubmodule (S : Set (LieSubmodule R L M)) :
    (↑(sInf S) : Submodule R M) = sInf {(s : Submodule R M) | s ∈ S} :=
  rfl
/-
**LieSubmodule.sInf_toSubmodule_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`
。
形式化陈述：sInf_toSubmodule_eq_iInf (S : Set (LieSubmodule R L M)) : (↑(sInf S) : Sub
module R M) = ⨅ N in S, (N : Submodule R M)
参数：S : Set (LieSubmodule R L M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.sInf_toSubmodule`：sInf_toSubmodule (S : Set (LieSubmodule R
 L M)) : (↑(sInf S) : Submodule R M) = sInf {(s : Submodule R M) | s in S}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image.eq_1`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Set α), f '
' s = {x | ∃ a ∈ s, f a = x}
· 使用定理 `sInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
s : Set β} {f : β → α}, sInf (f '' s) = ⨅ a ∈ s, f a
-/
theorem sInf_toSubmodule_eq_iInf (S : Set (LieSubmodule R L M)) :
    (↑(sInf S) : Submodule R M) = ⨅ N ∈ S, (N : Submodule R M) := by
  rw [sInf_toSubmodule, ← Set.image, sInf_image]

@[simp]
/-
**LieSubmodule.iInf_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：iInf_toSubmodule {ι} (p : ι -> LieSubmodule R L M) : (↑(⨅ i, p i) : Submod
ule R M) = ⨅ i, (p i : Submodule R M)
参数：p : ι -> LieSubmodule R L M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `LieSubmodule.sInf_toSubmodule`：sInf_toSubmodule (S : Set (LieSubmodule R
 L M)) : (↑(sInf S) : Submodule R M) = sInf {(s : Submodule R M) | s in S}
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iInf_toSubmodule {ι} (p : ι → LieSubmodule R L M) :
    (↑(⨅ i, p i) : Submodule R M) = ⨅ i, (p i : Submodule R M) := by
  rw [iInf, sInf_toSubmodule]; ext; simp

@[simp]
/-
**LieSubmodule.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：coe_sInf (S : Set (LieSubmodule R L M)) : (↑(sInf S) : Set M) = ⋂ s in S, 
(s : Set M)
参数：S : Set (LieSubmodule R L M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.coe_toSubmodule`：coe_toSubmodule : ((N : Submodule R M) : S
et M) = N
· 使用定理 `LieSubmodule.sInf_toSubmodule`：sInf_toSubmodule (S : Set (LieSubmodule R
 L M)) : (↑(sInf S) : Submodule R M) = sInf {(s : Submodule R M) | s in S}
· 使用定理 `Submodule.coe_sInf`：coe_sInf (P : Set (Submodule R M)) : (↑(sInf P) : Se
t M) = ⋂ p in P, ↑p
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_sInf (S : Set (LieSubmodule R L M)) : (↑(sInf S) : Set M) = ⋂ s ∈ S, (s : Set M) := by
  rw [← LieSubmodule.coe_toSubmodule, sInf_toSubmodule, Submodule.coe_sInf]
  ext m
  simp only [mem_iInter, mem_ofPred_eq, forall_apply_eq_imp_iff₂, exists_imp,
    and_imp, SetLike.mem_coe, mem_toSubmodule]

@[simp]
/-
**LieSubmodule.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：coe_iInf {ι} (p : ι -> LieSubmodule R L M) : (↑(⨅ i, p i) : Set M) = ⋂ i, 
↑(p i)
参数：p : ι -> LieSubmodule R L M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `LieSubmodule.coe_sInf`：coe_sInf (S : Set (LieSubmodule R L M)) : (↑(sInf
 S) : Set M) = ⋂ s in S, (s : Set M)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iInter_iInter_eq'`：iInter_iInter_eq' {f : ι -> α} {g : α -> Set β} :
 ⋂ (x) (y) (_ : f y = x), g x = ⋂ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_iInf {ι} (p : ι → LieSubmodule R L M) : (↑(⨅ i, p i) : Set M) = ⋂ i, ↑(p i) := by
  rw [iInf, coe_sInf]; simp only [Set.mem_range, Set.iInter_exists, Set.iInter_iInter_eq']

@[simp]
/-
**LieSubmodule.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：mem_iInf {ι} (p : ι -> LieSubmodule R L M) {x} : x in ⨅ i, p i ↔ forall i,
 x in p i
参数：p : ι -> LieSubmodule R L M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `LieSubmodule.coe_iInf`：coe_iInf {ι} (p : ι -> LieSubmodule R L M) : (↑(⨅
 i, p i) : Set M) = ⋂ i, ↑(p i)
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_iInf {ι} (p : ι → LieSubmodule R L M) {x} : x ∈ ⨅ i, p i ↔ ∀ i, x ∈ p i := by
  rw [← SetLike.mem_coe, coe_iInf, Set.mem_iInter]; rfl
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (LieSubmodule R L M) where
  max N N' :=
    { toSubmodule := (N : Submodule R M) ⊔ (N' : Submodule R M)
      lie_mem := by
        rintro x m (hm : m ∈ (N : Submodule R M) ⊔ (N' : Submodule R M))
        change ⁅x, m⁆ ∈ (N : Submodule R M) ⊔ (N' : Submodule R M)
        rw [Submodule.mem_sup] at hm ⊢
        obtain ⟨y, hy, z, hz, rfl⟩ := hm
        exact ⟨⁅x, y⁆, N.lie_mem hy, ⁅x, z⁆, N'.lie_mem hz, (lie_add _ _ _).symm⟩ }
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SupSet (LieSubmodule R L M) where
  sSup S :=
    { toSubmodule := sSup {(p : Submodule R M) | p ∈ S}
      lie_mem := by
        intro x m (hm : m ∈ sSup {(p : Submodule R M) | p ∈ S})
        change ⁅x, m⁆ ∈ sSup {(p : Submodule R M) | p ∈ S}
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
          obtain ⟨p, hp, rfl⟩ : ∃ p ∈ S, ↑p = q := hs (Finset.mem_insert_self q t)
          suffices p ≤ sSup {(p : Submodule R M) | p ∈ S} by exact this (p.lie_mem hm')
          exact le_sSup ⟨p, hp, rfl⟩ }

@[norm_cast, simp]
/-
**LieSubmodule.sup_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：sup_toSubmodule : (↑(N ⊔ N') : Submodule R M) = (N : Submodule R M) ⊔ (N' 
: Submodule R M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_toSubmodule :
    (↑(N ⊔ N') : Submodule R M) = (N : Submodule R M) ⊔ (N' : Submodule R M) := by
  rfl

@[simp]
/-
**LieSubmodule.sSup_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：sSup_toSubmodule (S : Set (LieSubmodule R L M)) : (↑(sSup S) : Submodule R
 M) = sSup {(s : Submodule R M) | s in S}
参数：S : Set (LieSubmodule R L M)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sSup_toSubmodule (S : Set (LieSubmodule R L M)) :
    (↑(sSup S) : Submodule R M) = sSup {(s : Submodule R M) | s ∈ S} :=
  rfl
/-
**LieSubmodule.sSup_toSubmodule_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`
。
形式化陈述：sSup_toSubmodule_eq_iSup (S : Set (LieSubmodule R L M)) : (↑(sSup S) : Sub
module R M) = ⨆ N in S, (N : Submodule R M)
参数：S : Set (LieSubmodule R L M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.sSup_toSubmodule`：sSup_toSubmodule (S : Set (LieSubmodule R
 L M)) : (↑(sSup S) : Submodule R M) = sSup {(s : Submodule R M) | s in S}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image.eq_1`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Set α), f '
' s = {x | ∃ a ∈ s, f a = x}
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
-/
theorem sSup_toSubmodule_eq_iSup (S : Set (LieSubmodule R L M)) :
    (↑(sSup S) : Submodule R M) = ⨆ N ∈ S, (N : Submodule R M) := by
  rw [sSup_toSubmodule, ← Set.image, sSup_image]

@[simp]
/-
**LieSubmodule.iSup_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：iSup_toSubmodule {ι} (p : ι -> LieSubmodule R L M) : (↑(⨆ i, p i) : Submod
ule R M) = ⨆ i, (p i : Submodule R M)
参数：p : ι -> LieSubmodule R L M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `LieSubmodule.sSup_toSubmodule`：sSup_toSubmodule (S : Set (LieSubmodule R
 L M)) : (↑(sSup S) : Submodule R M) = sSup {(s : Submodule R M) | s in S}
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iSup_toSubmodule {ι} (p : ι → LieSubmodule R L M) :
    (↑(⨆ i, p i) : Submodule R M) = ⨆ i, (p i : Submodule R M) := by
  rw [iSup, sSup_toSubmodule]; ext; simp [Submodule.mem_sSup, Submodule.mem_iSup]

/-- The Lie submodules of a Lie module form a complete lattice. -/
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Lie submodules of a Lie module form a complete lattice.
-/
instance : CompleteLattice (LieSubmodule R L M) :=
  toSubmodule_injective.completeLattice toSubmodule .rfl .rfl sup_toSubmodule inf_toSubmodule
    sSup_toSubmodule_eq_iSup sInf_toSubmodule_eq_iInf rfl rfl
/-
**LieSubmodule.mem_iSup_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：mem_iSup_of_mem {ι} {b : M} {N : ι -> LieSubmodule R L M} (i : ι) (h : b i
n N i) : b in ⨆ i, N i
参数：i : ι；h : b in N i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem mem_iSup_of_mem {ι} {b : M} {N : ι → LieSubmodule R L M} (i : ι) (h : b ∈ N i) :
    b ∈ ⨆ i, N i :=
  (le_iSup N i) h

@[elab_as_elim]
/-
**LieSubmodule.iSup_induction** 是 Mathlib 中的一个引理，位于命名空间 `LieSubmodule`。
形式化陈述：iSup_induction {ι} (N : ι -> LieSubmodule R L M) {motive : M -> Prop} {x :
 M} (hx : x in ⨆ i, N i) (mem : forall i, forall y in N i, motive y) (zero : mot
ive 0) (add : forall y z, motive y -> motive z -> motive (y + z)) : motive x
参数：N : ι -> LieSubmodule R L M；hx : x in ⨆ i, N i；mem : forall i, forall y in N 
i, motive y；zero : motive 0；add : forall y z, motive y -> motive z -> motive (y 
+ z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.iSup_induction`：iSup_induction {ι : Sort*} (p : ι -> Submodule
 R M) {motive : M -> Prop} {x : M} (hx : x in ⨆ i, p i) (mem : forall (i), foral
l x in p i, mo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.iSup_toSubmodule`：iSup_toSubmodule {ι} (p : ι -> LieSubmodu
le R L M) : (↑(⨆ i, p i) : Submodule R M) = ⨆ i, (p i : Submodule R M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.mem_toSubmodule`：mem_toSubmodule {x : M} : x in (N : Submod
ule R M) ↔ x in N
-/
lemma iSup_induction {ι} (N : ι → LieSubmodule R L M) {motive : M → Prop} {x : M}
    (hx : x ∈ ⨆ i, N i) (mem : ∀ i, ∀ y ∈ N i, motive y) (zero : motive 0)
    (add : ∀ y z, motive y → motive z → motive (y + z)) : motive x := by
  rw [← LieSubmodule.mem_toSubmodule, LieSubmodule.iSup_toSubmodule] at hx
  exact Submodule.iSup_induction (motive := motive) (fun i ↦ (N i : Submodule R M)) hx mem zero add

@[elab_as_elim]
/-
**LieSubmodule.iSup_induction'** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：iSup_induction' {ι} (N : ι -> LieSubmodule R L M) {motive : (x : M) -> (x 
in ⨆ i, N i) -> Prop} (mem : forall (i) (x) (hx : x in N i), motive x (mem_iSup_
of_mem i hx)) (zero : motive 0 (zero_mem _)) (add : forall x y hx hy, motive x h
x -> motive y hy -> motive (x + y) (add_mem ‹_› ‹_›)) {x : M} (hx : x in ⨆ i, N 
i) : motive x hx
参数：N : ι -> LieSubmodule R L M；x : M；x in ⨆ i, N i；mem : forall (i) (x) (hx : x 
in N i), motive x (mem_iSup_of_mem i hx)；zero : motive 0 (zero_mem _)；add : fora
ll x y hx hy, motive x hx -> motive y hy -> motive (x + y) (add_mem ‹_› ‹_›)；hx 
: x in ⨆ i, N i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.mem_iSup_of_mem`：mem_iSup_of_mem {ι} {b : M} {N : ι -> LieS
ubmodule R L M} (i : ι) (h : b in N i) : b in ⨆ i, N i
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用引理 `LieSubmodule.iSup_induction`：iSup_induction {ι} (N : ι -> LieSubmodule R
 L M) {motive : M -> Prop} {x : M} (hx : x in ⨆ i, N i) (mem : forall i, forall 
y in N i, motive …
-/
theorem iSup_induction' {ι} (N : ι → LieSubmodule R L M) {motive : (x : M) → (x ∈ ⨆ i, N i) → Prop}
    (mem : ∀ (i) (x) (hx : x ∈ N i), motive x (mem_iSup_of_mem i hx)) (zero : motive 0 (zero_mem _))
    (add : ∀ x y hx hy, motive x hx → motive y hy → motive (x + y) (add_mem ‹_› ‹_›)) {x : M}
    (hx : x ∈ ⨆ i, N i) : motive x hx := by
  refine Exists.elim ?_ fun (hx : x ∈ ⨆ i, N i) (hc : motive x hx) => hc
  refine iSup_induction N (motive := fun x : M ↦ ∃ (hx : x ∈ ⨆ i, N i), motive x hx) hx
    (fun i x hx => ?_) ?_ fun x y => ?_
  · exact ⟨_, mem _ _ hx⟩
  · exact ⟨_, zero⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    exact ⟨_, add _ _ _ _ Cx Cy⟩

variable {N N'}
/-
**LieSubmodule.disjoint_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：∀ {R : Type u} {L : Type v} {M : Type w} [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] [inst_4 : LieRi
ngModule L M] {N N' : LieSubmodule R L M}, Disjoint ↑N ↑N' ↔ Disjoint N N'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieSubmodule.inf_toSubmodule`：inf_toSubmodule : (↑(N ⊓ N') : Submodule R
 M) = (N : Submodule R M) ⊓ (N' : Submodule R M)
· 使用定理 `LieSubmodule.bot_toSubmodule`：bot_toSubmodule : ((⊥ : LieSubmodule R L M
) : Submodule R M) = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma disjoint_toSubmodule :
    Disjoint (N : Submodule R M) (N' : Submodule R M) ↔ Disjoint N N' := by
  rw [disjoint_iff, disjoint_iff, ← toSubmodule_inj, inf_toSubmodule, bot_toSubmodule,
    ← disjoint_iff]
/-
**LieSubmodule.codisjoint_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：∀ {R : Type u} {L : Type v} {M : Type w} [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] [inst_4 : LieRi
ngModule L M] {N N' : LieSubmodule R L M},   Codisjoint ↑N ↑N' ↔ Codisjoint N N'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieSubmodule.sup_toSubmodule`：sup_toSubmodule : (↑(N ⊔ N') : Submodule R
 M) = (N : Submodule R M) ⊔ (N' : Submodule R M)
· 使用定理 `LieSubmodule.top_toSubmodule`：top_toSubmodule : ((⊤ : LieSubmodule R L M
) : Submodule R M) = ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma codisjoint_toSubmodule :
    Codisjoint (N : Submodule R M) (N' : Submodule R M) ↔ Codisjoint N N' := by
  rw [codisjoint_iff, codisjoint_iff, ← toSubmodule_inj, sup_toSubmodule,
    top_toSubmodule, ← codisjoint_iff]
/-
**LieSubmodule.isCompl_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：∀ {R : Type u} {L : Type v} {M : Type w} [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] [inst_4 : LieRi
ngModule L M] {N N' : LieSubmodule R L M}, IsCompl ↑N ↑N' ↔ IsCompl N N'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isCompl_toSubmodule :
    IsCompl (N : Submodule R M) (N' : Submodule R M) ↔ IsCompl N N' := by
  simp [isCompl_iff]
/-
**LieSubmodule.iSupIndep_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：∀ {R : Type u} {L : Type v} {M : Type w} [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] [inst_4 : LieRi
ngModule L M] {ι : Type u_1} {N : ι → LieSubmodule R L M},   (iSupIndep fun i =>
 ↑(N i)) ↔ iSupIndep N
参数：iSupIndep fun i => ↑(N i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LieSubmodule.iSup_toSubmodule`：iSup_toSubmodule {ι} (p : ι -> LieSubmodu
le R L M) : (↑(⨆ i, p i) : Submodule R M) = ⨆ i, (p i : Submodule R M)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma iSupIndep_toSubmodule {ι : Type*} {N : ι → LieSubmodule R L M} :
    iSupIndep (fun i ↦ (N i : Submodule R M)) ↔ iSupIndep N := by
  simp [iSupIndep_def, ← disjoint_toSubmodule]
/-
**LieSubmodule.iSup_toSubmodule_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：∀ {R : Type u} {L : Type v} {M : Type w} [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] [inst_4 : LieRi
ngModule L M] {ι : Sort u_1} {N : ι → LieSubmodule R L M},   ⨆ i, ↑(N i) = ⊤ ↔ ⨆
 i, N i = ⊤
参数：N i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.iSup_toSubmodule`：iSup_toSubmodule {ι} (p : ι -> LieSubmodu
le R L M) : (↑(⨆ i, p i) : Submodule R M) = ⨆ i, (p i : Submodule R M)
· 使用定理 `LieSubmodule.top_toSubmodule`：top_toSubmodule : ((⊤ : LieSubmodule R L M
) : Submodule R M) = ⊤
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma iSup_toSubmodule_eq_top {ι : Sort*} {N : ι → LieSubmodule R L M} :
    ⨆ i, (N i : Submodule R M) = ⊤ ↔ ⨆ i, N i = ⊤ := by
  rw [← iSup_toSubmodule, ← top_toSubmodule (L := L), toSubmodule_inj]
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (LieSubmodule R L M) where add := max
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommMonoid (LieSubmodule R L M) where
  add_assoc := sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  nsmul := nsmulRec

variable (N N')

@[simp]
/-
**LieSubmodule.add_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：add_eq_sup : N + N' = N ⊔ N'
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_eq_sup : N + N' = N ⊔ N' :=
  rfl

@[simp]
/-
**LieSubmodule.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：mem_inf (x : M) : x in N ⊓ N' ↔ x in N ∧ x in N'
参数：x : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.mem_toSubmodule`：mem_toSubmodule {x : M} : x in (N : Submod
ule R M) ↔ x in N
· 使用定理 `LieSubmodule.inf_toSubmodule`：inf_toSubmodule : (↑(N ⊓ N') : Submodule R
 M) = (N : Submodule R M) ⊓ (N' : Submodule R M)
· 使用定理 `Submodule.mem_inf`：mem_inf {p q : Submodule R M} {x : M} : x in p ⊓ q ↔ 
x in p ∧ x in q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inf (x : M) : x ∈ N ⊓ N' ↔ x ∈ N ∧ x ∈ N' := by
  rw [← mem_toSubmodule, ← mem_toSubmodule, ← mem_toSubmodule, inf_toSubmodule,
    Submodule.mem_inf]
/-
**LieSubmodule.mem_sup** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：mem_sup (x : M) : x in N ⊔ N' ↔ exists y in N, exists z in N', y + z = x
参数：x : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.mem_toSubmodule`：mem_toSubmodule {x : M} : x in (N : Submod
ule R M) ↔ x in N
· 使用定理 `LieSubmodule.sup_toSubmodule`：sup_toSubmodule : (↑(N ⊔ N') : Submodule R
 M) = (N : Submodule R M) ⊔ (N' : Submodule R M)
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_sup (x : M) : x ∈ N ⊔ N' ↔ ∃ y ∈ N, ∃ z ∈ N', y + z = x := by
  rw [← mem_toSubmodule, sup_toSubmodule, Submodule.mem_sup]; exact Iff.rfl

variable {N N'} in
/-
**LieSubmodule.mem_sup_left** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：mem_sup_left {x : M} (hx : x in N) : x in N ⊔ N'
参数：hx : x in N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem mem_sup_left {x : M} (hx : x ∈ N) : x ∈ N ⊔ N' :=
  le_sup_left (a := N) hx

variable {N N'} in
/-
**LieSubmodule.mem_sup_right** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：mem_sup_right {x : M} (hx : x in N') : x in N ⊔ N'
参数：hx : x in N'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieSubmodule.mem_sup`：mem_sup (x : M) : x in N ⊔ N' ↔ exists y in N, exi
sts z in N', y + z = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mem_sup_right {x : M} (hx : x ∈ N') : x ∈ N ⊔ N' :=
  (mem_sup _ _ _).mpr ⟨0, by simp, x, hx, by simp⟩

nonrec theorem eq_bot_iff : N = ⊥ ↔ ∀ m : M, m ∈ N → m = 0 := by rw [eq_bot_iff]; exact Iff.rfl
/-
**LieSubmodule.subsingleton_of_bot** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
形式化陈述：subsingleton_of_bot : Subsingleton (LieSubmodule R L (⊥ : LieSubmodule R L
 M))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_of_bot_eq_top`：subsingleton_of_bot_eq_top (hα : (⊥ : α) = (
⊤ : α)) : Subsingleton α
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
instance subsingleton_of_bot : Subsingleton (LieSubmodule R L (⊥ : LieSubmodule R L M)) := by
  apply subsingleton_of_bot_eq_top
  subsingleton
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsModularLattice (LieSubmodule R L M) where
  sup_inf_le_assoc_of_le _ _ := by
    simp only [← toSubmodule_le_toSubmodule, sup_toSubmodule, inf_toSubmodule]
    exact IsModularLattice.sup_inf_le_assoc_of_le _

variable (R L M)

/-- The natural functor that forgets the action of `L` as an order embedding. -/
/-
**LieSubmodule.toSubmodule_orderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `LieSubmodul
e`。
形式化陈述：(R : Type u) →   (L : Type v) →     (M : Type w) →       [inst : CommRing 
R] →         [inst_1 : LieRing L] →           [inst_2 : AddCommGroup M] →       
      [inst_3 : _root_.Module R M] → [inst_4 : LieRingModule L M] → LieSubmodule
 R L M ↪o Submodule R M
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.toSubmodule_injective`：toSubmodule_injective : Function.Inj
ective (toSubmodule : LieSubmodule R L M -> Submodule R M)

--- 原说明 ---
The natural functor that forgets the action of `L` as an order embedding.
-/
@[simps] def toSubmodule_orderEmbedding : LieSubmodule R L M ↪o Submodule R M :=
  { toFun := (↑)
    inj' := toSubmodule_injective
    map_rel_iff' := Iff.rfl }
/-
**LieSubmodule.wellFoundedGT_of_noetherian** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodu
le`。
形式化陈述：wellFoundedGT_of_noetherian [IsNoetherian R M] : WellFoundedGT (LieSubmodu
le R L M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHomClass.isWellFounded`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → 
Prop} {s : β → β → Prop} {F : Type u_5} [inst : FunLike F α β]   [RelHomClass F 
r s] (f : F) [I…
· 使用定理 `RelEmbedding.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α
 → Prop} {s : β → β → Prop}, RelHomClass (r ↪r s) r s
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
-/
instance wellFoundedGT_of_noetherian [IsNoetherian R M] : WellFoundedGT (LieSubmodule R L M) :=
  RelHomClass.isWellFounded (toSubmodule_orderEmbedding R L M).dual.ltEmbedding
/-
**LieSubmodule.wellFoundedLT_of_isArtinian** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodu
le`。
形式化陈述：wellFoundedLT_of_isArtinian [IsArtinian R M] : WellFoundedLT (LieSubmodule
 R L M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHomClass.isWellFounded`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → 
Prop} {s : β → β → Prop} {F : Type u_5} [inst : FunLike F α β]   [RelHomClass F 
r s] (f : F) [I…
· 使用定理 `RelEmbedding.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α
 → Prop} {s : β → β → Prop}, RelHomClass (r ↪r s) r s
-/
theorem wellFoundedLT_of_isArtinian [IsArtinian R M] : WellFoundedLT (LieSubmodule R L M) :=
  RelHomClass.isWellFounded (toSubmodule_orderEmbedding R L M).ltEmbedding
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsArtinian R M] : IsAtomic (LieSubmodule R L M) :=
  isAtomic_of_orderBot_wellFounded_lt <| (wellFoundedLT_of_isArtinian R L M).wf

@[simp]
/-
**LieSubmodule.subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：subsingleton_iff : Subsingleton (LieSubmodule R L M) ↔ Subsingleton M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `subsingleton_iff_bot_eq_top`：subsingleton_iff_bot_eq_top : (⊥ : α) = (⊤ 
: α) ↔ Subsingleton α
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieSubmodule.top_toSubmodule`：top_toSubmodule : ((⊤ : LieSubmodule R L M
) : Submodule R M) = ⊤
· 使用定理 `LieSubmodule.bot_toSubmodule`：bot_toSubmodule : ((⊥ : LieSubmodule R L M
) : Submodule R M) = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Submodule.subsingleton_iff`：subsingleton_iff : Subsingleton (Submodule R
 M) ↔ Subsingleton M
-/
theorem subsingleton_iff : Subsingleton (LieSubmodule R L M) ↔ Subsingleton M :=
  have h : Subsingleton (LieSubmodule R L M) ↔ Subsingleton (Submodule R M) := by
    rw [← subsingleton_iff_bot_eq_top, ← subsingleton_iff_bot_eq_top, ← toSubmodule_inj,
      top_toSubmodule, bot_toSubmodule]
  h.trans <| Submodule.subsingleton_iff R

@[simp]
/-
**LieSubmodule.nontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：nontrivial_iff : Nontrivial (LieSubmodule R L M) ↔ Nontrivial M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `not_nontrivial_iff_subsingleton`：not_nontrivial_iff_subsingleton : ¬Nont
rivial α ↔ Subsingleton α
· 使用定理 `LieSubmodule.subsingleton_iff`：subsingleton_iff : Subsingleton (LieSubmo
dule R L M) ↔ Subsingleton M
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
-/
theorem nontrivial_iff : Nontrivial (LieSubmodule R L M) ↔ Nontrivial M :=
  not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans <| subsingleton_iff R L M).trans
      not_nontrivial_iff_subsingleton.symm)
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial M] : Nontrivial (LieSubmodule R L M) :=
  (nontrivial_iff R L M).mpr ‹_›
/-
**LieSubmodule.nontrivial_iff_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：nontrivial_iff_ne_bot {N : LieSubmodule R L M} : Nontrivial N ↔ N != ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieSubmodule.mem_bot`：mem_bot (x : M) : x in (⊥ : LieSubmodule R L M) ↔ 
x = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LieSubmodule.eq_bot_iff`：∀ {R : Type u} {L : Type v} {M : Type w} [inst 
: CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.
Module R M] […
· 使用定理 `LieSubmodule.zero_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mo
dule R M] […
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
-/
theorem nontrivial_iff_ne_bot {N : LieSubmodule R L M} : Nontrivial N ↔ N ≠ ⊥ := by
  constructor
  · rintro ⟨⟨m₁, h₁⟩, ⟨m₂, h₂⟩, h₁₂⟩ rfl
    simp [(LieSubmodule.mem_bot _).mp h₁, (LieSubmodule.mem_bot _).mp h₂] at h₁₂
  · contrapose!
    rw [LieSubmodule.eq_bot_iff]
    rintro ⟨h⟩ m hm
    simpa using h ⟨m, hm⟩ ⟨_, N.zero_mem⟩

variable {R L M}

section InclusionMaps

/-- The inclusion of a Lie submodule into its ambient space is a morphism of Lie modules. -/
/-
**LieSubmodule.incl** 是 Mathlib 中的一个定义，位于命名空间 `LieSubmodule`。
形式化陈述：incl : N ->ₗ⁅R,L⁆ M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […

--- 原说明 ---
The inclusion of a Lie submodule into its ambient space is a morphism of Lie mod
ules.
-/
def incl : N →ₗ⁅R,L⁆ M :=
  { Submodule.subtype (N : Submodule R M) with map_lie' := fun {_ _} ↦ rfl }

@[simp]
/-
**LieSubmodule.incl_coe** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：incl_coe : (N.incl : N ->ₗ[R] M) = (N : Submodule R M).subtype
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
theorem incl_coe : (N.incl : N →ₗ[R] M) = (N : Submodule R M).subtype :=
  rfl

@[simp]
/-
**LieSubmodule.incl_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：incl_apply (m : N) : N.incl m = m
参数：m : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
theorem incl_apply (m : N) : N.incl m = m :=
  rfl
/-
**LieSubmodule.incl_eq_val** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：incl_eq_val : (N.incl : N -> M) = Subtype.val
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
theorem incl_eq_val : (N.incl : N → M) = Subtype.val :=
  rfl
/-
**LieSubmodule.injective_incl** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：injective_incl : Function.Injective N.incl
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem injective_incl : Function.Injective N.incl := Subtype.coe_injective

variable {N N'}
variable (h : N ≤ N')

/-- Given two nested Lie submodules `N ⊆ N'`,
the inclusion `N ↪ N'` is a morphism of Lie modules. -/
/-
**LieSubmodule.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `LieSubmodule`。
形式化陈述：inclusion : N ->ₗ⁅R,L⁆ N' where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […

--- 原说明 ---
Given two nested Lie submodules `N ⊆ N'`,
the inclusion `N ↪ N'` is a morphism of Lie modules.
-/
def inclusion : N →ₗ⁅R,L⁆ N' where
  __ := Submodule.inclusion (show N.toSubmodule ≤ N'.toSubmodule from h)
  map_lie' := rfl

@[simp]
/-
**LieSubmodule.coe_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：coe_inclusion (m : N) : (inclusion h m : M) = m
参数：m : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
theorem coe_inclusion (m : N) : (inclusion h m : M) = m :=
  rfl
/-
**LieSubmodule.inclusion_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：inclusion_apply (m : N) : inclusion h m = ⟨m.1, h m.2⟩
参数：m : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
theorem inclusion_apply (m : N) : inclusion h m = ⟨m.1, h m.2⟩ :=
  rfl
/-
**LieSubmodule.inclusion_injective** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
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

end InclusionMaps

section LieSpan

variable (R L) (s : Set M)

/-- The `lieSpan` of a set `s ⊆ M` is the smallest Lie submodule of `M` that contains `s`. -/
/-
**LieSubmodule.lieSpan** 是 Mathlib 中的一个定义，位于命名空间 `LieSubmodule`。
形式化陈述：lieSpan : LieSubmodule R L M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `lieSpan` of a set `s ⊆ M` is the smallest Lie submodule of `M` that contain
s `s`.
-/
def lieSpan : LieSubmodule R L M :=
  sInf { N | s ⊆ N }

variable {R L s}
/-
**LieSubmodule.mem_lieSpan** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：mem_lieSpan {x : M} : x in lieSpan R L s ↔ forall N : LieSubmodule R L M, 
s subseteq N -> x in N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `LieSubmodule.lieSpan.eq_1`：∀ (R : Type u) (L : Type v) {M : Type w} [ins
t : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root
_.Module R M] […
· 使用定理 `LieSubmodule.coe_sInf`：coe_sInf (S : Set (LieSubmodule R L M)) : (↑(sInf
 S) : Set M) = ⋂ s in S, (s : Set M)
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
-/
theorem mem_lieSpan {x : M} : x ∈ lieSpan R L s ↔ ∀ N : LieSubmodule R L M, s ⊆ N → x ∈ N := by
  rw [← SetLike.mem_coe, lieSpan, coe_sInf]
  exact mem_iInter₂
/-
**LieSubmodule.subset_lieSpan** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：subset_lieSpan : s subseteq lieSpan R L s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `LieSubmodule.mem_lieSpan`：mem_lieSpan {x : M} : x in lieSpan R L s ↔ for
all N : LieSubmodule R L M, s subseteq N -> x in N
-/
theorem subset_lieSpan : s ⊆ lieSpan R L s := by
  intro m hm
  rw [SetLike.mem_coe, mem_lieSpan]
  intro N hN
  exact hN hm
/-
**LieSubmodule.submodule_span_le_lieSpan** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule
`。
形式化陈述：submodule_span_le_lieSpan : Submodule.span R s <= lieSpan R L s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `LieSubmodule.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
-/
theorem submodule_span_le_lieSpan : Submodule.span R s ≤ lieSpan R L s := by
  rw [Submodule.span_le]
  apply subset_lieSpan

@[simp]
/-
**LieSubmodule.lieSpan_le** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：lieSpan_le {N} : lieSpan R L s <= N ↔ s subseteq N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `LieSubmodule.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.mem_lieSpan`：mem_lieSpan {x : M} : x in lieSpan R L s ↔ for
all N : LieSubmodule R L M, s subseteq N -> x in N
-/
theorem lieSpan_le {N} : lieSpan R L s ≤ N ↔ s ⊆ N := by
  constructor
  · exact Subset.trans subset_lieSpan
  · intro hs m hm; rw [mem_lieSpan] at hm; exact hm _ hs

@[gcongr]
/-
**LieSubmodule.lieSpan_mono** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：lieSpan_mono {t : Set M} (h : s subseteq t) : lieSpan R L s <= lieSpan R L
 t
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.lieSpan_le`：lieSpan_le {N} : lieSpan R L s <= N ↔ s subsete
q N
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `LieSubmodule.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
-/
theorem lieSpan_mono {t : Set M} (h : s ⊆ t) : lieSpan R L s ≤ lieSpan R L t := by
  rw [lieSpan_le]
  exact Subset.trans h subset_lieSpan
/-
**LieSubmodule.lieSpan_eq** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：lieSpan_eq (N : LieSubmodule R L M) : lieSpan R L (N : Set M) = N
参数：N : LieSubmodule R L M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieSubmodule.lieSpan_le`：lieSpan_le {N} : lieSpan R L s <= N ↔ s subsete
q N
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `LieSubmodule.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
-/
theorem lieSpan_eq (N : LieSubmodule R L M) : lieSpan R L (N : Set M) = N :=
  le_antisymm (lieSpan_le.mpr rfl.subset) subset_lieSpan
/-
**LieSubmodule.coe_lieSpan_submodule_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmod
ule`。
形式化陈述：coe_lieSpan_submodule_eq_iff {p : Submodule R M} : (lieSpan R L (p : Set M
) : Submodule R M) = p ↔ exists N : LieSubmodule R L M, ↑N = p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.exists_lieSubmodule_coe_eq_iff`：Submodule.exists_lieSubmodule_
coe_eq_iff (p : Submodule R M) : (exists N : LieSubmodule R L M, ↑N = p) ↔ foral
l (x : L) (m : M), m in p -> ⁅…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.mem_toSubmodule`：mem_toSubmodule {x : M} : x in (N : Submod
ule R M) ↔ x in N
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […
· 使用定理 `LieSubmodule.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
· 使用定理 `LieSubmodule.toSubmodule_mk`：toSubmodule_mk (p : Submodule R M) (h) : ((
{ p with lie_mem
· 使用定理 `LieSubmodule.coe_toSubmodule`：coe_toSubmodule : ((N : Submodule R M) : S
et M) = N
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieSubmodule.lieSpan_eq`：lieSpan_eq (N : LieSubmodule R L M) : lieSpan R
 L (N : Set M) = N
-/
theorem coe_lieSpan_submodule_eq_iff {p : Submodule R M} :
    (lieSpan R L (p : Set M) : Submodule R M) = p ↔ ∃ N : LieSubmodule R L M, ↑N = p := by
  rw [p.exists_lieSubmodule_coe_eq_iff L]; constructor <;> intro h
  · intro x m hm; rw [← h, mem_toSubmodule]; exact lie_mem _ (subset_lieSpan hm)
  · rw [← toSubmodule_mk p @h, coe_toSubmodule, toSubmodule_inj, lieSpan_eq]

variable (R L M)

/-- `lieSpan` forms a Galois insertion with the coercion from `LieSubmodule` to `Set`. -/
/-
**LieSubmodule.gi** 是 Mathlib 中的一个定义，位于命名空间 `LieSubmodule`。
形式化陈述：(R : Type u) →   (L : Type v) →     (M : Type w) →       [inst : CommRing 
R] →         [inst_1 : LieRing L] →           [inst_2 : AddCommGroup M] →       
      [inst_3 : _root_.Module R M] →               [inst_4 : LieRingModule L M] 
→ GaloisInsertion (LieSubmodule.lieSpan R L) SetLike.coe
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.lieSpan_le`：lieSpan_le {N} : lieSpan R L s <= N ↔ s subsete
q N

--- 原说明 ---
`lieSpan` forms a Galois insertion with the coercion from `LieSubmodule` to `Set
`.
-/
protected def gi : GaloisInsertion (lieSpan R L : Set M → LieSubmodule R L M) (↑) where
  choice s _ := lieSpan R L s
  gc _ _ := lieSpan_le
  le_l_u _ := subset_lieSpan
  choice_eq _ _ := rfl

@[simp]
/-
**LieSubmodule.span_empty** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：span_empty : lieSpan R L (∅ : Set M) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem span_empty : lieSpan R L (∅ : Set M) = ⊥ :=
  (LieSubmodule.gi R L M).gc.l_bot

@[simp]
/-
**LieSubmodule.span_univ** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：span_univ : lieSpan R L (Set.univ : Set M) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `LieSubmodule.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
-/
theorem span_univ : lieSpan R L (Set.univ : Set M) = ⊤ :=
  eq_top_iff.2 <| SetLike.le_def.2 <| subset_lieSpan
/-
**LieSubmodule.lieSpan_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：lieSpan_eq_bot_iff : lieSpan R L s = ⊥ ↔ forall m in s, m = (0 : M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `LieSubmodule.lieSpan_le`：lieSpan_le {N} : lieSpan R L s <= N ↔ s subsete
q N
· 使用定理 `LieSubmodule.bot_coe`：bot_coe : ((⊥ : LieSubmodule R L M) : Set M) = {0}
· 使用定理 `Set.subset_singleton_iff`：subset_singleton_iff {α : Type*} {s : Set α} {
x : α} : s subseteq {x} ↔ forall y in s, y = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lieSpan_eq_bot_iff : lieSpan R L s = ⊥ ↔ ∀ m ∈ s, m = (0 : M) := by
  rw [_root_.eq_bot_iff, lieSpan_le, bot_coe, subset_singleton_iff]

variable {M}
/-
**LieSubmodule.span_union** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：span_union (s t : Set M) : lieSpan R L (s union t) = lieSpan R L s ⊔ lieSp
an R L t
参数：s t : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem span_union (s t : Set M) : lieSpan R L (s ∪ t) = lieSpan R L s ⊔ lieSpan R L t :=
  (LieSubmodule.gi R L M).gc.l_sup
/-
**LieSubmodule.span_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：span_iUnion {ι} (s : ι -> Set M) : lieSpan R L (⋃ i, s i) = ⨆ i, lieSpan R
 L (s i)
参数：s : ι -> Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem span_iUnion {ι} (s : ι → Set M) : lieSpan R L (⋃ i, s i) = ⨆ i, lieSpan R L (s i) :=
  (LieSubmodule.gi R L M).gc.l_iSup

/-- An induction principle for span membership. If `p` holds for 0 and all elements of `s`, and is
preserved under addition, scalar multiplication and the Lie bracket, then `p` holds for all
elements of the Lie submodule spanned by `s`. -/
@[elab_as_elim]
/-
**LieSubmodule.lieSpan_induction** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：lieSpan_induction {p : (x : M) -> x in lieSpan R L s -> Prop} (mem : foral
l (x) (h : x in s), p x (subset_lieSpan h)) (zero : p 0 (LieSubmodule.zero_mem _
)) (add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem ‹_› ‹_›)) (sm
ul : forall (a : R) (x hx), p x hx -> p (a • x) (SMulMemClass.smul_mem _ hx)) {x
} (lie : forall (x : L) (y hy), p y hy -> p (⁅x, y⁆) (LieSubmodule.lie_mem _ ‹_›
)) (hx : x in lieSpan R L s) : p x hx
参数：x : M；mem : forall (x) (h : x in s), p x (subset_lieSpan h)；zero : p 0 (LieSu
bmodule.zero_mem _)；add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (add_m
em ‹_› ‹_›)；smul : forall (a : R) (x hx), p x hx -> p (a • x) (SMulMemClass.smul
_mem _ hx)；lie : forall (x : L) (y hy), p y hy -> p (⁅x, y⁆) (LieSubmodule.lie_m
em _ ‹_›)；hx : x in lieSpan R L s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
· 使用定理 `LieSubmodule.zero_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mo
dule R M] […
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieSubmodule.lieSpan_le`：lieSpan_le {N} : lieSpan R L s <= N ↔ s subsete
q N

--- 原说明 ---
An induction principle for span membership. If `p` holds for 0 and all elements 
of `s`, and is
preserved under addition, scalar multiplication and the Lie bracket, then `p` ho
lds for all
elements of the Lie submodule spanned by `s`.
-/
theorem lieSpan_induction {p : (x : M) → x ∈ lieSpan R L s → Prop}
    (mem : ∀ (x) (h : x ∈ s), p x (subset_lieSpan h))
    (zero : p 0 (LieSubmodule.zero_mem _))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem ‹_› ‹_›))
    (smul : ∀ (a : R) (x hx), p x hx → p (a • x) (SMulMemClass.smul_mem _ hx)) {x}
    (lie : ∀ (x : L) (y hy), p y hy → p (⁅x, y⁆) (LieSubmodule.lie_mem _ ‹_›))
    (hx : x ∈ lieSpan R L s) : p x hx := by
  let p : LieSubmodule R L M :=
    { carrier := { x | ∃ hx, p x hx }
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, add _ _ _ _ hpx hpy⟩
      zero_mem' := ⟨_, zero⟩
      smul_mem' := fun r ↦ fun ⟨_, hpx⟩ ↦ ⟨_, smul r _ _ hpx⟩
      lie_mem := fun ⟨_, hpy⟩ ↦ ⟨_, lie _ _ _ hpy⟩ }
  exact lieSpan_le (N := p) |>.mpr (fun y hy ↦ ⟨subset_lieSpan hy, mem y hy⟩) hx |>.elim fun _ ↦ id
/-
**LieSubmodule.isCompactElement_lieSpan_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Lie
Submodule`。
形式化陈述：isCompactElement_lieSpan_singleton (m : M) : IsCompactElement (lieSpan R L
 {m})
参数：m : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le`：isCompactEl
ement_iff_le_of_directed_sSup_le (k : α) : IsCompactElement k ↔ forall s : Set α
, s.Nonempty -> DirectedOn (· <= ·) s -> k <= sSu…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `LieSubmodule.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_coe_sort`：nonempty_coe_sort {s : Set α} : Nonempty ↥s ↔ s.N
onempty
· 使用定理 `Submodule.coe_iSup_of_directed`：coe_iSup_of_directed {ι} [Nonempty ι] (S
 : ι -> Submodule R M) (H : Directed (· <= ·) S) : ((iSup S : Submodule R M) : S
et M) = ⋃ i, S i
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SetLike.coe_set_eq`：coe_set_eq : (p : Set B) = q ↔ p = q
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
-/
lemma isCompactElement_lieSpan_singleton (m : M) :
    IsCompactElement (lieSpan R L {m}) := by
  rw [CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le]
  intro s hne hdir hsup
  replace hsup : m ∈ (↑(sSup s) : Set M) := (SetLike.le_def.mp hsup) (subset_lieSpan rfl)
  suffices (↑(sSup s) : Set M) = ⋃ N ∈ s, ↑N by simp_all
  replace hne : Nonempty s := Set.nonempty_coe_sort.mpr hne
  have := Submodule.coe_iSup_of_directed _ hdir.directed_val
  simp_rw [← iSup_toSubmodule, Set.iUnion_coe_set, coe_toSubmodule] at this
  rw [← this, SetLike.coe_set_eq, sSup_eq_iSup, iSup_subtype]

@[simp]
/-
**LieSubmodule.sSup_image_lieSpan_singleton** 是 Mathlib 中的一个引理，位于命名空间 `LieSubmod
ule`。
形式化陈述：sSup_image_lieSpan_singleton : sSup ((fun x => lieSpan R L {x}) '' N) = N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_sSup`：mem_sSup {s : Set (Submodule R M)} {m : M} : (m in s
Sup s) ↔ forall N, (forall p in s, p <= N) -> m in N
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `LieSubmodule.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
-/
lemma sSup_image_lieSpan_singleton : sSup ((fun x ↦ lieSpan R L {x}) '' N) = N := by
  refine le_antisymm (sSup_le <| by simp) ?_
  simp_rw [← toSubmodule_le_toSubmodule, sSup_toSubmodule, Set.mem_image, SetLike.mem_coe]
  refine fun m hm ↦ Submodule.mem_sSup.mpr fun N' hN' ↦ ?_
  replace hN' : ∀ m ∈ N, lieSpan R L {m} ≤ N' := by simpa using hN'
  exact hN' _ hm (subset_lieSpan rfl)
/-
**LieSubmodule.instIsCompactlyGenerated** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`
。
形式化陈述：instIsCompactlyGenerated : IsCompactlyGenerated (LieSubmodule R L M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `LieSubmodule.isCompactElement_lieSpan_singleton`：isCompactElement_lieSpa
n_singleton (m : M) : IsCompactElement (lieSpan R L {m})
· 使用引理 `LieSubmodule.sSup_image_lieSpan_singleton`：sSup_image_lieSpan_singleton 
: sSup ((fun x => lieSpan R L {x}) '' N) = N
-/
instance instIsCompactlyGenerated : IsCompactlyGenerated (LieSubmodule R L M) :=
  ⟨fun N ↦ ⟨(fun x ↦ lieSpan R L {x}) '' N, fun _ ⟨m, _, hm⟩ ↦
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

variable (f : M →ₗ⁅R,L⁆ M') (N N₂ : LieSubmodule R L M) (N' : LieSubmodule R L M')

/-- A morphism of Lie modules `f : M → M'` pushes forward Lie submodules of `M` to Lie submodules
of `M'`. -/
/-
**LieSubmodule.map** 是 Mathlib 中的一个定义，位于命名空间 `LieSubmodule`。
形式化陈述：map : LieSubmodule R L M'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of Lie modules `f : M → M'` pushes forward Lie submodules of `M` to L
ie submodules
of `M'`.
-/
def map : LieSubmodule R L M' :=
  { (N : Submodule R M).map (f : M →ₗ[R] M') with
    lie_mem := fun {x m'} h ↦ by
      rcases h with ⟨m, hm, hfm⟩; use ⁅x, m⁆; constructor
      · apply N.lie_mem hm
      · norm_cast at hfm; simp [hfm] }
/-
**LieSubmodule.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：∀ {R : Type u} {L : Type v} {M : Type w} {M' : Type w₁} [inst : CommRing R
] [inst_1 : LieRing L]   [inst_2 : AddCommGroup M] [inst_3 : _root_.Module R M] 
[inst_4 : LieRingModule L M] [inst_5 : AddCommGroup M']   [inst_6 : _root_.Modul
e R M'] [inst_7 : LieRingModule L M'] (f : M →ₗ⁅R,L⁆ M') (N : LieSubmodule R L M
),   ↑(LieSubmodule.map f N) = ⇑f '' ↑N
参数：f : M →ₗ⁅R,L⁆ M'；N : LieSubmodule R L M；LieSubmodule.map f N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_map : (N.map f : Set M') = f '' N := rfl

@[simp]
/-
**LieSubmodule.toSubmodule_map** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：toSubmodule_map : (N.map f : Submodule R M') = (N : Submodule R M).map (f 
: M ->ₗ[R] M')
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubmodule_map : (N.map f : Submodule R M') = (N : Submodule R M).map (f : M →ₗ[R] M') :=
  rfl

/-- A morphism of Lie modules `f : M → M'` pulls back Lie submodules of `M'` to Lie submodules of
`M`. -/
/-
**LieSubmodule.comap** 是 Mathlib 中的一个定义，位于命名空间 `LieSubmodule`。
形式化陈述：comap : LieSubmodule R L M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of Lie modules `f : M → M'` pulls back Lie submodules of `M'` to Lie 
submodules of
`M`.
-/
def comap : LieSubmodule R L M :=
  { (N' : Submodule R M').comap (f : M →ₗ[R] M') with
    lie_mem := fun {x m} h ↦ by
      suffices ⁅x, f m⁆ ∈ N' by simp [this]
      apply N'.lie_mem h }

@[simp]
/-
**LieSubmodule.toSubmodule_comap** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：toSubmodule_comap : (N'.comap f : Submodule R M) = (N' : Submodule R M').c
omap (f : M ->ₗ[R] M')
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubmodule_comap :
    (N'.comap f : Submodule R M) = (N' : Submodule R M').comap (f : M →ₗ[R] M') :=
  rfl

variable {f N N₂ N'}
/-
**LieSubmodule.map_le_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：map_le_iff_le_comap : map f N <= N' ↔ N <= comap f N'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_le_iff_le_comap : map f N ≤ N' ↔ N ≤ comap f N' :=
  Set.image_subset_iff

variable (f) in
/-
**LieSubmodule.gc_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：gc_map_comap : GaloisConnection (map f) (comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.map_le_iff_le_comap`：map_le_iff_le_comap : map f N <= N' ↔ 
N <= comap f N'
-/
theorem gc_map_comap : GaloisConnection (map f) (comap f) := fun _ _ ↦ map_le_iff_le_comap
/-
**LieSubmodule.map_inf_le** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：map_inf_le : (N ⊓ N₂).map f <= N.map f ⊓ N₂.map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_inter_subset`：image_inter_subset (f : α -> β) (s t : Set α) : 
f '' (s inter t) subseteq f '' s inter f '' t
-/
theorem map_inf_le : (N ⊓ N₂).map f ≤ N.map f ⊓ N₂.map f :=
  Set.image_inter_subset f N N₂
/-
**LieSubmodule.map_inf** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：map_inf (hf : Function.Injective f) : (N ⊓ N₂).map f = N.map f ⊓ N₂.map f
参数：hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
-/
theorem map_inf (hf : Function.Injective f) :
    (N ⊓ N₂).map f = N.map f ⊓ N₂.map f :=
  SetLike.coe_injective <| Set.image_inter hf

@[simp]
/-
**LieSubmodule.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：map_sup : (N ⊔ N₂).map f = N.map f ⊔ N₂.map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `LieSubmodule.gc_map_comap`：gc_map_comap : GaloisConnection (map f) (coma
p f)
-/
theorem map_sup : (N ⊔ N₂).map f = N.map f ⊔ N₂.map f :=
  (gc_map_comap f).l_sup

@[simp]
/-
**LieSubmodule.comap_inf** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：comap_inf {N₂' : LieSubmodule R L M'} : (N' ⊓ N₂').comap f = N'.comap f ⊓ 
N₂'.comap f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_inf {N₂' : LieSubmodule R L M'} :
    (N' ⊓ N₂').comap f = N'.comap f ⊓ N₂'.comap f :=
  rfl

@[simp]
/-
**LieSubmodule.map_iSup** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：map_iSup {ι : Sort*} (N : ι -> LieSubmodule R L M) : (⨆ i, N i).map f = ⨆ 
i, (N i).map f
参数：N : ι -> LieSubmodule R L M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `LieSubmodule.gc_map_comap`：gc_map_comap : GaloisConnection (map f) (coma
p f)
-/
theorem map_iSup {ι : Sort*} (N : ι → LieSubmodule R L M) :
    (⨆ i, N i).map f = ⨆ i, (N i).map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup

@[simp]
/-
**LieSubmodule.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：mem_map (m' : M') : m' in N.map f ↔ exists m, m in N ∧ f m = m'
参数：m' : M'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_map`：mem_map {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x :
 M₂} : x in map f p ↔ exists y, y in p ∧ f y = x
-/
theorem mem_map (m' : M') : m' ∈ N.map f ↔ ∃ m, m ∈ N ∧ f m = m' :=
  Submodule.mem_map
/-
**LieSubmodule.mem_map_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：mem_map_of_mem {m : M} (h : m in N) : f m in N.map f
参数：h : m in N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem mem_map_of_mem {m : M} (h : m ∈ N) : f m ∈ N.map f :=
  Set.mem_image_of_mem _ h

@[simp]
/-
**LieSubmodule.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：mem_comap {m : M} : m in comap f N' ↔ f m in N'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap {m : M} : m ∈ comap f N' ↔ f m ∈ N' :=
  Iff.rfl
/-
**LieSubmodule.comap_incl_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：comap_incl_eq_top : N₂.comap N.incl = ⊤ ↔ N <= N₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieSubmodule.toSubmodule_comap`：toSubmodule_comap : (N'.comap f : Submod
ule R M) = (N' : Submodule R M').comap (f : M ->ₗ[R] M')
· 使用定理 `LieSubmodule.incl_coe`：incl_coe : (N.incl : N ->ₗ[R] M) = (N : Submodule
 R M).subtype
· 使用定理 `LieSubmodule.top_toSubmodule`：top_toSubmodule : ((⊤ : LieSubmodule R L M
) : Submodule R M) = ⊤
· 使用定理 `Submodule.comap_subtype_eq_top`：comap_subtype_eq_top {p p' : Submodule R
 M} : comap p.subtype p' = ⊤ ↔ p <= p'
· 使用定理 `LieSubmodule.toSubmodule_le_toSubmodule`：toSubmodule_le_toSubmodule : (N
 : Submodule R M) <= N' ↔ N <= N'
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem comap_incl_eq_top : N₂.comap N.incl = ⊤ ↔ N ≤ N₂ := by
  rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.toSubmodule_comap, LieSubmodule.incl_coe,
    LieSubmodule.top_toSubmodule, Submodule.comap_subtype_eq_top, toSubmodule_le_toSubmodule]
/-
**LieSubmodule.comap_incl_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：comap_incl_eq_bot : N₂.comap N.incl = ⊥ ↔ N ⊓ N₂ = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.disjoint_iff_comap_eq_bot`：disjoint_iff_comap_eq_bot {p q : Su
bmodule R M} : Disjoint p q ↔ comap p.subtype q = ⊥
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem comap_incl_eq_bot : N₂.comap N.incl = ⊥ ↔ N ⊓ N₂ = ⊥ := by
  simp only [← toSubmodule_inj, toSubmodule_comap, incl_coe, bot_toSubmodule,
    inf_toSubmodule]
  rw [← Submodule.disjoint_iff_comap_eq_bot, disjoint_iff]

@[gcongr, mono]
/-
**LieSubmodule.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：map_mono (h : N <= N₂) : N.map f <= N₂.map f
参数：h : N <= N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
theorem map_mono (h : N ≤ N₂) : N.map f ≤ N₂.map f :=
  Set.image_mono h
/-
**LieSubmodule.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：map_comp {M'' : Type*} [AddCommGroup M''] [Module R M''] [LieRingModule L 
M''] {g : M' ->ₗ⁅R,L⁆ M''} : N.map (g.comp f) = (N.map f).map g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_comp
    {M'' : Type*} [AddCommGroup M''] [Module R M''] [LieRingModule L M''] {g : M' →ₗ⁅R,L⁆ M''} :
    N.map (g.comp f) = (N.map f).map g :=
  SetLike.coe_injective <| by
    simp only [← Set.image_comp, coe_map, LieModuleHom.coe_comp]

@[simp]
/-
**LieSubmodule.map_id** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：map_id : N.map LieModuleHom.id = N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.ext`：ext (h : forall m, m in N ↔ m in N') : N = N'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_id : N.map LieModuleHom.id = N := by ext; simp
/-
**LieSubmodule.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：∀ {R : Type u} {L : Type v} {M : Type w} {M' : Type w₁} [inst : CommRing R
] [inst_1 : LieRing L]   [inst_2 : AddCommGroup M] [inst_3 : _root_.Module R M] 
[inst_4 : LieRingModule L M] [inst_5 : AddCommGroup M']   [inst_6 : _root_.Modul
e R M'] [inst_7 : LieRingModule L M'] {f : M →ₗ⁅R,L⁆ M'}, LieSubmodule.map f ⊥ =
 ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.ext`：ext (h : forall m, m in N ↔ m in N') : N = N'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LieModuleHom.instLinearMapClass`：∀ {R : Type u} {L : Type v} {M : Type w
} {N : Type w₁} [inst : CommRing R] [inst_1 : LieRing L]   [inst_2 : AddCommGrou
p M] [inst_3 : AddCom…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem map_bot :
    (⊥ : LieSubmodule R L M).map f = ⊥ := by
  ext m; simp [eq_comm]
/-
**LieSubmodule.map_le_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `LieSubmodule`。
形式化陈述：map_le_map_iff (hf : Function.Injective f) : N.map f <= N₂.map f ↔ N <= N₂
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_image_iff`：image_subset_image_iff {f : α -> β} (hf : In
jective f) : f '' s subseteq f '' t ↔ s subseteq t
-/
lemma map_le_map_iff (hf : Function.Injective f) :
    N.map f ≤ N₂.map f ↔ N ≤ N₂ :=
  Set.image_subset_image_iff hf
/-
**LieSubmodule.map_injective_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `LieSubmodul
e`。
形式化陈述：map_injective_of_injective (hf : Function.Injective f) : Function.Injectiv
e (map f)
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Function.Injective.image_injective`：∀ {α : Type u_1} {β : Type u_2} {f :
 α → β}, Function.Injective f → Function.Injective (Set.image f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_injective_of_injective (hf : Function.Injective f) :
    Function.Injective (map f) := fun {N N'} h ↦
  SetLike.coe_injective <| hf.image_injective <| by simp only [← coe_map, h]

/-- An injective morphism of Lie modules embeds the lattice of submodules of the domain into that
of the target. -/
/-
**LieSubmodule.mapOrderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `LieSubmodule`。
形式化陈述：{R : Type u} →   {L : Type v} →     {M : Type w} →       {M' : Type w₁} → 
        [inst : CommRing R] →           [inst_1 : LieRing L] →             [inst
_2 : AddCommGroup M] →               [inst_3 : _root_.Module R M] →             
    [inst_4 : LieRingModule L M] →                   [inst_5 : AddCommGroup M'] 
→                     [inst_6 : _root_.Module R M'] →                       [ins
t_7 : LieRingModule L M'] →                         {f : M →ₗ⁅R,L⁆ M'} → Functio
n.Injective ⇑f → LieSubmodule R L M ↪o LieSubmodule R L M'
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `LieSubmodule.map_injective_of_injective`：map_injective_of_injective (hf 
: Function.Injective f) : Function.Injective (map f)

--- 原说明 ---
An injective morphism of Lie modules embeds the lattice of submodules of the dom
ain into that
of the target.
-/
@[simps] def mapOrderEmbedding {f : M →ₗ⁅R,L⁆ M'} (hf : Function.Injective f) :
    LieSubmodule R L M ↪o LieSubmodule R L M' where
  toFun := LieSubmodule.map f
  inj' := map_injective_of_injective hf
  map_rel_iff' := Set.image_subset_image_iff hf

variable (N) in
/-- For an injective morphism of Lie modules, any Lie submodule is equivalent to its image. -/
/-
**LieSubmodule.equivMapOfInjective** 是 Mathlib 中的一个定义，位于命名空间 `LieSubmodule`。
形式化陈述：equivMapOfInjective (hf : Function.Injective f) : N ≃ₗ⁅R,L⁆ N.map f
参数：hf : Function.Injective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […

--- 原说明 ---
For an injective morphism of Lie modules, any Lie submodule is equivalent to its
 image.
-/
noncomputable def equivMapOfInjective (hf : Function.Injective f) :
    N ≃ₗ⁅R,L⁆ N.map f :=
  { Submodule.equivMapOfInjective (f : M →ₗ[R] M') hf N with
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify `invFun` explicitly this way, otherwise we'd get a type mismatch
    invFun := by exact DFunLike.coe (Submodule.equivMapOfInjective (f : M →ₗ[R] M') hf N).symm
    map_lie' := by rintro x ⟨m, hm : m ∈ N⟩; ext; exact f.map_lie x m }

/-- An equivalence of Lie modules yields an order-preserving equivalence of their lattices of Lie
Submodules. -/
/-
**LieSubmodule.orderIsoMapComap** 是 Mathlib 中的一个定义，位于命名空间 `LieSubmodule`。
形式化陈述：{R : Type u} →   {L : Type v} →     {M : Type w} →       {M' : Type w₁} → 
        [inst : CommRing R] →           [inst_1 : LieRing L] →             [inst
_2 : AddCommGroup M] →               [inst_3 : _root_.Module R M] →             
    [inst_4 : LieRingModule L M] →                   [inst_5 : AddCommGroup M'] 
→                     [inst_6 : _root_.Module R M'] →                       [ins
t_7 : LieRingModule L M'] → (M ≃ₗ⁅R,L⁆ M') → LieSubmodule R L M ≃o LieSubmodule 
R L M'
参数：M ≃ₗ⁅R,L⁆ M'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of Lie modules yields an order-preserving equivalence of their la
ttices of Lie
Submodules.
-/
@[simps] def orderIsoMapComap (e : M ≃ₗ⁅R,L⁆ M') :
    LieSubmodule R L M ≃o LieSubmodule R L M' where
  toFun := map e
  invFun := comap e
  left_inv := fun N ↦ by ext; simp
  right_inv := fun N ↦ by ext; simp [← e.eq_symm_apply]
  map_rel_iff' := fun {_ _} ↦ Set.image_subset_image_iff e.injective

end LieSubmodule


end LieSubmoduleMapAndComap

namespace LieModuleHom

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}
variable [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N]
variable (f : M →ₗ⁅R,L⁆ N)

/-- The kernel of a morphism of Lie algebras, as an ideal in the domain. -/
/-
**LieModuleHom.ker** 是 Mathlib 中的一个定义，位于命名空间 `LieModuleHom`。
形式化陈述：ker : LieSubmodule R L M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of a morphism of Lie algebras, as an ideal in the domain.
-/
def ker : LieSubmodule R L M :=
  LieSubmodule.comap f ⊥

@[simp]
/-
**LieModuleHom.ker_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：ker_toSubmodule : (f.ker : Submodule R M) = LinearMap.ker (f : M ->ₗ[R] N)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ker_toSubmodule : (f.ker : Submodule R M) = LinearMap.ker (f : M →ₗ[R] N) :=
  rfl
/-
**LieModuleHom.ker_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：ker_eq_bot : f.ker = ⊥ ↔ Function.Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieModuleHom.ker_toSubmodule`：ker_toSubmodule : (f.ker : Submodule R M) 
= LinearMap.ker (f : M ->ₗ[R] N)
· 使用定理 `LieSubmodule.bot_toSubmodule`：bot_toSubmodule : ((⊥ : LieSubmodule R L M
) : Submodule R M) = ⊥
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `LieModuleHom.coe_toLinearMap`：coe_toLinearMap (f : M ->ₗ⁅R,L⁆ N) : ((f :
 M ->ₗ[R] N) : M -> N) = f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ker_eq_bot : f.ker = ⊥ ↔ Function.Injective f := by
  rw [← LieSubmodule.toSubmodule_inj, ker_toSubmodule, LieSubmodule.bot_toSubmodule,
    LinearMap.ker_eq_bot, coe_toLinearMap]

variable {f}

@[simp]
/-
**LieModuleHom.mem_ker** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：mem_ker {m : M} : m in f.ker ↔ f m = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ker {m : M} : m ∈ f.ker ↔ f m = 0 :=
  Iff.rfl

@[simp]
/-
**LieModuleHom.ker_id** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：ker_id : (LieModuleHom.id : M ->ₗ⁅R,L⁆ M).ker = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ker_id : (LieModuleHom.id : M →ₗ⁅R,L⁆ M).ker = ⊥ :=
  rfl

@[simp]
/-
**LieModuleHom.comp_ker_incl** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：comp_ker_incl : f.comp f.ker.incl = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModuleHom.ext`：ext {f g : M ->ₗ⁅R,L⁆ N} (h : forall m, f m = g m) : f
 = g
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieModuleHom.mem_ker`：mem_ker {m : M} : m in f.ker ↔ f m = 0
-/
theorem comp_ker_incl : f.comp f.ker.incl = 0 := by ext ⟨m, hm⟩; exact mem_ker.mp hm
/-
**LieModuleHom.le_ker_iff_map** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：le_ker_iff_map (M' : LieSubmodule R L M) : M' <= f.ker ↔ LieSubmodule.map 
f M' = ⊥
参数：M' : LieSubmodule R L M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModuleHom.ker.eq_1`：∀ {R : Type u} {L : Type v} {M : Type w} {N : Typ
e w₁} [inst : CommRing R] [inst_1 : LieRing L]   [inst_2 : AddCommGroup M] [inst
_3 : _root_…
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `LieSubmodule.map_le_iff_le_comap`：map_le_iff_le_comap : map f N <= N' ↔ 
N <= comap f N'
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_ker_iff_map (M' : LieSubmodule R L M) : M' ≤ f.ker ↔ LieSubmodule.map f M' = ⊥ := by
  rw [ker, eq_bot_iff, LieSubmodule.map_le_iff_le_comap]

variable (f)

/-- The range of a morphism of Lie modules `f : M → N` is a Lie submodule of `N`.
See Note [range copy pattern]. -/
/-
**LieModuleHom.range** 是 Mathlib 中的一个定义，位于命名空间 `LieModuleHom`。
形式化陈述：range : LieSubmodule R L N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a morphism of Lie modules `f : M → N` is a Lie submodule of `N`.
See Note [range copy pattern].
-/
def range : LieSubmodule R L N :=
  (LieSubmodule.map f ⊤).copy (Set.range f) Set.image_univ.symm

@[simp]
/-
**LieModuleHom.coe_range** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：coe_range : f.range = Set.range f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_range : f.range = Set.range f :=
  rfl

@[simp]
/-
**LieModuleHom.toSubmodule_range** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：toSubmodule_range : f.range = LinearMap.range (f : M ->ₗ[R] N)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubmodule_range : f.range = LinearMap.range (f : M →ₗ[R] N) :=
  rfl

@[simp]
/-
**LieModuleHom.mem_range** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：mem_range (n : N) : n in f.range ↔ exists m, f m = n
参数：n : N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_range (n : N) : n ∈ f.range ↔ ∃ m, f m = n :=
  Iff.rfl

@[simp]
/-
**LieModuleHom.map_top** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：map_top : LieSubmodule.map f ⊤ = f.range
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.ext`：ext (h : forall m, m in N ↔ m in N') : N = N'
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
theorem map_top : LieSubmodule.map f ⊤ = f.range := by ext; simp [LieSubmodule.mem_map]
/-
**LieModuleHom.range_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：range_eq_top : f.range = ⊤ ↔ Function.Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `LieModuleHom.coe_range`：coe_range : f.range = Set.range f
· 使用定理 `LieSubmodule.top_coe`：top_coe : ((⊤ : LieSubmodule R L M) : Set M) = uni
v
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem range_eq_top : f.range = ⊤ ↔ Function.Surjective f := by
  rw [SetLike.ext'_iff, coe_range, LieSubmodule.top_coe, Set.range_eq_univ]

/-- A morphism of Lie modules `f : M → N` whose values lie in a Lie submodule `P ⊆ N` can be
restricted to a morphism of Lie modules `M → P`. -/
/-
**LieModuleHom.codRestrict** 是 Mathlib 中的一个定义，位于命名空间 `LieModuleHom`。
形式化陈述：codRestrict (P : LieSubmodule R L N) (f : M ->ₗ⁅R,L⁆ N) (h : forall m, f m
 in P) : M ->ₗ⁅R,L⁆ P where toFun
参数：P : LieSubmodule R L N；f : M ->ₗ⁅R,L⁆ N；h : forall m, f m in P。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […

--- 原说明 ---
A morphism of Lie modules `f : M → N` whose values lie in a Lie submodule `P ⊆ N
` can be
restricted to a morphism of Lie modules `M → P`.
-/
def codRestrict (P : LieSubmodule R L N) (f : M →ₗ⁅R,L⁆ N) (h : ∀ m, f m ∈ P) :
    M →ₗ⁅R,L⁆ P where
  toFun := f.toLinearMap.codRestrict P h
  __ := f.toLinearMap.codRestrict P h
  map_lie' {x m} := by ext; simp

@[simp]
/-
**LieModuleHom.codRestrict_apply** 是 Mathlib 中的一个引理，位于命名空间 `LieModuleHom`。
形式化陈述：codRestrict_apply (P : LieSubmodule R L N) (f : M ->ₗ⁅R,L⁆ N) (h : forall 
m, f m in P) (m : M) : (f.codRestrict P h m : N) = f m
参数：P : LieSubmodule R L N；f : M ->ₗ⁅R,L⁆ N；h : forall m, f m in P；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
lemma codRestrict_apply (P : LieSubmodule R L N) (f : M →ₗ⁅R,L⁆ N) (h : ∀ m, f m ∈ P) (m : M) :
    (f.codRestrict P h m : N) = f m :=
  rfl

end LieModuleHom

namespace LieSubmodule

variable {R : Type u} {L : Type v} {M : Type w}
variable [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]
variable (N : LieSubmodule R L M)

@[simp]
/-
**LieSubmodule.ker_incl** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：ker_incl : N.incl.ker = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `LieModuleHom.ker_eq_bot`：ker_eq_bot : f.ker = ⊥ ↔ Function.Injective f
· 使用定理 `LieSubmodule.injective_incl`：injective_incl : Function.Injective N.incl
-/
theorem ker_incl : N.incl.ker = ⊥ := (LieModuleHom.ker_eq_bot N.incl).mpr <| injective_incl N

@[simp]
/-
**LieSubmodule.range_incl** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：range_incl : N.incl.range = N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
-/
theorem range_incl : N.incl.range = N := by
  simp only [← toSubmodule_inj, LieModuleHom.toSubmodule_range, incl_coe]
  rw [Submodule.range_subtype]

@[simp]
/-
**LieSubmodule.comap_incl_self** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：comap_incl_self : comap N.incl N = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.comap_subtype_self`：comap_subtype_self : comap p.subtype p = ⊤
-/
theorem comap_incl_self : comap N.incl N = ⊤ := by
  simp only [← toSubmodule_inj, toSubmodule_comap, incl_coe, top_toSubmodule]
  rw [Submodule.comap_subtype_self]
/-
**LieSubmodule.map_incl_top** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：map_incl_top : (⊤ : LieSubmodule R L N).map N.incl = N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModuleHom.map_top`：map_top : LieSubmodule.map f ⊤ = f.range
· 使用定理 `LieSubmodule.range_incl`：range_incl : N.incl.range = N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_incl_top : (⊤ : LieSubmodule R L N).map N.incl = N := by simp
/-
**LieSubmodule.map_restrictLie_incl_top** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`
。
形式化陈述：map_restrictLie_incl_top [LieAlgebra R L] (H : LieSubalgebra R L) : (⊤ : L
ieSubmodule R H N).map (N.incl.restrictLie H) = N.restr H
参数：H : LieSubalgebra R L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.ext`：ext (h : forall m, m in N ↔ m in N') : N = N'
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieModuleHom.map_top`：map_top : LieSubmodule.map f ⊤ = f.range
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_restrictLie_incl_top [LieAlgebra R L] (H : LieSubalgebra R L) :
    (⊤ : LieSubmodule R H N).map (N.incl.restrictLie H) = N.restr H := by
  ext; simp

variable {N}

@[simp]
/-
**LieSubmodule.map_le_range** 是 Mathlib 中的一个引理，位于命名空间 `LieSubmodule`。
形式化陈述：map_le_range {M' : Type*} [AddCommGroup M'] [Module R M'] [LieRingModule L
 M'] (f : M ->ₗ⁅R,L⁆ M') : N.map f <= f.range
参数：f : M ->ₗ⁅R,L⁆ M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieModuleHom.map_top`：map_top : LieSubmodule.map f ⊤ = f.range
· 使用定理 `LieSubmodule.map_mono`：map_mono (h : N <= N₂) : N.map f <= N₂.map f
· 使用定理 `le_top`：le_top : a <= ⊤
-/
lemma map_le_range {M' : Type*}
    [AddCommGroup M'] [Module R M'] [LieRingModule L M'] (f : M →ₗ⁅R,L⁆ M') :
    N.map f ≤ f.range := by
  rw [← LieModuleHom.map_top]
  exact LieSubmodule.map_mono le_top

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**LieSubmodule.map_incl_lt_iff_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `LieSubmodule`。
形式化陈述：map_incl_lt_iff_lt_top {N' : LieSubmodule R L N} : N'.map (LieSubmodule.in
cl N) < N ↔ N' < ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.mapOrderEmbedding_apply`：∀ {R : Type u} {L : Type v} {M : T
ype w} {M' : Type w₁} [inst : CommRing R] [inst_1 : LieRing L]   [inst_2 : AddCo
mmGroup M] [inst_3 : _root…
· 使用定理 `LieModuleHom.map_top`：map_top : LieSubmodule.map f ⊤ = f.range
· 使用定理 `LieSubmodule.range_incl`：range_incl : N.incl.range = N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `OrderEmbedding.lt_iff_lt`：lt_iff_lt {a b} : f a < f b ↔ a < b
-/
lemma map_incl_lt_iff_lt_top {N' : LieSubmodule R L N} :
    N'.map (LieSubmodule.incl N) < N ↔ N' < ⊤ := by
  convert! (LieSubmodule.mapOrderEmbedding (f := N.incl) Subtype.coe_injective).lt_iff_lt
  simp

@[simp]
/-
**LieSubmodule.map_incl_le** 是 Mathlib 中的一个引理，位于命名空间 `LieSubmodule`。
形式化陈述：map_incl_le {N' : LieSubmodule R L N} : N'.map N.incl <= N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.map_incl_top`：map_incl_top : (⊤ : LieSubmodule R L N).map N
.incl = N
· 使用定理 `LieSubmodule.map_mono`：map_mono (h : N <= N₂) : N.map f <= N₂.map f
· 使用定理 `le_top`：le_top : a <= ⊤
-/
lemma map_incl_le {N' : LieSubmodule R L N} :
    N'.map N.incl ≤ N := by
  conv_rhs => rw [← N.map_incl_top]
  exact LieSubmodule.map_mono le_top

end LieSubmodule

section TopEquiv

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L]

variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M]

/-- The natural equivalence between the 'top' Lie submodule and the enclosing Lie module. -/
/-
**LieModuleEquiv.ofTop** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LieModuleEquiv.ofTop : (⊤ : LieSubmodule R L M) ≃ₗ⁅R,L⁆ M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […

--- 原说明 ---
The natural equivalence between the 'top' Lie submodule and the enclosing Lie mo
dule.
-/
def LieModuleEquiv.ofTop : (⊤ : LieSubmodule R L M) ≃ₗ⁅R,L⁆ M :=
  { LinearEquiv.ofTop ⊤ rfl with
    map_lie' := rfl }

variable {R L}
/-
**LieModuleEquiv.ofTop_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LieModuleEquiv.ofTop_apply (x : (⊤ : LieSubmodule R L M)) : LieModuleEquiv
.ofTop R L M x = x
参数：x : (⊤ : LieSubmodule R L M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
lemma LieModuleEquiv.ofTop_apply (x : (⊤ : LieSubmodule R L M)) :
    LieModuleEquiv.ofTop R L M x = x :=
  rfl
/-
**LieModuleEquiv.range_coe** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleEquiv`。
形式化陈述：∀ {R : Type u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] (M : 
Type u_1) [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] [inst_4 : Lie
RingModule L M] {M' : Type u_2} [inst_5 : AddCommGroup M']   [inst_6 : _root_.Mo
dule R M'] [inst_7 : LieRingModule L M'] (e : M ≃ₗ⁅R,L⁆ M'), e.range = ⊤
参数：M : Type u_1；e : M ≃ₗ⁅R,L⁆ M'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModuleHom.range_eq_top`：range_eq_top : f.range = ⊤ ↔ Function.Surject
ive f
· 使用定理 `LieModuleEquiv.surjective`：surjective (e : M ≃ₗ⁅R,L⁆ N) : Function.Surje
ctive e
-/
@[simp] lemma LieModuleEquiv.range_coe {M' : Type*}
    [AddCommGroup M'] [Module R M'] [LieRingModule L M'] (e : M ≃ₗ⁅R,L⁆ M') :
    LieModuleHom.range (e : M →ₗ⁅R,L⁆ M') = ⊤ := by
  rw [LieModuleHom.range_eq_top]
  exact e.surjective

variable [LieAlgebra R L] [LieModule R L M]

/-- The natural equivalence between the 'top' Lie subalgebra and the enclosing Lie algebra.

This is the Lie subalgebra version of `Submodule.topEquiv`. -/
/-
**LieSubalgebra.topEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LieSubalgebra.topEquiv : (⊤ : LieSubalgebra R L) ≃ₗ⁅R⁆ L
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
The natural equivalence between the 'top' Lie subalgebra and the enclosing Lie a
lgebra.

This is the Lie subalgebra version of `Submodule.topEquiv`.
-/
def LieSubalgebra.topEquiv : (⊤ : LieSubalgebra R L) ≃ₗ⁅R⁆ L :=
  { (⊤ : LieSubalgebra R L).incl with
    invFun := fun x ↦ ⟨x, Set.mem_univ x⟩ }

@[simp]
/-
**LieSubalgebra.topEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieSubalgebra.topEquiv_apply (x : (⊤ : LieSubalgebra R L)) : LieSubalgebra
.topEquiv x = x
参数：x : (⊤ : LieSubalgebra R L)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LieSubalgebra.topEquiv_apply (x : (⊤ : LieSubalgebra R L)) : LieSubalgebra.topEquiv x = x :=
  rfl

end TopEquiv

