/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!

# Relative rank of subfields and intermediate fields

This file contains basics about the relative rank of subfields and intermediate fields.

## Main definitions

- `Subfield.relrank A B`, `IntermediateField.relrank A B`:
  defined to be `[B : A ⊓ B]` as a `Cardinal`.
  In particular, when `A ≤ B` it is `[B : A]`, the degree of the field extension `B / A`.
  This is similar to `Subgroup.relIndex` but it is `Cardinal` valued.

- `Subfield.relfinrank A B`, `IntermediateField.relfinrank A B`:
  the `Nat` version of `Subfield.relrank A B` and `IntermediateField.relrank A B`, respectively.
  If `B / A ⊓ B` is an infinite extension, then it is zero.
  This is similar to `Subgroup.relIndex`.

-/

@[expose] public section

open Module Cardinal

universe u v w

namespace Subfield

variable {E : Type v} [Field E] {L : Type w} [Field L]

variable (A B C : Subfield E)

/-- `Subfield.relrank A B` is defined to be `[B : A ⊓ B]` as a `Cardinal`, in particular,
when `A ≤ B` it is `[B : A]`, the degree of the field extension `B / A`.
This is similar to `Subgroup.relIndex` but it is `Cardinal` valued. -/
/-
**Subfield.relrank** 是 Mathlib 中的一个定义，位于命名空间 `Subfield`。
形式化陈述：relrank
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Subfield.relrank A B` is defined to be `[B : A ⊓ B]` as a `Cardinal`, in partic
ular,
when `A ≤ B` it is `[B : A]`, the degree of the field extension `B / A`.
This is similar to `Subgroup.relIndex` but it is `Cardinal` valued.
-/
noncomputable def relrank := Module.rank ↥(A ⊓ B) (extendScalars (inf_le_right : A ⊓ B ≤ B))

/-- The `Nat` version of `Subfield.relrank`.
If `B / A ⊓ B` is an infinite extension, then it is zero. -/
/-
**Subfield.relfinrank** 是 Mathlib 中的一个定义，位于命名空间 `Subfield`。
形式化陈述：relfinrank
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Nat` version of `Subfield.relrank`.
If `B / A ⊓ B` is an infinite extension, then it is zero.
-/
noncomputable def relfinrank := finrank ↥(A ⊓ B) (extendScalars (inf_le_right : A ⊓ B ≤ B))
/-
**Subfield.relfinrank_eq_toNat_relrank** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relfinrank_eq_toNat_relrank : relfinrank A B = toNat (relrank A B)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem relfinrank_eq_toNat_relrank : relfinrank A B = toNat (relrank A B) := rfl

variable {A B C}
/-
**Subfield.relrank_eq_of_inf_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) : relrank A C = relrank B C
参数：h : A ⊓ C = B ⊓ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
-/
theorem relrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) : relrank A C = relrank B C := by
  simp_rw [relrank]
  congr!
/-
**Subfield.relfinrank_eq_of_inf_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relfinrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) : relfinrank A C = relfinrank 
B C
参数：h : A ⊓ C = B ⊓ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subfield.relrank_eq_of_inf_eq`：relrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) 
: relrank A C = relrank B C
-/
theorem relfinrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) : relfinrank A C = relfinrank B C :=
  congr(toNat $(relrank_eq_of_inf_eq h))

/-- If `A ≤ B`, then `Subfield.relrank A B` is `[B : A]`. -/
/-
**Subfield.relrank_eq_rank_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relrank_eq_rank_of_le (h : A <= B) : relrank A B = Module.rank A (extendSc
alars h)
参数：h : A <= B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subfield.relrank.eq_1`：∀ {E : Type v} [inst : Field E] (A B : Subfield E
), A.relrank B = Module.rank ↥(A ⊓ B) ↥(Subfield.extendScalars ⋯)
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K

--- 原说明 ---
If `A ≤ B`, then `Subfield.relrank A B` is `[B : A]`.
-/
theorem relrank_eq_rank_of_le (h : A ≤ B) : relrank A B = Module.rank A (extendScalars h) := by
  rw [relrank]
  have := inf_of_le_left h
  congr!

/-- If `A ≤ B`, then `Subfield.relfinrank A B` is `[B : A]`. -/
/-
**Subfield.relfinrank_eq_finrank_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relfinrank_eq_finrank_of_le (h : A <= B) : relfinrank A B = finrank A (ext
endScalars h)
参数：h : A <= B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subfield.relrank_eq_rank_of_le`：relrank_eq_rank_of_le (h : A <= B) : rel
rank A B = Module.rank A (extendScalars h)

--- 原说明 ---
If `A ≤ B`, then `Subfield.relfinrank A B` is `[B : A]`.
-/
theorem relfinrank_eq_finrank_of_le (h : A ≤ B) : relfinrank A B = finrank A (extendScalars h) :=
  congr(toNat $(relrank_eq_rank_of_le h))

variable (A B C)
/-
**Subfield.inf_relrank_right** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：inf_relrank_right : relrank (A ⊓ B) B = relrank A B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.relrank_eq_rank_of_le`：relrank_eq_rank_of_le (h : A <= B) : rel
rank A B = Module.rank A (extendScalars h)
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem inf_relrank_right : relrank (A ⊓ B) B = relrank A B :=
  relrank_eq_rank_of_le (inf_le_right : A ⊓ B ≤ B)
/-
**Subfield.inf_relfinrank_right** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：inf_relfinrank_right : relfinrank (A ⊓ B) B = relfinrank A B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subfield.inf_relrank_right`：inf_relrank_right : relrank (A ⊓ B) B = relr
ank A B
-/
theorem inf_relfinrank_right : relfinrank (A ⊓ B) B = relfinrank A B :=
  congr(toNat $(inf_relrank_right A B))
/-
**Subfield.inf_relrank_left** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：inf_relrank_left : relrank (A ⊓ B) A = relrank B A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Subfield.inf_relrank_right`：inf_relrank_right : relrank (A ⊓ B) B = relr
ank A B
-/
theorem inf_relrank_left : relrank (A ⊓ B) A = relrank B A := by
  rw [inf_comm, inf_relrank_right]
/-
**Subfield.inf_relfinrank_left** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：inf_relfinrank_left : relfinrank (A ⊓ B) A = relfinrank B A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subfield.inf_relrank_left`：inf_relrank_left : relrank (A ⊓ B) A = relran
k B A
-/
theorem inf_relfinrank_left : relfinrank (A ⊓ B) A = relfinrank B A :=
  congr(toNat $(inf_relrank_left A B))

@[simp]
/-
**Subfield.relrank_self** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relrank_self : relrank A A = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subfield.relrank_eq_rank_of_le`：relrank_eq_rank_of_le (h : A <= B) : rel
rank A B = Module.rank A (extendScalars h)
· 使用定理 `Subfield.extendScalars_self`：extendScalars_self : extendScalars (le_refl
 F) = ⊥
· 使用定理 `IntermediateField.rank_bot`：∀ {F : Type u_1} [inst : Field F] {E : Type 
u_2} [inst_1 : Field E] [inst_2 : Algebra F E], Module.rank F ↥⊥ = 1
-/
theorem relrank_self : relrank A A = 1 := by
  rw [relrank_eq_rank_of_le (le_refl A), extendScalars_self, IntermediateField.rank_bot]

@[simp]
/-
**Subfield.relfinrank_self** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relfinrank_self : relfinrank A A = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subfield.relrank_self`：relrank_self : relrank A A = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem relfinrank_self : relfinrank A A = 1 := by
  simp [relfinrank_eq_toNat_relrank]

variable {A B}
/-
**Subfield.relrank_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relrank_eq_one_iff : relrank A B = 1 ↔ B <= A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subfield.relrank.eq_1`：∀ {E : Type v} [inst : Field E] (A B : Subfield E
), A.relrank B = Module.rank ↥(A ⊓ B) ↥(Subfield.extendScalars ⋯)
· 使用定理 `IntermediateField.rank_eq_one_iff`：rank_eq_one_iff : Module.rank F K = 1
 ↔ K = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.toSubfield_inj`：toSubfield_inj : F.toSubfield = E.toSu
bfield ↔ F = E
· 使用定理 `Subfield.extendScalars_toSubfield`：extendScalars_toSubfield : (extendSca
lars h).toSubfield = E
· 使用定理 `IntermediateField.bot_toSubfield`：bot_toSubfield : (⊥ : IntermediateFiel
d F E).toSubfield = (algebraMap F E).fieldRange
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用定理 `Subfield.algebraMap_ofSubfield`：algebraMap_ofSubfield : algebraMap s K =
 s.subtype
· 使用定理 `Subfield.fieldRange_subtype`：fieldRange_subtype (s : Subfield K) : s.sub
type.fieldRange = s
· 使用定理 `right_eq_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b = a 
⊓ b ↔ b ≤ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem relrank_eq_one_iff : relrank A B = 1 ↔ B ≤ A := by
  rw [relrank, IntermediateField.rank_eq_one_iff, ← IntermediateField.toSubfield_inj,
    extendScalars_toSubfield, IntermediateField.bot_toSubfield, algebraMap_ofSubfield,
    fieldRange_subtype, right_eq_inf]
/-
**Subfield.relfinrank_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relfinrank_eq_one_iff : relfinrank A B = 1 ↔ B <= A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subfield.relfinrank_eq_toNat_relrank`：relfinrank_eq_toNat_relrank : relf
inrank A B = toNat (relrank A B)
· 使用定理 `Cardinal.toNat_eq_one`：toNat_eq_one : toNat c = 1 ↔ c = 1
· 使用定理 `Subfield.relrank_eq_one_iff`：relrank_eq_one_iff : relrank A B = 1 ↔ B <=
 A
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem relfinrank_eq_one_iff : relfinrank A B = 1 ↔ B ≤ A := by
  rw [relfinrank_eq_toNat_relrank, toNat_eq_one, relrank_eq_one_iff]

alias ⟨_, relrank_eq_one_of_le⟩ := relrank_eq_one_iff

alias ⟨_, relfinrank_eq_one_of_le⟩ := relfinrank_eq_one_iff
/-
**Subfield.relrank_mul_rank_top** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relrank_mul_rank_top (h : A <= B) : relrank A B * Module.rank B E = Module
.rank A E
参数：h : A <= B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subfield.relrank_eq_rank_of_le`：relrank_eq_rank_of_le (h : A <= B) : rel
rank A B = Module.rank A (extendScalars h)
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `rank_mul_rank`：rank_mul_rank (A : Type v) [AddCommMonoid A] [Module K A]
 [Module F A] [IsScalarTower F K A] [Module.Free K A] : Module.rank F K * Module
.ra…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
-/
theorem relrank_mul_rank_top (h : A ≤ B) : relrank A B * Module.rank B E = Module.rank A E := by
  rw [relrank_eq_rank_of_le h]
  let : Algebra A B := (inclusion h).toAlgebra
  have : IsScalarTower A B E := IsScalarTower.of_algebraMap_eq' rfl
  exact rank_mul_rank A B E
/-
**Subfield.relfinrank_mul_finrank_top** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relfinrank_mul_finrank_top (h : A <= B) : relfinrank A B * finrank B E = f
inrank A E
参数：h : A <= B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Subfield.relrank_mul_rank_top`：relrank_mul_rank_top (h : A <= B) : relra
nk A B * Module.rank B E = Module.rank A E
-/
theorem relfinrank_mul_finrank_top (h : A ≤ B) : relfinrank A B * finrank B E = finrank A E := by
  simpa using! congr(toNat $(relrank_mul_rank_top h))

variable (A B)

@[simp]
/-
**Subfield.relrank_top_left** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relrank_top_left : relrank ⊤ A = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.relrank_eq_one_of_le`：∀ {E : Type v} [inst : Field E] {A B : Su
bfield E}, B ≤ A → A.relrank B = 1
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem relrank_top_left : relrank ⊤ A = 1 := relrank_eq_one_of_le le_top

@[simp]
/-
**Subfield.relfinrank_top_left** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relfinrank_top_left : relfinrank ⊤ A = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.relfinrank_eq_one_of_le`：∀ {E : Type v} [inst : Field E] {A B :
 Subfield E}, B ≤ A → A.relfinrank B = 1
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem relfinrank_top_left : relfinrank ⊤ A = 1 := relfinrank_eq_one_of_le le_top

@[simp]
/-
**Subfield.relrank_top_right** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relrank_top_right : relrank A ⊤ = Module.rank A E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subfield.relrank_eq_rank_of_le`：relrank_eq_rank_of_le (h : A <= B) : rel
rank A B = Module.rank A (extendScalars h)
· 使用定理 `Subfield.extendScalars_top`：extendScalars_top : extendScalars (le_top : 
F <= ⊤) = ⊤
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁
-/
theorem relrank_top_right : relrank A ⊤ = Module.rank A E := by
  rw [relrank_eq_rank_of_le (show A ≤ ⊤ from le_top), extendScalars_top,
    IntermediateField.topEquiv.toLinearEquiv.rank_eq]

@[simp]
/-
**Subfield.relfinrank_top_right** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relfinrank_top_right : relfinrank A ⊤ = finrank A E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subfield.relrank_top_right`：relrank_top_right : relrank A ⊤ = Module.ran
k A E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem relfinrank_top_right : relfinrank A ⊤ = finrank A E := by
  simp [relfinrank_eq_toNat_relrank, finrank]
/-
**Subfield.lift_relrank_map_map** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：lift_relrank_map_map (f : E ->+* L) : lift.{v} (relrank (A.map f) (B.map f
)) = lift.{w} (relrank A B)
参数：f : E ->+* L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.lift_rank_eq_of_equiv_equiv`：lift_rank_eq_of_equiv_equiv (i : R 
≃+* R') (j : S ≃+* S') (hc : (algebraMap R' S').comp i.toRingHom = j.toRingHom.c
omp (algebraMap R S)) : l…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subfield.map_inf`：map_inf (s t : Subfield K) (f : K ->+* L) : (s ⊓ t).ma
p f = s.map f ⊓ t.map f
-/
theorem lift_relrank_map_map (f : E →+* L) :
    lift.{v} (relrank (A.map f) (B.map f)) = lift.{w} (relrank A B) :=
  -- typeclass inference is slow
  .symm <| Algebra.lift_rank_eq_of_equiv_equiv (((A ⊓ B).equivMapOfInjective f f.injective).trans
    <| .subringCongr <| by rw [← map_inf]; rfl) (B.equivMapOfInjective f f.injective) rfl
/-
**Subfield.relrank_map_map** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relrank_map_map {L : Type v} [Field L] (f : E ->+* L) : relrank (A.map f) 
(B.map f) = relrank A B
参数：f : E ->+* L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Subfield.lift_relrank_map_map`：lift_relrank_map_map (f : E ->+* L) : lif
t.{v} (relrank (A.map f) (B.map f)) = lift.{w} (relrank A B)
-/
theorem relrank_map_map {L : Type v} [Field L] (f : E →+* L) :
    relrank (A.map f) (B.map f) = relrank A B := by
  simpa only [lift_id] using lift_relrank_map_map A B f
/-
**Subfield.lift_relrank_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：lift_relrank_comap (f : L ->+* E) (B : Subfield L) : lift.{v} (relrank (A.
comap f) B) = lift.{w} (relrank A (B.map f))
参数：f : L ->+* E；B : Subfield L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subfield.lift_relrank_map_map`：lift_relrank_map_map (f : E ->+* L) : lif
t.{v} (relrank (A.map f) (B.map f)) = lift.{w} (relrank A B)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subfield.relrank_eq_of_inf_eq`：relrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) 
: relrank A C = relrank B C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subfield.map_comap_eq`：map_comap_eq (f : K ->+* L) (s : Subfield L) : (s
.comap f).map f = s ⊓ f.fieldRange
· 使用定理 `RingHom.fieldRange_eq_map`：fieldRange_eq_map : f.fieldRange = Subfield.m
ap f ⊤
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `Subfield.map_inf`：map_inf (s t : Subfield K) (f : K ->+* L) : (s ⊓ t).ma
p f = s.map f ⊓ t.map f
· 使用定理 `top_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊓ a = a
-/
theorem lift_relrank_comap (f : L →+* E) (B : Subfield L) :
    lift.{v} (relrank (A.comap f) B) = lift.{w} (relrank A (B.map f)) :=
  (lift_relrank_map_map _ _ f).symm.trans <| congr_arg lift <| relrank_eq_of_inf_eq <| by
    rw [map_comap_eq, f.fieldRange_eq_map, inf_assoc, ← map_inf, top_inf_eq]
/-
**Subfield.relrank_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relrank_comap {L : Type v} [Field L] (f : L ->+* E) (B : Subfield L) : rel
rank (A.comap f) B = relrank A (B.map f)
参数：f : L ->+* E；B : Subfield L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Subfield.lift_relrank_comap`：lift_relrank_comap (f : L ->+* E) (B : Subf
ield L) : lift.{v} (relrank (A.comap f) B) = lift.{w} (relrank A (B.map f))
-/
theorem relrank_comap {L : Type v} [Field L] (f : L →+* E)
    (B : Subfield L) : relrank (A.comap f) B = relrank A (B.map f) := by
  simpa only [lift_id] using A.lift_relrank_comap f B
/-
**Subfield.relfinrank_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relfinrank_comap (f : L ->+* E) (B : Subfield L) : relfinrank (A.comap f) 
B = relfinrank A (B.map f)
参数：f : L ->+* E；B : Subfield L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `Subfield.lift_relrank_comap`：lift_relrank_comap (f : L ->+* E) (B : Subf
ield L) : lift.{v} (relrank (A.comap f) B) = lift.{w} (relrank A (B.map f))
-/
theorem relfinrank_comap (f : L →+* E) (B : Subfield L) :
    relfinrank (A.comap f) B = relfinrank A (B.map f) := by
  simpa using! congr(toNat $(lift_relrank_comap A f B))
/-
**Subfield.lift_rank_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：lift_rank_comap (f : L ->+* E) : lift.{v} (Module.rank (A.comap f) L) = li
ft.{w} (relrank A f.fieldRange)
参数：f : L ->+* E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subfield.relrank_top_right`：relrank_top_right : relrank A ⊤ = Module.ran
k A E
· 使用定理 `Subfield.lift_relrank_comap`：lift_relrank_comap (f : L ->+* E) (B : Subf
ield L) : lift.{v} (relrank (A.comap f) B) = lift.{w} (relrank A (B.map f))
-/
theorem lift_rank_comap (f : L →+* E) :
    lift.{v} (Module.rank (A.comap f) L) = lift.{w} (relrank A f.fieldRange) := by
  simpa only [relrank_top_right, ← RingHom.fieldRange_eq_map] using lift_relrank_comap A f ⊤
/-
**Subfield.rank_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：rank_comap {L : Type v} [Field L] (f : L ->+* E) : Module.rank (A.comap f)
 L = relrank A f.fieldRange
参数：f : L ->+* E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Subfield.lift_rank_comap`：lift_rank_comap (f : L ->+* E) : lift.{v} (Mod
ule.rank (A.comap f) L) = lift.{w} (relrank A f.fieldRange)
-/
theorem rank_comap {L : Type v} [Field L] (f : L →+* E) :
    Module.rank (A.comap f) L = relrank A f.fieldRange := by
  simpa only [lift_id] using A.lift_rank_comap f
/-
**Subfield.finrank_comap** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：finrank_comap (f : L ->+* E) : finrank (A.comap f) L = relfinrank A f.fiel
dRange
参数：f : L ->+* E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `Subfield.lift_rank_comap`：lift_rank_comap (f : L ->+* E) : lift.{v} (Mod
ule.rank (A.comap f) L) = lift.{w} (relrank A f.fieldRange)
-/
theorem finrank_comap (f : L →+* E) : finrank (A.comap f) L = relfinrank A f.fieldRange := by
  simpa using! congr(toNat $(lift_rank_comap A f))
/-
**Subfield.relfinrank_map_map** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relfinrank_map_map (f : E ->+* L) : relfinrank (A.map f) (B.map f) = relfi
nrank A B
参数：f : E ->+* L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `Subfield.lift_relrank_map_map`：lift_relrank_map_map (f : E ->+* L) : lif
t.{v} (relrank (A.map f) (B.map f)) = lift.{w} (relrank A B)
-/
theorem relfinrank_map_map (f : E →+* L) :
    relfinrank (A.map f) (B.map f) = relfinrank A B := by
  simpa using! congr(toNat $(lift_relrank_map_map A B f))
/-
**Subfield.lift_relrank_comap_comap_eq_lift_relrank_inf** 是 Mathlib 中的一个定理，位于命名空
间 `Subfield`。
形式化陈述：lift_relrank_comap_comap_eq_lift_relrank_inf (f : L ->+* E) : lift.{v} (re
lrank (A.comap f) (B.comap f)) = lift.{w} (relrank A (B ⊓ f.fieldRange))
参数：f : L ->+* E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subfield.lift_relrank_map_map`：lift_relrank_map_map (f : E ->+* L) : lif
t.{v} (relrank (A.map f) (B.map f)) = lift.{w} (relrank A B)
· 使用定理 `Subfield.map_comap_eq`：map_comap_eq (f : K ->+* L) (s : Subfield L) : (s
.comap f).map f = s ⊓ f.fieldRange
· 使用定理 `Subfield.relrank_eq_of_inf_eq`：relrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) 
: relrank A C = relrank B C
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `inf_left_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓
 (b ⊓ c) = b ⊓ (a ⊓ c)
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem lift_relrank_comap_comap_eq_lift_relrank_inf (f : L →+* E) :
    lift.{v} (relrank (A.comap f) (B.comap f)) =
    lift.{w} (relrank A (B ⊓ f.fieldRange)) := by
  conv_lhs => rw [← lift_relrank_map_map _ _ f, map_comap_eq, map_comap_eq]
  congr 1
  apply relrank_eq_of_inf_eq
  rw [inf_assoc, inf_left_comm _ B, inf_of_le_left (le_refl _)]
/-
**Subfield.relrank_comap_comap_eq_relrank_inf** 是 Mathlib 中的一个定理，位于命名空间 `Subfiel
d`。
形式化陈述：relrank_comap_comap_eq_relrank_inf {L : Type v} [Field L] (f : L ->+* E) :
 relrank (A.comap f) (B.comap f) = relrank A (B ⊓ f.fieldRange)
参数：f : L ->+* E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Subfield.lift_relrank_comap_comap_eq_lift_relrank_inf`：lift_relrank_coma
p_comap_eq_lift_relrank_inf (f : L ->+* E) : lift.{v} (relrank (A.comap f) (B.co
map f)) = lift.{w} (relrank A (B ⊓ f.fieldR…
-/
theorem relrank_comap_comap_eq_relrank_inf
    {L : Type v} [Field L] (f : L →+* E) :
    relrank (A.comap f) (B.comap f) = relrank A (B ⊓ f.fieldRange) := by
  simpa only [lift_id] using lift_relrank_comap_comap_eq_lift_relrank_inf A B f
/-
**Subfield.relfinrank_comap_comap_eq_relfinrank_inf** 是 Mathlib 中的一个定理，位于命名空间 `S
ubfield`。
形式化陈述：relfinrank_comap_comap_eq_relfinrank_inf (f : L ->+* E) : relfinrank (A.co
map f) (B.comap f) = relfinrank A (B ⊓ f.fieldRange)
参数：f : L ->+* E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `Subfield.lift_relrank_comap_comap_eq_lift_relrank_inf`：lift_relrank_coma
p_comap_eq_lift_relrank_inf (f : L ->+* E) : lift.{v} (relrank (A.comap f) (B.co
map f)) = lift.{w} (relrank A (B ⊓ f.fieldR…
-/
theorem relfinrank_comap_comap_eq_relfinrank_inf (f : L →+* E) :
    relfinrank (A.comap f) (B.comap f) = relfinrank A (B ⊓ f.fieldRange) := by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_inf A B f))
/-
**Subfield.lift_relrank_comap_comap_eq_lift_relrank_of_le** 是 Mathlib 中的一个定理，位于命
名空间 `Subfield`。
形式化陈述：lift_relrank_comap_comap_eq_lift_relrank_of_le (f : L ->+* E) (h : B <= f.
fieldRange) : lift.{v} (relrank (A.comap f) (B.comap f)) = lift.{w} (relrank A B
)
参数：f : L ->+* E；h : B <= f.fieldRange。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `Subfield.lift_relrank_comap_comap_eq_lift_relrank_inf`：lift_relrank_coma
p_comap_eq_lift_relrank_inf (f : L ->+* E) : lift.{v} (relrank (A.comap f) (B.co
map f)) = lift.{w} (relrank A (B ⊓ f.fieldR…
-/
theorem lift_relrank_comap_comap_eq_lift_relrank_of_le (f : L →+* E) (h : B ≤ f.fieldRange) :
    lift.{v} (relrank (A.comap f) (B.comap f)) =
    lift.{w} (relrank A B) := by
  simpa only [inf_of_le_left h] using lift_relrank_comap_comap_eq_lift_relrank_inf A B f
/-
**Subfield.relrank_comap_comap_eq_relrank_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Subfi
eld`。
形式化陈述：relrank_comap_comap_eq_relrank_of_le {L : Type v} [Field L] (f : L ->+* E)
 (h : B <= f.fieldRange) : relrank (A.comap f) (B.comap f) = relrank A B
参数：f : L ->+* E；h : B <= f.fieldRange。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Subfield.lift_relrank_comap_comap_eq_lift_relrank_of_le`：lift_relrank_co
map_comap_eq_lift_relrank_of_le (f : L ->+* E) (h : B <= f.fieldRange) : lift.{v
} (relrank (A.comap f) (B.comap f)) = lift.{w…
-/
theorem relrank_comap_comap_eq_relrank_of_le
    {L : Type v} [Field L] (f : L →+* E) (h : B ≤ f.fieldRange) :
    relrank (A.comap f) (B.comap f) = relrank A B := by
  simpa only [lift_id] using lift_relrank_comap_comap_eq_lift_relrank_of_le A B f h
/-
**Subfield.relfinrank_comap_comap_eq_relfinrank_of_le** 是 Mathlib 中的一个定理，位于命名空间 
`Subfield`。
形式化陈述：relfinrank_comap_comap_eq_relfinrank_of_le (f : L ->+* E) (h : B <= f.fiel
dRange) : relfinrank (A.comap f) (B.comap f) = relfinrank A B
参数：f : L ->+* E；h : B <= f.fieldRange。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `Subfield.lift_relrank_comap_comap_eq_lift_relrank_of_le`：lift_relrank_co
map_comap_eq_lift_relrank_of_le (f : L ->+* E) (h : B <= f.fieldRange) : lift.{v
} (relrank (A.comap f) (B.comap f)) = lift.{w…
-/
theorem relfinrank_comap_comap_eq_relfinrank_of_le (f : L →+* E) (h : B ≤ f.fieldRange) :
    relfinrank (A.comap f) (B.comap f) = relfinrank A B := by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_of_le A B f h))
/-
**Subfield.lift_relrank_comap_comap_eq_lift_relrank_of_surjective** 是 Mathlib 中的
一个定理，位于命名空间 `Subfield`。
形式化陈述：lift_relrank_comap_comap_eq_lift_relrank_of_surjective (f : L ->+* E) (h :
 Function.Surjective f) : lift.{v} (relrank (A.comap f) (B.comap f)) = lift.{w} 
(relrank A B)
参数：f : L ->+* E；h : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.lift_relrank_comap_comap_eq_lift_relrank_of_le`：lift_relrank_co
map_comap_eq_lift_relrank_of_le (f : L ->+* E) (h : B <= f.fieldRange) : lift.{v
} (relrank (A.comap f) (B.comap f)) = lift.{w…
-/
theorem lift_relrank_comap_comap_eq_lift_relrank_of_surjective
    (f : L →+* E) (h : Function.Surjective f) :
    lift.{v} (relrank (A.comap f) (B.comap f)) =
    lift.{w} (relrank A B) :=
  lift_relrank_comap_comap_eq_lift_relrank_of_le A B f fun x _ ↦ h x
/-
**Subfield.relrank_comap_comap_eq_relrank_of_surjective** 是 Mathlib 中的一个定理，位于命名空
间 `Subfield`。
形式化陈述：relrank_comap_comap_eq_relrank_of_surjective {L : Type v} [Field L] (f : L
 ->+* E) (h : Function.Surjective f) : relrank (A.comap f) (B.comap f) = relrank
 A B
参数：f : L ->+* E；h : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Subfield.lift_relrank_comap_comap_eq_lift_relrank_of_surjective`：lift_re
lrank_comap_comap_eq_lift_relrank_of_surjective (f : L ->+* E) (h : Function.Sur
jective f) : lift.{v} (relrank (A.comap f) (B.comap f…
-/
theorem relrank_comap_comap_eq_relrank_of_surjective
    {L : Type v} [Field L] (f : L →+* E) (h : Function.Surjective f) :
    relrank (A.comap f) (B.comap f) = relrank A B := by
  simpa using lift_relrank_comap_comap_eq_lift_relrank_of_surjective A B f h
/-
**Subfield.relfinrank_comap_comap_eq_relfinrank_of_surjective** 是 Mathlib 中的一个定理
，位于命名空间 `Subfield`。
形式化陈述：relfinrank_comap_comap_eq_relfinrank_of_surjective (f : L ->+* E) (h : Fun
ction.Surjective f) : relfinrank (A.comap f) (B.comap f) = relfinrank A B
参数：f : L ->+* E；h : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `Subfield.lift_relrank_comap_comap_eq_lift_relrank_of_surjective`：lift_re
lrank_comap_comap_eq_lift_relrank_of_surjective (f : L ->+* E) (h : Function.Sur
jective f) : lift.{v} (relrank (A.comap f) (B.comap f…
-/
theorem relfinrank_comap_comap_eq_relfinrank_of_surjective
    (f : L →+* E) (h : Function.Surjective f) :
    relfinrank (A.comap f) (B.comap f) = relfinrank A B := by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_of_surjective A B f h))

variable {A B} in
/-
**Subfield.relrank_dvd_rank_top_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relrank_dvd_rank_top_of_le (h : A <= B) : relrank A B ∣ Module.rank A E
参数：h : A <= B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_of_mul_right_eq`：∀ {α : Type u_1} [inst : Semigroup α] {a b : α} (c 
: α), a * c = b → a ∣ b
· 使用定理 `Subfield.relrank_mul_rank_top`：relrank_mul_rank_top (h : A <= B) : relra
nk A B * Module.rank B E = Module.rank A E
-/
theorem relrank_dvd_rank_top_of_le (h : A ≤ B) : relrank A B ∣ Module.rank A E :=
  dvd_of_mul_right_eq _ (relrank_mul_rank_top h)

variable {A B} in
/-
**Subfield.relfinrank_dvd_finrank_top_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`
。
形式化陈述：relfinrank_dvd_finrank_top_of_le (h : A <= B) : relfinrank A B ∣ finrank A
 E
参数：h : A <= B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_of_mul_right_eq`：∀ {α : Type u_1} [inst : Semigroup α] {a b : α} (c 
: α), a * c = b → a ∣ b
· 使用定理 `Subfield.relfinrank_mul_finrank_top`：relfinrank_mul_finrank_top (h : A <
= B) : relfinrank A B * finrank B E = finrank A E
-/
theorem relfinrank_dvd_finrank_top_of_le (h : A ≤ B) : relfinrank A B ∣ finrank A E :=
  dvd_of_mul_right_eq _ (relfinrank_mul_finrank_top h)

variable {A B C} in
/-
**Subfield.relrank_mul_relrank** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relrank_mul_relrank (h1 : A <= B) (h2 : B <= C) : relrank A B * relrank B 
C = relrank A C
参数：h1 : A <= B；h2 : B <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subfield.relrank_eq_rank_of_le`：relrank_eq_rank_of_le (h : A <= B) : rel
rank A B = Module.rank A (extendScalars h)
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `Subfield.instSubfieldClass`：∀ {K : Type u} [inst : DivisionRing K], Subf
ieldClass (Subfield K) K
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `rank_mul_rank`：rank_mul_rank (A : Type v) [AddCommMonoid A] [Module K A]
 [Module F A] [IsScalarTower F K A] [Module.Free K A] : Module.rank F K * Module
.ra…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
-/
theorem relrank_mul_relrank (h1 : A ≤ B) (h2 : B ≤ C) :
    relrank A B * relrank B C = relrank A C := by
  have h3 := h1.trans h2
  rw [relrank_eq_rank_of_le h1, relrank_eq_rank_of_le h2, relrank_eq_rank_of_le h3]
  let : Algebra A B := (inclusion h1).toAlgebra
  let : Algebra B C := (inclusion h2).toAlgebra
  let : Algebra A C := (inclusion h3).toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  exact rank_mul_rank A B C

variable {A B C} in
/-
**Subfield.relfinrank_mul_relfinrank** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relfinrank_mul_relfinrank (h1 : A <= B) (h2 : B <= C) : relfinrank A B * r
elfinrank B C = relfinrank A C
参数：h1 : A <= B；h2 : B <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Subfield.relrank_mul_relrank`：relrank_mul_relrank (h1 : A <= B) (h2 : B 
<= C) : relrank A B * relrank B C = relrank A C
-/
theorem relfinrank_mul_relfinrank (h1 : A ≤ B) (h2 : B ≤ C) :
    relfinrank A B * relfinrank B C = relfinrank A C := by
  simpa using! congr(toNat $(relrank_mul_relrank h1 h2))
/-
**Subfield.relrank_inf_mul_relrank** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relrank_inf_mul_relrank : A.relrank (B ⊓ C) * B.relrank C = (A ⊓ B).relran
k C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subfield.inf_relrank_right`：inf_relrank_right : relrank (A ⊓ B) B = relr
ank A B
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `Subfield.relrank_mul_relrank`：relrank_mul_relrank (h1 : A <= B) (h2 : B 
<= C) : relrank A B * relrank B C = relrank A C
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem relrank_inf_mul_relrank : A.relrank (B ⊓ C) * B.relrank C = (A ⊓ B).relrank C := by
  rw [← inf_relrank_right A (B ⊓ C), ← inf_relrank_right B C, ← inf_relrank_right (A ⊓ B) C,
    inf_assoc, relrank_mul_relrank inf_le_right inf_le_right]
/-
**Subfield.relfinrank_inf_mul_relfinrank** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relfinrank_inf_mul_relfinrank : A.relfinrank (B ⊓ C) * B.relfinrank C = (A
 ⊓ B).relfinrank C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Subfield.relrank_inf_mul_relrank`：relrank_inf_mul_relrank : A.relrank (B
 ⊓ C) * B.relrank C = (A ⊓ B).relrank C
-/
theorem relfinrank_inf_mul_relfinrank :
    A.relfinrank (B ⊓ C) * B.relfinrank C = (A ⊓ B).relfinrank C := by
  simpa using! congr(toNat $(relrank_inf_mul_relrank A B C))

variable {B C} in
/-
**Subfield.relrank_mul_relrank_eq_inf_relrank** 是 Mathlib 中的一个定理，位于命名空间 `Subfiel
d`。
形式化陈述：relrank_mul_relrank_eq_inf_relrank (h : B <= C) : relrank A B * relrank B 
C = (A ⊓ B).relrank C
参数：h : B <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `Subfield.relrank_inf_mul_relrank`：relrank_inf_mul_relrank : A.relrank (B
 ⊓ C) * B.relrank C = (A ⊓ B).relrank C
-/
theorem relrank_mul_relrank_eq_inf_relrank (h : B ≤ C) :
    relrank A B * relrank B C = (A ⊓ B).relrank C := by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

variable {B C} in
/-
**Subfield.relfinrank_mul_relfinrank_eq_inf_relfinrank** 是 Mathlib 中的一个定理，位于命名空间
 `Subfield`。
形式化陈述：relfinrank_mul_relfinrank_eq_inf_relfinrank (h : B <= C) : relfinrank A B 
* relfinrank B C = (A ⊓ B).relfinrank C
参数：h : B <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Subfield.relrank_mul_relrank_eq_inf_relrank`：relrank_mul_relrank_eq_inf_
relrank (h : B <= C) : relrank A B * relrank B C = (A ⊓ B).relrank C
-/
theorem relfinrank_mul_relfinrank_eq_inf_relfinrank (h : B ≤ C) :
    relfinrank A B * relfinrank B C = (A ⊓ B).relfinrank C := by
  simpa using! congr(toNat $(relrank_mul_relrank_eq_inf_relrank A h))

variable {A B} in
/-
**Subfield.relrank_inf_mul_relrank_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relrank_inf_mul_relrank_of_le (h : A <= B) : A.relrank (B ⊓ C) * B.relrank
 C = A.relrank C
参数：h : A <= B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `Subfield.relrank_inf_mul_relrank`：relrank_inf_mul_relrank : A.relrank (B
 ⊓ C) * B.relrank C = (A ⊓ B).relrank C
-/
theorem relrank_inf_mul_relrank_of_le (h : A ≤ B) :
    A.relrank (B ⊓ C) * B.relrank C = A.relrank C := by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

variable {A B} in
/-
**Subfield.relfinrank_inf_mul_relfinrank_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Subfie
ld`。
形式化陈述：relfinrank_inf_mul_relfinrank_of_le (h : A <= B) : A.relfinrank (B ⊓ C) * 
B.relfinrank C = A.relfinrank C
参数：h : A <= B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Subfield.relrank_inf_mul_relrank_of_le`：relrank_inf_mul_relrank_of_le (h
 : A <= B) : A.relrank (B ⊓ C) * B.relrank C = A.relrank C
-/
theorem relfinrank_inf_mul_relfinrank_of_le (h : A ≤ B) :
    A.relfinrank (B ⊓ C) * B.relfinrank C = A.relfinrank C := by
  simpa using! congr(toNat $(relrank_inf_mul_relrank_of_le C h))

variable {A B} in
/-
**Subfield.relrank_dvd_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relrank_dvd_of_le_left (h : A <= B) : B.relrank C ∣ A.relrank C
参数：h : A <= B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_of_mul_left_eq`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α} 
(c : α), c * a = b → a ∣ b
· 使用定理 `Subfield.relrank_inf_mul_relrank_of_le`：relrank_inf_mul_relrank_of_le (h
 : A <= B) : A.relrank (B ⊓ C) * B.relrank C = A.relrank C
-/
theorem relrank_dvd_of_le_left (h : A ≤ B) : B.relrank C ∣ A.relrank C :=
  dvd_of_mul_left_eq _ (relrank_inf_mul_relrank_of_le C h)

variable {A B} in
/-
**Subfield.relfinrank_dvd_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Subfield`。
形式化陈述：relfinrank_dvd_of_le_left (h : A <= B) : B.relfinrank C ∣ A.relfinrank C
参数：h : A <= B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_of_mul_left_eq`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α} 
(c : α), c * a = b → a ∣ b
· 使用定理 `Subfield.relfinrank_inf_mul_relfinrank_of_le`：relfinrank_inf_mul_relfinr
ank_of_le (h : A <= B) : A.relfinrank (B ⊓ C) * B.relfinrank C = A.relfinrank C
-/
theorem relfinrank_dvd_of_le_left (h : A ≤ B) : B.relfinrank C ∣ A.relfinrank C :=
  dvd_of_mul_left_eq _ (relfinrank_inf_mul_relfinrank_of_le C h)

end Subfield

namespace IntermediateField

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

variable {L : Type w} [Field L] [Algebra F L]

variable (A B C : IntermediateField F E)

/-- `IntermediateField.relrank A B` is defined to be `[B : A ⊓ B]` as a `Cardinal`, in particular,
when `A ≤ B` it is `[B : A]`, the degree of the field extension `B / A`.
This is similar to `Subgroup.relIndex` but it is `Cardinal` valued. -/
/-
**IntermediateField.relrank** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`。
形式化陈述：relrank
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IntermediateField.relrank A B` is defined to be `[B : A ⊓ B]` as a `Cardinal`, 
in particular,
when `A ≤ B` it is `[B : A]`, the degree of the field extension `B / A`.
This is similar to `Subgroup.relIndex` but it is `Cardinal` valued.
-/
noncomputable def relrank := A.toSubfield.relrank B.toSubfield

/-- The `Nat` version of `IntermediateField.relrank`.
If `B / A ⊓ B` is an infinite extension, then it is zero. -/
/-
**IntermediateField.relfinrank** 是 Mathlib 中的一个定义，位于命名空间 `IntermediateField`。
形式化陈述：relfinrank
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Nat` version of `IntermediateField.relrank`.
If `B / A ⊓ B` is an infinite extension, then it is zero.
-/
noncomputable def relfinrank := A.toSubfield.relfinrank B.toSubfield
/-
**IntermediateField.relfinrank_eq_toNat_relrank** 是 Mathlib 中的一个定理，位于命名空间 `Inter
mediateField`。
形式化陈述：relfinrank_eq_toNat_relrank : relfinrank A B = toNat (relrank A B)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem relfinrank_eq_toNat_relrank : relfinrank A B = toNat (relrank A B) := rfl

variable {A B C}
/-
**IntermediateField.relrank_eq_of_inf_eq** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field`。
形式化陈述：relrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) : relrank A C = relrank B C
参数：h : A ⊓ C = B ⊓ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.relrank_eq_of_inf_eq`：relrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) 
: relrank A C = relrank B C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem relrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) : relrank A C = relrank B C :=
  Subfield.relrank_eq_of_inf_eq congr(toSubfield $h)
/-
**IntermediateField.relfinrank_eq_of_inf_eq** 是 Mathlib 中的一个定理，位于命名空间 `Intermedi
ateField`。
形式化陈述：relfinrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) : relfinrank A C = relfinrank 
B C
参数：h : A ⊓ C = B ⊓ C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.relrank_eq_of_inf_eq`：relrank_eq_of_inf_eq (h : A ⊓ C 
= B ⊓ C) : relrank A C = relrank B C
-/
theorem relfinrank_eq_of_inf_eq (h : A ⊓ C = B ⊓ C) : relfinrank A C = relfinrank B C :=
  congr(toNat $(relrank_eq_of_inf_eq h))

/-- If `A ≤ B`, then `IntermediateField.relrank A B` is `[B : A]` -/
/-
**IntermediateField.relrank_eq_rank_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Intermediat
eField`。
形式化陈述：relrank_eq_rank_of_le (h : A <= B) : relrank A B = Module.rank A (extendSc
alars h)
参数：h : A <= B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.relrank_eq_rank_of_le`：relrank_eq_rank_of_le (h : A <= B) : rel
rank A B = Module.rank A (extendScalars h)

--- 原说明 ---
If `A ≤ B`, then `IntermediateField.relrank A B` is `[B : A]`
-/
theorem relrank_eq_rank_of_le (h : A ≤ B) : relrank A B = Module.rank A (extendScalars h) :=
  Subfield.relrank_eq_rank_of_le h

/-- If `A ≤ B`, then `IntermediateField.relrank A B` is `[B : A]` -/
/-
**IntermediateField.relfinrank_eq_finrank_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Inter
mediateField`。
形式化陈述：relfinrank_eq_finrank_of_le (h : A <= B) : relfinrank A B = finrank A (ext
endScalars h)
参数：h : A <= B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.relrank_eq_rank_of_le`：relrank_eq_rank_of_le (h : A <=
 B) : relrank A B = Module.rank A (extendScalars h)

--- 原说明 ---
If `A ≤ B`, then `IntermediateField.relrank A B` is `[B : A]`
-/
theorem relfinrank_eq_finrank_of_le (h : A ≤ B) : relfinrank A B = finrank A (extendScalars h) :=
  congr(toNat $(relrank_eq_rank_of_le h))

variable (A B C)
/-
**IntermediateField.inf_relrank_right** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFie
ld`。
形式化陈述：inf_relrank_right : relrank (A ⊓ B) B = relrank A B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.relrank_eq_rank_of_le`：relrank_eq_rank_of_le (h : A <=
 B) : relrank A B = Module.rank A (extendScalars h)
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem inf_relrank_right : relrank (A ⊓ B) B = relrank A B :=
  relrank_eq_rank_of_le (inf_le_right : A ⊓ B ≤ B)
/-
**IntermediateField.inf_relfinrank_right** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field`。
形式化陈述：inf_relfinrank_right : relfinrank (A ⊓ B) B = relfinrank A B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.inf_relrank_right`：inf_relrank_right : relrank (A ⊓ B)
 B = relrank A B
-/
theorem inf_relfinrank_right : relfinrank (A ⊓ B) B = relfinrank A B :=
  congr(toNat $(inf_relrank_right A B))
/-
**IntermediateField.inf_relrank_left** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFiel
d`。
形式化陈述：inf_relrank_left : relrank (A ⊓ B) A = relrank B A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `IntermediateField.inf_relrank_right`：inf_relrank_right : relrank (A ⊓ B)
 B = relrank A B
-/
theorem inf_relrank_left : relrank (A ⊓ B) A = relrank B A := by
  rw [inf_comm, inf_relrank_right]
/-
**IntermediateField.inf_relfinrank_left** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：inf_relfinrank_left : relfinrank (A ⊓ B) A = relfinrank B A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.inf_relrank_left`：inf_relrank_left : relrank (A ⊓ B) A
 = relrank B A
-/
theorem inf_relfinrank_left : relfinrank (A ⊓ B) A = relfinrank B A :=
  congr(toNat $(inf_relrank_left A B))

@[simp]
/-
**IntermediateField.relrank_self** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：relrank_self : relrank A A = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.relrank_self`：relrank_self : relrank A A = 1
-/
theorem relrank_self : relrank A A = 1 := A.toSubfield.relrank_self

@[simp]
/-
**IntermediateField.relfinrank_self** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField
`。
形式化陈述：relfinrank_self : relfinrank A A = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.relfinrank_self`：relfinrank_self : relfinrank A A = 1
-/
theorem relfinrank_self : relfinrank A A = 1 := A.toSubfield.relfinrank_self

variable {A B}
/-
**IntermediateField.relrank_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：relrank_eq_one_iff : relrank A B = 1 ↔ B <= A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.relrank_eq_one_iff`：relrank_eq_one_iff : relrank A B = 1 ↔ B <=
 A
-/
theorem relrank_eq_one_iff : relrank A B = 1 ↔ B ≤ A :=
  Subfield.relrank_eq_one_iff
/-
**IntermediateField.relfinrank_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Intermediat
eField`。
形式化陈述：relfinrank_eq_one_iff : relfinrank A B = 1 ↔ B <= A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.relfinrank_eq_one_iff`：relfinrank_eq_one_iff : relfinrank A B =
 1 ↔ B <= A
-/
theorem relfinrank_eq_one_iff : relfinrank A B = 1 ↔ B ≤ A :=
  Subfield.relfinrank_eq_one_iff

alias ⟨_, relrank_eq_one_of_le⟩ := relrank_eq_one_iff

alias ⟨_, relfinrank_eq_one_of_le⟩ := relfinrank_eq_one_iff

variable (A B)
/-
**IntermediateField.lift_rank_comap** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField
`。
形式化陈述：lift_rank_comap (f : L ->ₐ[F] E) : Cardinal.lift.{v} (Module.rank (A.comap
 f) L) = Cardinal.lift.{w} (relrank A f.fieldRange)
参数：f : L ->ₐ[F] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.lift_rank_comap`：lift_rank_comap (f : L ->+* E) : lift.{v} (Mod
ule.rank (A.comap f) L) = lift.{w} (relrank A f.fieldRange)
-/
theorem lift_rank_comap (f : L →ₐ[F] E) :
    Cardinal.lift.{v} (Module.rank (A.comap f) L) = Cardinal.lift.{w} (relrank A f.fieldRange) :=
  A.toSubfield.lift_rank_comap f.toRingHom
/-
**IntermediateField.rank_comap** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：rank_comap {L : Type v} [Field L] [Algebra F L] (f : L ->ₐ[F] E) : Module.
rank (A.comap f) L = relrank A f.fieldRange
参数：f : L ->ₐ[F] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `IntermediateField.lift_rank_comap`：lift_rank_comap (f : L ->ₐ[F] E) : Ca
rdinal.lift.{v} (Module.rank (A.comap f) L) = Cardinal.lift.{w} (relrank A f.fie
ldRange)
-/
theorem rank_comap {L : Type v} [Field L] [Algebra F L] (f : L →ₐ[F] E) :
    Module.rank (A.comap f) L = relrank A f.fieldRange := by
  simpa only [lift_id] using A.lift_rank_comap f
/-
**IntermediateField.finrank_comap** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：finrank_comap (f : L ->ₐ[F] E) : finrank (A.comap f) L = relfinrank A f.fi
eldRange
参数：f : L ->ₐ[F] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `IntermediateField.lift_rank_comap`：lift_rank_comap (f : L ->ₐ[F] E) : Ca
rdinal.lift.{v} (Module.rank (A.comap f) L) = Cardinal.lift.{w} (relrank A f.fie
ldRange)
-/
theorem finrank_comap (f : L →ₐ[F] E) : finrank (A.comap f) L = relfinrank A f.fieldRange := by
  simpa using! congr(toNat $(lift_rank_comap A f))
/-
**IntermediateField.lift_relrank_comap** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：lift_relrank_comap (f : L ->ₐ[F] E) (B : IntermediateField F L) : Cardinal
.lift.{v} (relrank (A.comap f) B) = Cardinal.lift.{w} (relrank A (B.map f))
参数：f : L ->ₐ[F] E；B : IntermediateField F L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.lift_relrank_comap`：lift_relrank_comap (f : L ->+* E) (B : Subf
ield L) : lift.{v} (relrank (A.comap f) B) = lift.{w} (relrank A (B.map f))
-/
theorem lift_relrank_comap (f : L →ₐ[F] E) (B : IntermediateField F L) :
    Cardinal.lift.{v} (relrank (A.comap f) B) = Cardinal.lift.{w} (relrank A (B.map f)) :=
  A.toSubfield.lift_relrank_comap f.toRingHom B.toSubfield
/-
**IntermediateField.relrank_comap** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：relrank_comap {L : Type v} [Field L] [Algebra F L] (f : L ->ₐ[F] E) (B : I
ntermediateField F L) : relrank (A.comap f) B = relrank A (B.map f)
参数：f : L ->ₐ[F] E；B : IntermediateField F L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `IntermediateField.lift_relrank_comap`：lift_relrank_comap (f : L ->ₐ[F] E
) (B : IntermediateField F L) : Cardinal.lift.{v} (relrank (A.comap f) B) = Card
inal.lift.{w} (relrank A (…
-/
theorem relrank_comap {L : Type v} [Field L] [Algebra F L] (f : L →ₐ[F] E)
    (B : IntermediateField F L) : relrank (A.comap f) B = relrank A (B.map f) := by
  simpa only [lift_id] using A.lift_relrank_comap f B
/-
**IntermediateField.relfinrank_comap** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFiel
d`。
形式化陈述：relfinrank_comap (f : L ->ₐ[F] E) (B : IntermediateField F L) : relfinrank
 (A.comap f) B = relfinrank A (B.map f)
参数：f : L ->ₐ[F] E；B : IntermediateField F L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `IntermediateField.lift_relrank_comap`：lift_relrank_comap (f : L ->ₐ[F] E
) (B : IntermediateField F L) : Cardinal.lift.{v} (relrank (A.comap f) B) = Card
inal.lift.{w} (relrank A (…
-/
theorem relfinrank_comap (f : L →ₐ[F] E) (B : IntermediateField F L) :
    relfinrank (A.comap f) B = relfinrank A (B.map f) := by
  simpa using! congr(toNat $(lift_relrank_comap A f B))
/-
**IntermediateField.lift_relrank_map_map** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field`。
形式化陈述：lift_relrank_map_map (f : E ->ₐ[F] L) : Cardinal.lift.{v} (relrank (A.map 
f) (B.map f)) = Cardinal.lift.{w} (relrank A B)
参数：f : E ->ₐ[F] L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.lift_relrank_comap`：lift_relrank_comap (f : L ->ₐ[F] E
) (B : IntermediateField F L) : Cardinal.lift.{v} (relrank (A.comap f) B) = Card
inal.lift.{w} (relrank A (…
· 使用定理 `IntermediateField.comap_map`：comap_map (f : L ->ₐ[K] L') (S : Intermedia
teField K L) : (S.map f).comap f = S
-/
theorem lift_relrank_map_map (f : E →ₐ[F] L) :
    Cardinal.lift.{v} (relrank (A.map f) (B.map f)) = Cardinal.lift.{w} (relrank A B) := by
  rw [← lift_relrank_comap, comap_map]
/-
**IntermediateField.relrank_map_map** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateField
`。
形式化陈述：relrank_map_map {L : Type v} [Field L] [Algebra F L] (f : E ->ₐ[F] L) : re
lrank (A.map f) (B.map f) = relrank A B
参数：f : E ->ₐ[F] L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `IntermediateField.lift_relrank_map_map`：lift_relrank_map_map (f : E ->ₐ[
F] L) : Cardinal.lift.{v} (relrank (A.map f) (B.map f)) = Cardinal.lift.{w} (rel
rank A B)
-/
theorem relrank_map_map {L : Type v} [Field L] [Algebra F L] (f : E →ₐ[F] L) :
    relrank (A.map f) (B.map f) = relrank A B := by
  simpa only [lift_id] using lift_relrank_map_map A B f
/-
**IntermediateField.relfinrank_map_map** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFi
eld`。
形式化陈述：relfinrank_map_map (f : E ->ₐ[F] L) : relfinrank (A.map f) (B.map f) = rel
finrank A B
参数：f : E ->ₐ[F] L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `IntermediateField.lift_relrank_map_map`：lift_relrank_map_map (f : E ->ₐ[
F] L) : Cardinal.lift.{v} (relrank (A.map f) (B.map f)) = Cardinal.lift.{w} (rel
rank A B)
-/
theorem relfinrank_map_map (f : E →ₐ[F] L) :
    relfinrank (A.map f) (B.map f) = relfinrank A B := by
  simpa using! congr(toNat $(lift_relrank_map_map A B f))
/-
**IntermediateField.lift_relrank_comap_comap_eq_lift_relrank_inf** 是 Mathlib 中的一
个定理，位于命名空间 `IntermediateField`。
形式化陈述：lift_relrank_comap_comap_eq_lift_relrank_inf (f : L ->ₐ[F] E) : Cardinal.l
ift.{v} (relrank (A.comap f) (B.comap f)) = Cardinal.lift.{w} (relrank A (B ⊓ f.
fieldRange))
参数：f : L ->ₐ[F] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.lift_relrank_comap_comap_eq_lift_relrank_inf`：lift_relrank_coma
p_comap_eq_lift_relrank_inf (f : L ->+* E) : lift.{v} (relrank (A.comap f) (B.co
map f)) = lift.{w} (relrank A (B ⊓ f.fieldR…
-/
theorem lift_relrank_comap_comap_eq_lift_relrank_inf (f : L →ₐ[F] E) :
    Cardinal.lift.{v} (relrank (A.comap f) (B.comap f)) =
    Cardinal.lift.{w} (relrank A (B ⊓ f.fieldRange)) :=
  A.toSubfield.lift_relrank_comap_comap_eq_lift_relrank_inf B.toSubfield f.toRingHom
/-
**IntermediateField.relrank_comap_comap_eq_relrank_inf** 是 Mathlib 中的一个定理，位于命名空间
 `IntermediateField`。
形式化陈述：relrank_comap_comap_eq_relrank_inf {L : Type v} [Field L] [Algebra F L] (f
 : L ->ₐ[F] E) : relrank (A.comap f) (B.comap f) = relrank A (B ⊓ f.fieldRange)
参数：f : L ->ₐ[F] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `IntermediateField.lift_relrank_comap_comap_eq_lift_relrank_inf`：lift_rel
rank_comap_comap_eq_lift_relrank_inf (f : L ->ₐ[F] E) : Cardinal.lift.{v} (relra
nk (A.comap f) (B.comap f)) = Cardinal.lift.{w} (rel…
-/
theorem relrank_comap_comap_eq_relrank_inf
    {L : Type v} [Field L] [Algebra F L] (f : L →ₐ[F] E) :
    relrank (A.comap f) (B.comap f) = relrank A (B ⊓ f.fieldRange) := by
  simpa only [lift_id] using lift_relrank_comap_comap_eq_lift_relrank_inf A B f
/-
**IntermediateField.relfinrank_comap_comap_eq_relfinrank_inf** 是 Mathlib 中的一个定理，
位于命名空间 `IntermediateField`。
形式化陈述：relfinrank_comap_comap_eq_relfinrank_inf (f : L ->ₐ[F] E) : relfinrank (A.
comap f) (B.comap f) = relfinrank A (B ⊓ f.fieldRange)
参数：f : L ->ₐ[F] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `IntermediateField.lift_relrank_comap_comap_eq_lift_relrank_inf`：lift_rel
rank_comap_comap_eq_lift_relrank_inf (f : L ->ₐ[F] E) : Cardinal.lift.{v} (relra
nk (A.comap f) (B.comap f)) = Cardinal.lift.{w} (rel…
-/
theorem relfinrank_comap_comap_eq_relfinrank_inf (f : L →ₐ[F] E) :
    relfinrank (A.comap f) (B.comap f) = relfinrank A (B ⊓ f.fieldRange) := by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_inf A B f))
/-
**IntermediateField.lift_relrank_comap_comap_eq_lift_relrank_of_le** 是 Mathlib 中
的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：lift_relrank_comap_comap_eq_lift_relrank_of_le (f : L ->ₐ[F] E) (h : B <= 
f.fieldRange) : Cardinal.lift.{v} (relrank (A.comap f) (B.comap f)) = Cardinal.l
ift.{w} (relrank A B)
参数：f : L ->ₐ[F] E；h : B <= f.fieldRange。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `IntermediateField.lift_relrank_comap_comap_eq_lift_relrank_inf`：lift_rel
rank_comap_comap_eq_lift_relrank_inf (f : L ->ₐ[F] E) : Cardinal.lift.{v} (relra
nk (A.comap f) (B.comap f)) = Cardinal.lift.{w} (rel…
-/
theorem lift_relrank_comap_comap_eq_lift_relrank_of_le (f : L →ₐ[F] E) (h : B ≤ f.fieldRange) :
    Cardinal.lift.{v} (relrank (A.comap f) (B.comap f)) = Cardinal.lift.{w} (relrank A B) := by
  simpa only [inf_of_le_left h] using lift_relrank_comap_comap_eq_lift_relrank_inf A B f
/-
**IntermediateField.relrank_comap_comap_eq_relrank_of_le** 是 Mathlib 中的一个定理，位于命名
空间 `IntermediateField`。
形式化陈述：relrank_comap_comap_eq_relrank_of_le {L : Type v} [Field L] [Algebra F L] 
(f : L ->ₐ[F] E) (h : B <= f.fieldRange) : relrank (A.comap f) (B.comap f) = rel
rank A B
参数：f : L ->ₐ[F] E；h : B <= f.fieldRange。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `IntermediateField.lift_relrank_comap_comap_eq_lift_relrank_of_le`：lift_r
elrank_comap_comap_eq_lift_relrank_of_le (f : L ->ₐ[F] E) (h : B <= f.fieldRange
) : Cardinal.lift.{v} (relrank (A.comap f) (B.comap f)…
-/
theorem relrank_comap_comap_eq_relrank_of_le
    {L : Type v} [Field L] [Algebra F L] (f : L →ₐ[F] E) (h : B ≤ f.fieldRange) :
    relrank (A.comap f) (B.comap f) = relrank A B := by
  simpa only [lift_id] using lift_relrank_comap_comap_eq_lift_relrank_of_le A B f h
/-
**IntermediateField.relfinrank_comap_comap_eq_relfinrank_of_le** 是 Mathlib 中的一个定
理，位于命名空间 `IntermediateField`。
形式化陈述：relfinrank_comap_comap_eq_relfinrank_of_le (f : L ->ₐ[F] E) (h : B <= f.fi
eldRange) : relfinrank (A.comap f) (B.comap f) = relfinrank A B
参数：f : L ->ₐ[F] E；h : B <= f.fieldRange。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `IntermediateField.lift_relrank_comap_comap_eq_lift_relrank_of_le`：lift_r
elrank_comap_comap_eq_lift_relrank_of_le (f : L ->ₐ[F] E) (h : B <= f.fieldRange
) : Cardinal.lift.{v} (relrank (A.comap f) (B.comap f)…
-/
theorem relfinrank_comap_comap_eq_relfinrank_of_le (f : L →ₐ[F] E) (h : B ≤ f.fieldRange) :
    relfinrank (A.comap f) (B.comap f) = relfinrank A B := by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_of_le A B f h))
/-
**IntermediateField.lift_relrank_comap_comap_eq_lift_relrank_of_surjective** 是 M
athlib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：lift_relrank_comap_comap_eq_lift_relrank_of_surjective (f : L ->ₐ[F] E) (h
 : Function.Surjective f) : Cardinal.lift.{v} (relrank (A.comap f) (B.comap f)) 
= Cardinal.lift.{w} (relrank A B)
参数：f : L ->ₐ[F] E；h : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.lift_relrank_comap_comap_eq_lift_relrank_of_le`：lift_r
elrank_comap_comap_eq_lift_relrank_of_le (f : L ->ₐ[F] E) (h : B <= f.fieldRange
) : Cardinal.lift.{v} (relrank (A.comap f) (B.comap f)…
-/
theorem lift_relrank_comap_comap_eq_lift_relrank_of_surjective
    (f : L →ₐ[F] E) (h : Function.Surjective f) :
    Cardinal.lift.{v} (relrank (A.comap f) (B.comap f)) = Cardinal.lift.{w} (relrank A B) :=
  lift_relrank_comap_comap_eq_lift_relrank_of_le A B f fun x _ ↦ h x
/-
**IntermediateField.relrank_comap_comap_eq_relrank_of_surjective** 是 Mathlib 中的一
个定理，位于命名空间 `IntermediateField`。
形式化陈述：relrank_comap_comap_eq_relrank_of_surjective {L : Type v} [Field L] [Algeb
ra F L] (f : L ->ₐ[F] E) (h : Function.Surjective f) : relrank (A.comap f) (B.co
map f) = relrank A B
参数：f : L ->ₐ[F] E；h : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `IntermediateField.lift_relrank_comap_comap_eq_lift_relrank_of_surjective
`：lift_relrank_comap_comap_eq_lift_relrank_of_surjective (f : L ->ₐ[F] E) (h : F
unction.Surjective f) : Cardinal.lift.{v} (relrank (A.comap f)…
-/
theorem relrank_comap_comap_eq_relrank_of_surjective
    {L : Type v} [Field L] [Algebra F L] (f : L →ₐ[F] E) (h : Function.Surjective f) :
    relrank (A.comap f) (B.comap f) = relrank A B := by
  simpa using lift_relrank_comap_comap_eq_lift_relrank_of_surjective A B f h
/-
**IntermediateField.relfinrank_comap_comap_eq_relfinrank_of_surjective** 是 Mathl
ib 中的一个定理，位于命名空间 `IntermediateField`。
形式化陈述：relfinrank_comap_comap_eq_relfinrank_of_surjective (f : L ->ₐ[F] E) (h : F
unction.Surjective f) : relfinrank (A.comap f) (B.comap f) = relfinrank A B
参数：f : L ->ₐ[F] E；h : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `IntermediateField.lift_relrank_comap_comap_eq_lift_relrank_of_surjective
`：lift_relrank_comap_comap_eq_lift_relrank_of_surjective (f : L ->ₐ[F] E) (h : F
unction.Surjective f) : Cardinal.lift.{v} (relrank (A.comap f)…
-/
theorem relfinrank_comap_comap_eq_relfinrank_of_surjective
    (f : L →ₐ[F] E) (h : Function.Surjective f) :
    relfinrank (A.comap f) (B.comap f) = relfinrank A B := by
  simpa using! congr(toNat $(lift_relrank_comap_comap_eq_lift_relrank_of_surjective A B f h))

variable {A B} in
/-
**IntermediateField.relrank_mul_rank_top** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field`。
形式化陈述：relrank_mul_rank_top (h : A <= B) : relrank A B * Module.rank B E = Module
.rank A E
参数：h : A <= B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.relrank_mul_rank_top`：relrank_mul_rank_top (h : A <= B) : relra
nk A B * Module.rank B E = Module.rank A E
-/
theorem relrank_mul_rank_top (h : A ≤ B) : relrank A B * Module.rank B E = Module.rank A E :=
  Subfield.relrank_mul_rank_top h

variable {A B} in
/-
**IntermediateField.relfinrank_mul_finrank_top** 是 Mathlib 中的一个定理，位于命名空间 `Interm
ediateField`。
形式化陈述：relfinrank_mul_finrank_top (h : A <= B) : relfinrank A B * finrank B E = f
inrank A E
参数：h : A <= B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `IntermediateField.relrank_mul_rank_top`：relrank_mul_rank_top (h : A <= B
) : relrank A B * Module.rank B E = Module.rank A E
-/
theorem relfinrank_mul_finrank_top (h : A ≤ B) : relfinrank A B * finrank B E = finrank A E := by
  simpa using! congr(toNat $(relrank_mul_rank_top h))

variable {A B} in
/-
**IntermediateField.rank_bot_mul_relrank** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field`。
形式化陈述：rank_bot_mul_relrank (h : A <= B) : Module.rank F A * relrank A B = Module
.rank F B
参数：h : A <= B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.relrank_eq_rank_of_le`：relrank_eq_rank_of_le (h : A <=
 B) : relrank A B = Module.rank A (extendScalars h)
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `rank_mul_rank`：rank_mul_rank (A : Type v) [AddCommMonoid A] [Module K A]
 [Module F A] [IsScalarTower F K A] [Module.Free K A] : Module.rank F K * Module
.ra…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
-/
theorem rank_bot_mul_relrank (h : A ≤ B) : Module.rank F A * relrank A B = Module.rank F B := by
  rw [relrank_eq_rank_of_le h]
  let : Algebra A B := (inclusion h).toAlgebra
  exact rank_mul_rank F A B

variable {A B} in
/-
**IntermediateField.finrank_bot_mul_relfinrank** 是 Mathlib 中的一个定理，位于命名空间 `Interm
ediateField`。
形式化陈述：finrank_bot_mul_relfinrank (h : A <= B) : finrank F A * relfinrank A B = f
inrank F B
参数：h : A <= B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `IntermediateField.rank_bot_mul_relrank`：rank_bot_mul_relrank (h : A <= B
) : Module.rank F A * relrank A B = Module.rank F B
-/
theorem finrank_bot_mul_relfinrank (h : A ≤ B) : finrank F A * relfinrank A B = finrank F B := by
  simpa using! congr(toNat $(rank_bot_mul_relrank h))

variable {A B} in
/-
**IntermediateField.relrank_dvd_rank_top_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Interm
ediateField`。
形式化陈述：relrank_dvd_rank_top_of_le (h : A <= B) : relrank A B ∣ Module.rank A E
参数：h : A <= B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_of_mul_right_eq`：∀ {α : Type u_1} [inst : Semigroup α] {a b : α} (c 
: α), a * c = b → a ∣ b
· 使用定理 `IntermediateField.relrank_mul_rank_top`：relrank_mul_rank_top (h : A <= B
) : relrank A B * Module.rank B E = Module.rank A E
-/
theorem relrank_dvd_rank_top_of_le (h : A ≤ B) : relrank A B ∣ Module.rank A E :=
  dvd_of_mul_right_eq _ (relrank_mul_rank_top h)

variable {A B} in
/-
**IntermediateField.relfinrank_dvd_finrank_top_of_le** 是 Mathlib 中的一个定理，位于命名空间 `
IntermediateField`。
形式化陈述：relfinrank_dvd_finrank_top_of_le (h : A <= B) : relfinrank A B ∣ finrank A
 E
参数：h : A <= B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_of_mul_right_eq`：∀ {α : Type u_1} [inst : Semigroup α] {a b : α} (c 
: α), a * c = b → a ∣ b
· 使用定理 `IntermediateField.relfinrank_mul_finrank_top`：relfinrank_mul_finrank_top
 (h : A <= B) : relfinrank A B * finrank B E = finrank A E
-/
theorem relfinrank_dvd_finrank_top_of_le (h : A ≤ B) : relfinrank A B ∣ finrank A E :=
  dvd_of_mul_right_eq _ (relfinrank_mul_finrank_top h)
/-
**IntermediateField.relrank_dvd_rank_bot** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field`。
形式化陈述：relrank_dvd_rank_bot : relrank A B ∣ Module.rank F B
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_of_mul_left_eq`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α} 
(c : α), c * a = b → a ∣ b
· 使用定理 `IntermediateField.rank_bot_mul_relrank`：rank_bot_mul_relrank (h : A <= B
) : Module.rank F A * relrank A B = Module.rank F B
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `IntermediateField.inf_relrank_right`：inf_relrank_right : relrank (A ⊓ B)
 B = relrank A B
-/
theorem relrank_dvd_rank_bot : relrank A B ∣ Module.rank F B :=
  inf_relrank_right A B ▸ dvd_of_mul_left_eq _ (rank_bot_mul_relrank inf_le_right)
/-
**IntermediateField.relfinrank_dvd_finrank_bot** 是 Mathlib 中的一个定理，位于命名空间 `Interm
ediateField`。
形式化陈述：relfinrank_dvd_finrank_bot : relfinrank A B ∣ finrank F B
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_of_mul_left_eq`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α} 
(c : α), c * a = b → a ∣ b
· 使用定理 `IntermediateField.finrank_bot_mul_relfinrank`：finrank_bot_mul_relfinrank
 (h : A <= B) : finrank F A * relfinrank A B = finrank F B
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `IntermediateField.inf_relfinrank_right`：inf_relfinrank_right : relfinran
k (A ⊓ B) B = relfinrank A B
-/
theorem relfinrank_dvd_finrank_bot : relfinrank A B ∣ finrank F B :=
  inf_relfinrank_right A B ▸ dvd_of_mul_left_eq _ (finrank_bot_mul_relfinrank inf_le_right)

variable {A B C} in
/-
**IntermediateField.relrank_mul_relrank** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：relrank_mul_relrank (h1 : A <= B) (h2 : B <= C) : relrank A B * relrank B 
C = relrank A C
参数：h1 : A <= B；h2 : B <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.relrank_mul_relrank`：relrank_mul_relrank (h1 : A <= B) (h2 : B 
<= C) : relrank A B * relrank B C = relrank A C
-/
theorem relrank_mul_relrank (h1 : A ≤ B) (h2 : B ≤ C) :
    relrank A B * relrank B C = relrank A C :=
  Subfield.relrank_mul_relrank h1 h2

variable {A B C} in
/-
**IntermediateField.relfinrank_mul_relfinrank** 是 Mathlib 中的一个定理，位于命名空间 `Interme
diateField`。
形式化陈述：relfinrank_mul_relfinrank (h1 : A <= B) (h2 : B <= C) : relfinrank A B * r
elfinrank B C = relfinrank A C
参数：h1 : A <= B；h2 : B <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `IntermediateField.relrank_mul_relrank`：relrank_mul_relrank (h1 : A <= B)
 (h2 : B <= C) : relrank A B * relrank B C = relrank A C
-/
theorem relfinrank_mul_relfinrank (h1 : A ≤ B) (h2 : B ≤ C) :
    relfinrank A B * relfinrank B C = relfinrank A C := by
  simpa using! congr(toNat $(relrank_mul_relrank h1 h2))
/-
**IntermediateField.relrank_inf_mul_relrank** 是 Mathlib 中的一个定理，位于命名空间 `Intermedi
ateField`。
形式化陈述：relrank_inf_mul_relrank : A.relrank (B ⊓ C) * B.relrank C = (A ⊓ B).relran
k C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subfield.relrank_inf_mul_relrank`：relrank_inf_mul_relrank : A.relrank (B
 ⊓ C) * B.relrank C = (A ⊓ B).relrank C
-/
theorem relrank_inf_mul_relrank : A.relrank (B ⊓ C) * B.relrank C = (A ⊓ B).relrank C :=
  Subfield.relrank_inf_mul_relrank A.toSubfield B.toSubfield C.toSubfield
/-
**IntermediateField.relfinrank_inf_mul_relfinrank** 是 Mathlib 中的一个定理，位于命名空间 `Int
ermediateField`。
形式化陈述：relfinrank_inf_mul_relfinrank : A.relfinrank (B ⊓ C) * B.relfinrank C = (A
 ⊓ B).relfinrank C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `IntermediateField.relrank_inf_mul_relrank`：relrank_inf_mul_relrank : A.r
elrank (B ⊓ C) * B.relrank C = (A ⊓ B).relrank C
-/
theorem relfinrank_inf_mul_relfinrank :
    A.relfinrank (B ⊓ C) * B.relfinrank C = (A ⊓ B).relfinrank C := by
  simpa using! congr(toNat $(relrank_inf_mul_relrank A B C))

variable {B C} in
/-
**IntermediateField.relrank_mul_relrank_eq_inf_relrank** 是 Mathlib 中的一个定理，位于命名空间
 `IntermediateField`。
形式化陈述：relrank_mul_relrank_eq_inf_relrank (h : B <= C) : relrank A B * relrank B 
C = (A ⊓ B).relrank C
参数：h : B <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `IntermediateField.relrank_inf_mul_relrank`：relrank_inf_mul_relrank : A.r
elrank (B ⊓ C) * B.relrank C = (A ⊓ B).relrank C
-/
theorem relrank_mul_relrank_eq_inf_relrank (h : B ≤ C) :
    relrank A B * relrank B C = (A ⊓ B).relrank C := by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

variable {B C} in
/-
**IntermediateField.relfinrank_mul_relfinrank_eq_inf_relfinrank** 是 Mathlib 中的一个
定理，位于命名空间 `IntermediateField`。
形式化陈述：relfinrank_mul_relfinrank_eq_inf_relfinrank (h : B <= C) : relfinrank A B 
* relfinrank B C = (A ⊓ B).relfinrank C
参数：h : B <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `IntermediateField.relrank_mul_relrank_eq_inf_relrank`：relrank_mul_relran
k_eq_inf_relrank (h : B <= C) : relrank A B * relrank B C = (A ⊓ B).relrank C
-/
theorem relfinrank_mul_relfinrank_eq_inf_relfinrank (h : B ≤ C) :
    relfinrank A B * relfinrank B C = (A ⊓ B).relfinrank C := by
  simpa using! congr(toNat $(relrank_mul_relrank_eq_inf_relrank A h))

variable {A B} in
/-
**IntermediateField.relrank_inf_mul_relrank_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Int
ermediateField`。
形式化陈述：relrank_inf_mul_relrank_of_le (h : A <= B) : A.relrank (B ⊓ C) * B.relrank
 C = A.relrank C
参数：h : A <= B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `IntermediateField.relrank_inf_mul_relrank`：relrank_inf_mul_relrank : A.r
elrank (B ⊓ C) * B.relrank C = (A ⊓ B).relrank C
-/
theorem relrank_inf_mul_relrank_of_le (h : A ≤ B) :
    A.relrank (B ⊓ C) * B.relrank C = A.relrank C := by
  simpa only [inf_of_le_left h] using relrank_inf_mul_relrank A B C

variable {A B} in
/-
**IntermediateField.relfinrank_inf_mul_relfinrank_of_le** 是 Mathlib 中的一个定理，位于命名空
间 `IntermediateField`。
形式化陈述：relfinrank_inf_mul_relfinrank_of_le (h : A <= B) : A.relfinrank (B ⊓ C) * 
B.relfinrank C = A.relfinrank C
参数：h : A <= B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `IntermediateField.relrank_inf_mul_relrank_of_le`：relrank_inf_mul_relrank
_of_le (h : A <= B) : A.relrank (B ⊓ C) * B.relrank C = A.relrank C
-/
theorem relfinrank_inf_mul_relfinrank_of_le (h : A ≤ B) :
    A.relfinrank (B ⊓ C) * B.relfinrank C = A.relfinrank C := by
  simpa using! congr(toNat $(relrank_inf_mul_relrank_of_le C h))

@[simp]
/-
**IntermediateField.relrank_top_left** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFiel
d`。
形式化陈述：relrank_top_left : relrank ⊤ A = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.relrank_eq_one_of_le`：∀ {F : Type u} {E : Type v} [ins
t : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] {A B : IntermediateField 
F E},   B ≤ A → A.relrank B …
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem relrank_top_left : relrank ⊤ A = 1 := relrank_eq_one_of_le le_top

@[simp]
/-
**IntermediateField.relfinrank_top_left** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：relfinrank_top_left : relfinrank ⊤ A = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.relfinrank_eq_one_of_le`：∀ {F : Type u} {E : Type v} [
inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] {A B : IntermediateFie
ld F E},   B ≤ A → A.relfinrank…
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem relfinrank_top_left : relfinrank ⊤ A = 1 := relfinrank_eq_one_of_le le_top

@[simp]
/-
**IntermediateField.relrank_top_right** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFie
ld`。
形式化陈述：relrank_top_right : relrank A ⊤ = Module.rank A E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.relrank_mul_rank_top`：relrank_mul_rank_top (h : A <= B
) : relrank A B * Module.rank B E = Module.rank A E
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `IntermediateField.rank_top`：∀ {F : Type u_1} [inst : Field F] {E : Type 
u_2} [inst_1 : Field E] [inst_2 : Algebra F E], Module.rank (↥⊤) E = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem relrank_top_right : relrank A ⊤ = Module.rank A E := by
  rw [← relrank_mul_rank_top (show A ≤ ⊤ from le_top), IntermediateField.rank_top, mul_one]

@[simp]
/-
**IntermediateField.relfinrank_top_right** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field`。
形式化陈述：relfinrank_top_right : relfinrank A ⊤ = finrank A E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.relrank_top_right`：relrank_top_right : relrank A ⊤ = M
odule.rank A E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem relfinrank_top_right : relfinrank A ⊤ = finrank A E := by
  simp [relfinrank_eq_toNat_relrank, finrank]

@[simp]
/-
**IntermediateField.relrank_bot_left** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFiel
d`。
形式化陈述：relrank_bot_left : relrank ⊥ A = Module.rank F A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.rank_bot_mul_relrank`：rank_bot_mul_relrank (h : A <= B
) : Module.rank F A * relrank A B = Module.rank F B
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `IntermediateField.rank_bot`：∀ {F : Type u_1} [inst : Field F] {E : Type 
u_2} [inst_1 : Field E] [inst_2 : Algebra F E], Module.rank F ↥⊥ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem relrank_bot_left : relrank ⊥ A = Module.rank F A := by
  rw [← rank_bot_mul_relrank (show ⊥ ≤ A from bot_le), IntermediateField.rank_bot, one_mul]

@[simp]
/-
**IntermediateField.relfinrank_bot_left** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateF
ield`。
形式化陈述：relfinrank_bot_left : relfinrank ⊥ A = finrank F A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.relrank_bot_left`：relrank_bot_left : relrank ⊥ A = Mod
ule.rank F A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem relfinrank_bot_left : relfinrank ⊥ A = finrank F A := by
  simp [relfinrank_eq_toNat_relrank, finrank]

@[simp]
/-
**IntermediateField.relrank_bot_right** 是 Mathlib 中的一个定理，位于命名空间 `IntermediateFie
ld`。
形式化陈述：relrank_bot_right : relrank A ⊥ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.relrank_eq_one_of_le`：∀ {F : Type u} {E : Type v} [ins
t : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] {A B : IntermediateField 
F E},   B ≤ A → A.relrank B …
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem relrank_bot_right : relrank A ⊥ = 1 := relrank_eq_one_of_le bot_le

@[simp]
/-
**IntermediateField.relfinrank_bot_right** 是 Mathlib 中的一个定理，位于命名空间 `Intermediate
Field`。
形式化陈述：relfinrank_bot_right : relfinrank A ⊥ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.relfinrank_eq_one_of_le`：∀ {F : Type u} {E : Type v} [
inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] {A B : IntermediateFie
ld F E},   B ≤ A → A.relfinrank…
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem relfinrank_bot_right : relfinrank A ⊥ = 1 := relfinrank_eq_one_of_le bot_le

variable {A B} in
/-
**IntermediateField.relrank_dvd_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Intermedia
teField`。
形式化陈述：relrank_dvd_of_le_left (h : A <= B) : B.relrank C ∣ A.relrank C
参数：h : A <= B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_of_mul_left_eq`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α} 
(c : α), c * a = b → a ∣ b
· 使用定理 `IntermediateField.relrank_inf_mul_relrank_of_le`：relrank_inf_mul_relrank
_of_le (h : A <= B) : A.relrank (B ⊓ C) * B.relrank C = A.relrank C
-/
theorem relrank_dvd_of_le_left (h : A ≤ B) : B.relrank C ∣ A.relrank C :=
  dvd_of_mul_left_eq _ (relrank_inf_mul_relrank_of_le C h)

variable {A B} in
/-
**IntermediateField.relfinrank_dvd_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Interme
diateField`。
形式化陈述：relfinrank_dvd_of_le_left (h : A <= B) : B.relfinrank C ∣ A.relfinrank C
参数：h : A <= B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_of_mul_left_eq`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α} 
(c : α), c * a = b → a ∣ b
· 使用定理 `IntermediateField.relfinrank_inf_mul_relfinrank_of_le`：relfinrank_inf_mu
l_relfinrank_of_le (h : A <= B) : A.relfinrank (B ⊓ C) * B.relfinrank C = A.relf
inrank C
-/
theorem relfinrank_dvd_of_le_left (h : A ≤ B) : B.relfinrank C ∣ A.relfinrank C :=
  dvd_of_mul_left_eq _ (relfinrank_inf_mul_relfinrank_of_le C h)

end IntermediateField

