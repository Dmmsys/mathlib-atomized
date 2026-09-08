/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.IntermediateField.Basic

/-!

# Characteristic of intermediate fields

This file contains some convenient instances for determining the characteristic of
intermediate fields. Some char zero instances are not provided, since they are already
covered by `SubsemiringClass.instCharZero`.

-/

public section

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

namespace IntermediateField

variable (L : IntermediateField F E) (p : ℕ)

/-
**IntermediateField.charZero** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
形式化陈述：charZero [CharZero F] : CharZero L
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `charZero_of_injective_algebraMap`：charZero_of_injective_algebraMap [Comm
Semiring R] [Semiring A] [Algebra R A] (h : Function.Injective (algebraMap R A))
 [CharZero R] : CharZe…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
instance charZero [CharZero F] : CharZero L :=
  charZero_of_injective_algebraMap (algebraMap F _).injective
/-
**IntermediateField.charP** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
形式化陈述：charP [CharP F p] : CharP L p
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `charP_of_injective_algebraMap`：charP_of_injective_algebraMap [CommSemiri
ng R] [Semiring A] [Algebra R A] (h : Function.Injective (algebraMap R A)) (p : 
Nat) [CharP R p] : …
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
instance charP [CharP F p] : CharP L p :=
  charP_of_injective_algebraMap (algebraMap F _).injective p
/-
**IntermediateField.expChar** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
形式化陈述：expChar [ExpChar F p] : ExpChar L p
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `expChar_of_injective_algebraMap`：expChar_of_injective_algebraMap [CommSe
miring R] [Semiring A] [Algebra R A] (h : Function.Injective (algebraMap R A)) (
q : Nat) [ExpChar R q…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
instance expChar [ExpChar F p] : ExpChar L p :=
  expChar_of_injective_algebraMap (algebraMap F _).injective p
/-
**IntermediateField.charP'** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
形式化陈述：charP' [CharP E p] : CharP L p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance charP' [CharP E p] : CharP L p := Subfield.charP L.toSubfield p
/-
**IntermediateField.expChar'** 是 Mathlib 中的一个实例，位于命名空间 `IntermediateField`。
形式化陈述：expChar' [ExpChar E p] : ExpChar L p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance expChar' [ExpChar E p] : ExpChar L p := Subfield.expChar L.toSubfield p

end IntermediateField

