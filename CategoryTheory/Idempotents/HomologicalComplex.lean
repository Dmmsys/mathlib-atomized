/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Idempotents.Karoubi

/-!
# Idempotent completeness and homological complexes

This file contains simplifications lemmas for categories
`Karoubi (HomologicalComplex C c)` and the construction of an equivalence
of categories `Karoubi (HomologicalComplex C c) ≌ HomologicalComplex (Karoubi C) c`.

When the category `C` is idempotent complete, it is shown that
`HomologicalComplex (Karoubi C) c` is also idempotent complete.

-/

@[expose] public section


namespace CategoryTheory

open Category

variable {C : Type*} [Category* C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}

namespace Idempotents

namespace Karoubi

namespace HomologicalComplex

variable {P Q : Karoubi (HomologicalComplex C c)} (f : P ⟶ Q) (n : ι)

@[simp, reassoc]
/-
**CategoryTheory.Idempotents.Karoubi.HomologicalComplex.p_comp_d** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Idempotents.Karoubi.HomologicalComplex`。
形式化陈述：p_comp_d : P.p.f n ≫ f.f.f n = f.f.f n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.congr_hom`：congr_hom {C D : HomologicalComplex V c} {
f g : C ⟶ D} (w : f = g) (i : ι) : f.f i = g.f i
· 使用定理 `CategoryTheory.Idempotents.Karoubi.p_comp`：p_comp {P Q : Karoubi C} (f :
 Hom P Q) : P.p ≫ f.f = f.f
-/
theorem p_comp_d : P.p.f n ≫ f.f.f n = f.f.f n :=
  HomologicalComplex.congr_hom (p_comp f) n

@[simp, reassoc]
/-
**CategoryTheory.Idempotents.Karoubi.HomologicalComplex.comp_p_d** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Idempotents.Karoubi.HomologicalComplex`。
形式化陈述：comp_p_d : f.f.f n ≫ Q.p.f n = f.f.f n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.congr_hom`：congr_hom {C D : HomologicalComplex V c} {
f g : C ⟶ D} (w : f = g) (i : ι) : f.f i = g.f i
· 使用定理 `CategoryTheory.Idempotents.Karoubi.comp_p`：comp_p {P Q : Karoubi C} (f :
 Hom P Q) : f.f ≫ Q.p = f.f
-/
theorem comp_p_d : f.f.f n ≫ Q.p.f n = f.f.f n :=
  HomologicalComplex.congr_hom (comp_p f) n

@[reassoc]
/-
**CategoryTheory.Idempotents.Karoubi.HomologicalComplex.p_comm_f** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Idempotents.Karoubi.HomologicalComplex`。
形式化陈述：p_comm_f : P.p.f n ≫ f.f.f n = f.f.f n ≫ Q.p.f n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.congr_hom`：congr_hom {C D : HomologicalComplex V c} {
f g : C ⟶ D} (w : f = g) (i : ι) : f.f i = g.f i
· 使用定理 `CategoryTheory.Idempotents.Karoubi.p_comm`：p_comm {P Q : Karoubi C} (f :
 Hom P Q) : P.p ≫ f.f = f.f ≫ Q.p
-/
theorem p_comm_f : P.p.f n ≫ f.f.f n = f.f.f n ≫ Q.p.f n :=
  HomologicalComplex.congr_hom (p_comm f) n

variable (P)

@[simp, reassoc]
/-
**CategoryTheory.Idempotents.Karoubi.HomologicalComplex.p_idem** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Idempotents.Karoubi.HomologicalComplex`。
形式化陈述：p_idem : P.p.f n ≫ P.p.f n = P.p.f n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.congr_hom`：congr_hom {C D : HomologicalComplex V c} {
f g : C ⟶ D} (w : f = g) (i : ι) : f.f i = g.f i
· 使用定理 `CategoryTheory.Idempotents.Karoubi.idem`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] (self : CategoryTheory.Idempotents.Karoubi C),  
 CategoryTheory.CategoryStruc…
-/
theorem p_idem : P.p.f n ≫ P.p.f n = P.p.f n :=
  HomologicalComplex.congr_hom P.idem n

end HomologicalComplex

end Karoubi

open Karoubi

namespace KaroubiHomologicalComplexEquivalence

namespace Functor

/-- The functor `Karoubi (HomologicalComplex C c) ⥤ HomologicalComplex (Karoubi C) c`,
on objects. -/
@[simps]
/-
**CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Functor.obj** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Idempotents.KaroubiHomologicalComplexEqu
ivalence.Functor`。
形式化陈述：obj (P : Karoubi (HomologicalComplex C c)) : HomologicalComplex (Karoubi C
) c where X n
参数：P : Karoubi (HomologicalComplex C c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Karoubi (HomologicalComplex C c) ⥤ HomologicalComplex (Karoubi C) c
`,
on objects.
-/
def obj (P : Karoubi (HomologicalComplex C c)) : HomologicalComplex (Karoubi C) c where
  X n :=
    ⟨P.X.X n, P.p.f n, by
      simpa only [HomologicalComplex.comp_f] using HomologicalComplex.congr_hom P.idem n⟩
  d i j := { f := P.p.f i ≫ P.X.d i j }
  shape i j hij := by simp only [hom_eq_zero_iff]; cat_disch

set_option backward.defeqAttrib.useBackward true in
/-- The functor `Karoubi (HomologicalComplex C c) ⥤ HomologicalComplex (Karoubi C) c`,
on morphisms. -/
@[simps]
/-
**CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Functor.map** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Idempotents.KaroubiHomologicalComplexEqu
ivalence.Functor`。
形式化陈述：map {P Q : Karoubi (HomologicalComplex C c)} (f : P ⟶ Q) : obj P ⟶ obj Q w
here f n
参数：HomologicalComplex C c；f : P ⟶ Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Karoubi (HomologicalComplex C c) ⥤ HomologicalComplex (Karoubi C) c
`,
on morphisms.
-/
def map {P Q : Karoubi (HomologicalComplex C c)} (f : P ⟶ Q) : obj P ⟶ obj Q where
  f n :=
    { f := f.f.f n }

end Functor

/-- The functor `Karoubi (HomologicalComplex C c) ⥤ HomologicalComplex (Karoubi C) c`. -/
@[simps]
/-
**CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.functor** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.Idempotents.KaroubiHomologicalComplexEquival
ence`。
形式化陈述：functor : Karoubi (HomologicalComplex C c) ⥤ HomologicalComplex (Karoubi C
) c where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Karoubi (HomologicalComplex C c) ⥤ HomologicalComplex (Karoubi C) c
`.
-/
def functor : Karoubi (HomologicalComplex C c) ⥤ HomologicalComplex (Karoubi C) c where
  obj := Functor.obj
  map f := Functor.map f

namespace Inverse

/-- The functor `HomologicalComplex (Karoubi C) c ⥤ Karoubi (HomologicalComplex C c)`,
on objects -/
@[simps]
/-
**CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Inverse.obj** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Idempotents.KaroubiHomologicalComplexEqu
ivalence.Inverse`。
形式化陈述：obj (K : HomologicalComplex (Karoubi C) c) : Karoubi (HomologicalComplex C
 c) where X
参数：K : HomologicalComplex (Karoubi C) c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `HomologicalComplex (Karoubi C) c ⥤ Karoubi (HomologicalComplex C c)
`,
on objects
-/
def obj (K : HomologicalComplex (Karoubi C) c) : Karoubi (HomologicalComplex C c) where
  X :=
    { X := fun n => (K.X n).X
      d := fun i j => (K.d i j).f
      shape := fun i j hij => hom_eq_zero_iff.mp (K.shape i j hij)
      d_comp_d' := fun i j k _ _ => by
        simpa only [comp_f] using hom_eq_zero_iff.mp (K.d_comp_d i j k) }
  p := { f := fun n => (K.X n).p }

set_option backward.defeqAttrib.useBackward true in
/-- The functor `HomologicalComplex (Karoubi C) c ⥤ Karoubi (HomologicalComplex C c)`,
on morphisms -/
@[simps]
/-
**CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.Inverse.map** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Idempotents.KaroubiHomologicalComplexEqu
ivalence.Inverse`。
形式化陈述：map {K L : HomologicalComplex (Karoubi C) c} (f : K ⟶ L) : obj K ⟶ obj L w
here f
参数：Karoubi C；f : K ⟶ L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `HomologicalComplex (Karoubi C) c ⥤ Karoubi (HomologicalComplex C c)
`,
on morphisms
-/
def map {K L : HomologicalComplex (Karoubi C) c} (f : K ⟶ L) : obj K ⟶ obj L where
  f :=
    { f := fun n => (f.f n).f
      comm' := fun i j hij => by simpa only [comp_f] using! hom_ext_iff.mp (f.comm' i j hij) }

end Inverse

/-- The functor `HomologicalComplex (Karoubi C) c ⥤ Karoubi (HomologicalComplex C c)`. -/
@[simps]
/-
**CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.inverse** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.Idempotents.KaroubiHomologicalComplexEquival
ence`。
形式化陈述：inverse : HomologicalComplex (Karoubi C) c ⥤ Karoubi (HomologicalComplex C
 c) where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `HomologicalComplex (Karoubi C) c ⥤ Karoubi (HomologicalComplex C c)
`.
-/
def inverse : HomologicalComplex (Karoubi C) c ⥤ Karoubi (HomologicalComplex C c) where
  obj := Inverse.obj
  map f := Inverse.map f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The counit isomorphism of the equivalence
`Karoubi (HomologicalComplex C c) ≌ HomologicalComplex (Karoubi C) c`. -/
@[simps!]
/-
**CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.counitIso** 是 
Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Idempotents.KaroubiHomologicalComplexEquiv
alence`。
形式化陈述：counitIso : inverse ⋙ functor ≅ 𝟭 (HomologicalComplex (Karoubi C) c)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit isomorphism of the equivalence
`Karoubi (HomologicalComplex C c) ≌ HomologicalComplex (Karoubi C) c`.
-/
def counitIso : inverse ⋙ functor ≅ 𝟭 (HomologicalComplex (Karoubi C) c) :=
  eqToIso (Functor.ext (fun P => HomologicalComplex.ext (by cat_disch) (by simp))
    (by cat_disch))

set_option backward.defeqAttrib.useBackward true in
/-- The unit isomorphism of the equivalence
`Karoubi (HomologicalComplex C c) ≌ HomologicalComplex (Karoubi C) c`. -/
@[simps]
/-
**CategoryTheory.Idempotents.KaroubiHomologicalComplexEquivalence.unitIso** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.Idempotents.KaroubiHomologicalComplexEquival
ence`。
形式化陈述：unitIso : 𝟭 (Karoubi (HomologicalComplex C c)) ≅ functor ⋙ inverse where h
om
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit isomorphism of the equivalence
`Karoubi (HomologicalComplex C c) ≌ HomologicalComplex (Karoubi C) c`.
-/
def unitIso : 𝟭 (Karoubi (HomologicalComplex C c)) ≅ functor ⋙ inverse where
  hom :=
    { app := fun P =>
        { f :=
            { f := fun n => P.p.f n
              comm' := fun i j _ => by
                dsimp
                simp only [HomologicalComplex.Hom.comm, HomologicalComplex.Hom.comm_assoc,
                  HomologicalComplex.p_idem] }
          comm := by
            ext n
            dsimp
            simp only [HomologicalComplex.p_idem] }
      naturality := fun P Q φ => by
        ext
        dsimp
        simp only [HomologicalComplex.comp_p_d,
          HomologicalComplex.p_comp_d] }
  inv :=
    { app := fun P =>
        { f :=
            { f := fun n => P.p.f n
              comm' := fun i j _ => by
                dsimp
                simp only [HomologicalComplex.Hom.comm, assoc, HomologicalComplex.p_idem] }
          comm := by
            ext n
            dsimp
            simp only [HomologicalComplex.p_idem] }
      naturality := fun P Q φ => by
        ext
        dsimp
        simp only [HomologicalComplex.comp_p_d, HomologicalComplex.p_comp_d] }
  hom_inv_id := by
    ext
    dsimp
    simp only [HomologicalComplex.p_idem]
  inv_hom_id := by
    ext
    dsimp
    simp only [HomologicalComplex.p_idem]

end KaroubiHomologicalComplexEquivalence

variable (C) (c)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence `Karoubi (HomologicalComplex C c) ≌ HomologicalComplex (Karoubi C) c`. -/
@[simps]
/-
**CategoryTheory.Idempotents.karoubiHomologicalComplexEquivalence** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Idempotents`。
形式化陈述：karoubiHomologicalComplexEquivalence : Karoubi (HomologicalComplex C c) ≌ 
HomologicalComplex (Karoubi C) c where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `Karoubi (HomologicalComplex C c) ≌ HomologicalComplex (Karoubi 
C) c`.
-/
def karoubiHomologicalComplexEquivalence :
    Karoubi (HomologicalComplex C c) ≌ HomologicalComplex (Karoubi C) c where
  functor := KaroubiHomologicalComplexEquivalence.functor
  inverse := KaroubiHomologicalComplexEquivalence.inverse
  unitIso := KaroubiHomologicalComplexEquivalence.unitIso
  counitIso := KaroubiHomologicalComplexEquivalence.counitIso

variable (α : Type*) [AddRightCancelSemigroup α] [One α]

set_option backward.isDefEq.respectTransparency.types false in
/-- The equivalence `Karoubi (ChainComplex C α) ≌ ChainComplex (Karoubi C) α`. -/
@[simps!]
/-
**CategoryTheory.Idempotents.karoubiChainComplexEquivalence** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Idempotents`。
形式化陈述：karoubiChainComplexEquivalence : Karoubi (ChainComplex C α) ≌ ChainComplex
 (Karoubi C) α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G

--- 原说明 ---
The equivalence `Karoubi (ChainComplex C α) ≌ ChainComplex (Karoubi C) α`.
-/
def karoubiChainComplexEquivalence : Karoubi (ChainComplex C α) ≌ ChainComplex (Karoubi C) α :=
  karoubiHomologicalComplexEquivalence C (ComplexShape.down α)

set_option backward.isDefEq.respectTransparency.types false in
/-- The equivalence `Karoubi (CochainComplex C α) ≌ CochainComplex (Karoubi C) α`. -/
@[simps!]
/-
**CategoryTheory.Idempotents.karoubiCochainComplexEquivalence** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Idempotents`。
形式化陈述：karoubiCochainComplexEquivalence : Karoubi (CochainComplex C α) ≌ CochainC
omplex (Karoubi C) α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G

--- 原说明 ---
The equivalence `Karoubi (CochainComplex C α) ≌ CochainComplex (Karoubi C) α`.
-/
def karoubiCochainComplexEquivalence :
    Karoubi (CochainComplex C α) ≌ CochainComplex (Karoubi C) α :=
  karoubiHomologicalComplexEquivalence C (ComplexShape.up α)
/-
**CategoryTheory.Idempotents.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Idempote
nts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsIdempotentComplete C] : IsIdempotentComplete (HomologicalComplex C c) := by
  rw [isIdempotentComplete_iff_of_equivalence
      ((toKaroubiEquivalence C).mapHomologicalComplex c),
    ← isIdempotentComplete_iff_of_equivalence (karoubiHomologicalComplexEquivalence C c)]
  infer_instance

end Idempotents

end CategoryTheory

