/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Skeletal

/-!
# The monoid on the skeleton of a monoidal category

The skeleton of a monoidal category is a monoid.

## Main results

* `Skeleton.instMonoid`, for monoidal categories.
* `Skeleton.instCommMonoid`, for braided monoidal categories.

-/

@[expose] public section


namespace CategoryTheory

open MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- If `C` is monoidal and skeletal, it is a monoid.
See note [reducible non-instances]. -/
/-
**CategoryTheory.monoidOfSkeletalMonoidal** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory`。
形式化陈述：monoidOfSkeletalMonoidal (hC : Skeletal C) : Monoid C where mul X Y
参数：hC : Skeletal C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is monoidal and skeletal, it is a monoid.
See note [reducible non-instances].
-/
abbrev monoidOfSkeletalMonoidal (hC : Skeletal C) : Monoid C where
  mul X Y := X ⊗ Y
  one := 𝟙_ C
  one_mul X := hC ⟨λ_ X⟩
  mul_one X := hC ⟨ρ_ X⟩
  mul_assoc X Y Z := hC ⟨α_ X Y Z⟩

/-- If `C` is braided and skeletal, it is a commutative monoid. -/
/-
**CategoryTheory.commMonoidOfSkeletalBraided** 是 Mathlib 中的一个缩写定义，位于命名空间 `Catego
ryTheory`。
形式化陈述：commMonoidOfSkeletalBraided [BraidedCategory C] (hC : Skeletal C) : CommMo
noid C
参数：hC : Skeletal C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is braided and skeletal, it is a commutative monoid.
-/
abbrev commMonoidOfSkeletalBraided [BraidedCategory C] (hC : Skeletal C) : CommMonoid C :=
  { monoidOfSkeletalMonoidal hC with mul_comm := fun X Y => hC ⟨β_ X Y⟩ }

namespace Skeleton

/-- The skeleton of a monoidal category has a monoidal structure itself, induced by the equivalence.
-/
/-
**CategoryTheory.Skeleton.instMonoidalCategory** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Skeleton`。
形式化陈述：instMonoidalCategory : MonoidalCategory (Skeleton C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The skeleton of a monoidal category has a monoidal structure itself, induced by 
the equivalence.
-/
noncomputable instance instMonoidalCategory : MonoidalCategory (Skeleton C) :=
  Monoidal.transport (skeletonEquivalence C).symm

/--
The skeleton of a monoidal category can be viewed as a monoid, where the multiplication is given by
the tensor product, and satisfies the monoid axioms since it is a skeleton.
-/
/-
**CategoryTheory.Skeleton.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.S
keleton`。
形式化陈述：instMonoid : Monoid (Skeleton C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The skeleton of a monoidal category can be viewed as a monoid, where the multipl
ication is given by
the tensor product, and satisfies the monoid axioms since it is a skeleton.
-/
noncomputable instance instMonoid : Monoid (Skeleton C) :=
  monoidOfSkeletalMonoidal (skeleton_isSkeleton _).skel
/-
**CategoryTheory.Skeleton.mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Skele
ton`。
形式化陈述：mul_eq (X Y : Skeleton C) : X * Y = toSkeleton (X.out otimes Y.out)
参数：X Y : Skeleton C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_eq (X Y : Skeleton C) : X * Y = toSkeleton (X.out ⊗ Y.out) := rfl
/-
**CategoryTheory.Skeleton.one_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Skele
ton`。
形式化陈述：one_eq : (1 : Skeleton C) = toSkeleton (𝟙_ C)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_eq : (1 : Skeleton C) = toSkeleton (𝟙_ C) := rfl
/-
**CategoryTheory.Skeleton.toSkeleton_tensorObj** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Skeleton`。
形式化陈述：toSkeleton_tensorObj (X Y : C) : toSkeleton (X otimes Y) = toSkeleton X * 
toSkeleton Y
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
-/
theorem toSkeleton_tensorObj (X Y : C) : toSkeleton (X ⊗ Y) = toSkeleton X * toSkeleton Y :=
  let φ := (skeletonEquivalence C).symm.unitIso.app; Quotient.sound ⟨φ X ⊗ᵢ φ Y⟩

/-- The skeleton of a braided monoidal category has a braided monoidal structure itself, induced by
the equivalence. -/
/-
**CategoryTheory.Skeleton.instBraidedCategory** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Skeleton`。
形式化陈述：instBraidedCategory [BraidedCategory C] : BraidedCategory (Skeleton C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The skeleton of a braided monoidal category has a braided monoidal structure its
elf, induced by
the equivalence.
-/
noncomputable instance instBraidedCategory [BraidedCategory C] : BraidedCategory (Skeleton C) :=
  (BraidedCategory.ofFullyFaithful
    (Monoidal.equivalenceTransported (skeletonEquivalence C).symm).inverse :)

/--
The skeleton of a braided monoidal category can be viewed as a commutative monoid, where the
multiplication is given by the tensor product, and satisfies the monoid axioms since it is a
skeleton.
-/
/-
**CategoryTheory.Skeleton.instCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Skeleton`。
形式化陈述：instCommMonoid [BraidedCategory C] : CommMonoid (Skeleton C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The skeleton of a braided monoidal category can be viewed as a commutative monoi
d, where the
multiplication is given by the tensor product, and satisfies the monoid axioms s
ince it is a
skeleton.
-/
noncomputable instance instCommMonoid [BraidedCategory C] : CommMonoid (Skeleton C) :=
  commMonoidOfSkeletalBraided (skeleton_isSkeleton _).skel

end Skeleton

open CategoryTheory.Functor

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (skeletonEquivalence C).functor.Monoidal :=
  inferInstanceAs (Monoidal.equivalenceTransported (skeletonEquivalence C).symm).inverse.Monoidal
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (skeletonEquivalence C).inverse.Monoidal :=
  inferInstanceAs (Monoidal.equivalenceTransported (skeletonEquivalence C).symm).functor.Monoidal

variable {D : Type*} [Category* D] [MonoidalCategory D] (F : C ⥤ D) (e : C ≌ D)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [F.LaxMonoidal] : F.mapSkeleton.LaxMonoidal := .comp ..
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [F.OplaxMonoidal] : F.mapSkeleton.OplaxMonoidal := .comp ..
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [F.Monoidal] : F.mapSkeleton.Monoidal := .instComp ..

/-- A monoidal functor between skeletal monoidal categories induces a monoid homomorphism. -/
/-
**CategoryTheory.Skeletal.monoidHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sk
eletal`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.MonoidalCategory C] →       {D : Type u_1} →         [inst_2 : C
ategoryTheory.Category.{v_1, u_1} D] →           [inst_3 : CategoryTheory.Monoid
alCategory D] →             (F : CategoryTheory.Functor C D) →               [F.
Monoidal] →                 (hC : CategoryTheory.Skeletal C) →                  
 (hD : CategoryTheory.Skeletal D) →                     have x := CategoryTheory
.monoidOfSkeletalMonoidal hC;                     have x_1 := CategoryTheory.mon
oidOfSkeletalMonoidal hD;                     C →* D
参数：F : CategoryTheory.Functor C D；hC : CategoryTheory.Skeletal C；hD : CategoryTh
eory.Skeletal D。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monoidal functor between skeletal monoidal categories induces a monoid homomor
phism.
-/
def Skeletal.monoidHom [F.Monoidal] (hC : Skeletal C) (hD : Skeletal D) :
    let _ := monoidOfSkeletalMonoidal hC
    let _ := monoidOfSkeletalMonoidal hD
    C →* D := by
  intros; exact
  { toFun := F.obj
    map_one' := hD ⟨(Monoidal.εIso F).symm⟩
    map_mul' X Y := hD ⟨(Monoidal.μIso F X Y).symm⟩ }

/-- A monoidal functor between monoidal categories induces a monoid homomorphism between
the skeleta. -/
/-
**CategoryTheory.Skeleton.monoidHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sk
eleton`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.MonoidalCategory C] →       {D : Type u_1} →         [inst_2 : C
ategoryTheory.Category.{v_1, u_1} D] →           [inst_3 : CategoryTheory.Monoid
alCategory D] →             (F : CategoryTheory.Functor C D) → [F.Monoidal] → Ca
tegoryTheory.Skeleton C →* CategoryTheory.Skeleton D
参数：F : CategoryTheory.Functor C D。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.skeleton_skeletal`：skeleton_skeletal : Skeletal (Skeleton
 C)

--- 原说明 ---
A monoidal functor between monoidal categories induces a monoid homomorphism bet
ween
the skeleta.
-/
noncomputable def Skeleton.monoidHom [F.Monoidal] : Skeleton C →* Skeleton D :=
  (skeleton_skeletal C).monoidHom F.mapSkeleton (skeleton_skeletal D)

/-- A monoidal equivalence between skeletal monoidal categories induces a monoid isomorphism. -/
/-
**CategoryTheory.Skeletal.mulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ske
letal`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.MonoidalCategory C] →       {D : Type u_1} →         [inst_2 : C
ategoryTheory.Category.{v_1, u_1} D] →           [inst_3 : CategoryTheory.Monoid
alCategory D] →             (e : C ≌ D) →               [e.functor.Monoidal] →  
               (hC : CategoryTheory.Skeletal C) →                   (hD : Catego
ryTheory.Skeletal D) →                     have x := CategoryTheory.monoidOfSkel
etalMonoidal hC;                     have x_1 := CategoryTheory.monoidOfSkeletal
Monoidal hD;                     C ≃* D
参数：e : C ≌ D；hC : CategoryTheory.Skeletal C；hD : CategoryTheory.Skeletal D。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monoidal equivalence between skeletal monoidal categories induces a monoid iso
morphism.
-/
def Skeletal.mulEquiv [e.functor.Monoidal] (hC : Skeletal C) (hD : Skeletal D) :
    let _ := monoidOfSkeletalMonoidal hC
    let _ := monoidOfSkeletalMonoidal hD
    C ≃* D := by
  intros; exact
  { toFun := e.functor.obj
    invFun := e.inverse.obj
    left_inv X := hC ⟨(e.unitIso.app X).symm⟩
    right_inv X := hD ⟨e.counitIso.app X⟩
    map_mul' X Y := hD ⟨(Monoidal.μIso e.functor X Y).symm⟩ }

/-- A monoidal equivalence between monoidal categories induces a monoid isomorphism between
the skeleta. -/
/-
**CategoryTheory.Skeleton.mulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ske
leton`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.MonoidalCategory C] →       {D : Type u_1} →         [inst_2 : C
ategoryTheory.Category.{v_1, u_1} D] →           [inst_3 : CategoryTheory.Monoid
alCategory D] →             (e : C ≌ D) → [e.functor.Monoidal] → CategoryTheory.
Skeleton C ≃* CategoryTheory.Skeleton D
参数：e : C ≌ D。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.skeleton_skeletal`：skeleton_skeletal : Skeletal (Skeleton
 C)

--- 原说明 ---
A monoidal equivalence between monoidal categories induces a monoid isomorphism 
between
the skeleta.
-/
noncomputable def Skeleton.mulEquiv [e.functor.Monoidal] : Skeleton C ≃* Skeleton D :=
  (skeleton_skeletal C).mulEquiv
    (((skeletonEquivalence C).trans e).trans (skeletonEquivalence D).symm) (skeleton_skeletal D)

end CategoryTheory

