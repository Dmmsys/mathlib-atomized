/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# The category of (commutative) (additive) groups has a zero object.

`AddCommGroup` also has zero morphisms. For definitional reasons, we infer this from preadditivity
rather than from the existence of a zero object.
-/

public section

open CategoryTheory Limits

universe u

namespace GrpCat

@[to_additive]
/-
**GrpCat.isZero_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `GrpCat`。
形式化陈述：isZero_of_subsingleton (G : GrpCat) [Subsingleton G] : IsZero G
参数：G : GrpCat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `GrpCat.hom_ext`：hom_ext {X Y : GrpCat} {f g : X ⟶ Y} (hf : f.hom = g.hom
) : f = g
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem isZero_of_subsingleton (G : GrpCat) [Subsingleton G] : IsZero G := by
  refine ⟨fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩⟩
  · ext x
    have : x = 1 := Subsingleton.elim _ _
    rw [this, map_one, map_one]
  · ext
    subsingleton

@[to_additive AddGrpCat.hasZeroObject]
/-
**GrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `GrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasZeroObject GrpCat :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

@[to_additive]
/-
**GrpCat.subsingleton_of_isZero** 是 Mathlib 中的一个引理，位于命名空间 `GrpCat`。
形式化陈述：subsingleton_of_isZero {G : GrpCat} (h : Limits.IsZero G) : Subsingleton G
参数：h : Limits.IsZero G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
· 使用定理 `GrpCat.isZero_of_subsingleton`：isZero_of_subsingleton (G : GrpCat) [Subs
ingleton G] : IsZero G
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
-/
lemma subsingleton_of_isZero {G : GrpCat} (h : Limits.IsZero G) :
    Subsingleton G :=
  (h.iso (isZero_of_subsingleton <| .of PUnit)).groupIsoToMulEquiv.subsingleton

@[to_additive]
/-
**GrpCat.isZero_iff_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `GrpCat`。
形式化陈述：isZero_iff_subsingleton {G : GrpCat} : Limits.IsZero G ↔ Subsingleton G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `GrpCat.subsingleton_of_isZero`：subsingleton_of_isZero {G : GrpCat} (h : 
Limits.IsZero G) : Subsingleton G
· 使用定理 `GrpCat.isZero_of_subsingleton`：isZero_of_subsingleton (G : GrpCat) [Subs
ingleton G] : IsZero G
-/
lemma isZero_iff_subsingleton {G : GrpCat} : Limits.IsZero G ↔ Subsingleton G :=
  ⟨fun h ↦ subsingleton_of_isZero h, fun _ ↦ isZero_of_subsingleton G⟩

@[to_additive]
/-
**GrpCat.isZero_of_iff_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `GrpCat`。
形式化陈述：isZero_of_iff_subsingleton {G : Type*} [Group G] : Limits.IsZero (GrpCat.o
f G) ↔ Subsingleton G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `GrpCat.isZero_iff_subsingleton`：isZero_iff_subsingleton {G : GrpCat} : L
imits.IsZero G ↔ Subsingleton G
-/
lemma isZero_of_iff_subsingleton {G : Type*} [Group G] :
    Limits.IsZero (GrpCat.of G) ↔ Subsingleton G :=
  isZero_iff_subsingleton

end GrpCat

namespace CommGrpCat

@[to_additive]
/-
**CommGrpCat.isZero_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `CommGrpCat`。
形式化陈述：isZero_of_subsingleton (G : CommGrpCat) [Subsingleton G] : IsZero G
参数：G : CommGrpCat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CommGrpCat.hom_ext`：hom_ext {X Y : CommGrpCat} {f g : X ⟶ Y} (hf : f.hom
 = g.hom) : f = g
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem isZero_of_subsingleton (G : CommGrpCat) [Subsingleton G] : IsZero G := by
  refine ⟨fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨1⟩, fun f => ?_⟩⟩⟩
  · ext x
    have : x = 1 := Subsingleton.elim _ _
    rw [this, map_one, map_one]
  · ext
    subsingleton

@[to_additive AddCommGrpCat.hasZeroObject]
/-
**CommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasZeroObject CommGrpCat :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩

@[to_additive]
/-
**CommGrpCat.subsingleton_of_isZero** 是 Mathlib 中的一个引理，位于命名空间 `CommGrpCat`。
形式化陈述：subsingleton_of_isZero {G : CommGrpCat} (h : Limits.IsZero G) : Subsinglet
on G
参数：h : Limits.IsZero G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
· 使用定理 `CommGrpCat.isZero_of_subsingleton`：isZero_of_subsingleton (G : CommGrpCa
t) [Subsingleton G] : IsZero G
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
-/
lemma subsingleton_of_isZero {G : CommGrpCat} (h : Limits.IsZero G) :
    Subsingleton G :=
  (h.iso (isZero_of_subsingleton <| .of PUnit)).commGroupIsoToMulEquiv.subsingleton

@[to_additive]
/-
**CommGrpCat.isZero_iff_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `CommGrpCat`。
形式化陈述：isZero_iff_subsingleton {G : CommGrpCat} : Limits.IsZero G ↔ Subsingleton 
G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CommGrpCat.subsingleton_of_isZero`：subsingleton_of_isZero {G : CommGrpCa
t} (h : Limits.IsZero G) : Subsingleton G
· 使用定理 `CommGrpCat.isZero_of_subsingleton`：isZero_of_subsingleton (G : CommGrpCa
t) [Subsingleton G] : IsZero G
-/
lemma isZero_iff_subsingleton {G : CommGrpCat} : Limits.IsZero G ↔ Subsingleton G :=
  ⟨fun h ↦ subsingleton_of_isZero h, fun _ ↦ isZero_of_subsingleton G⟩

@[to_additive]
/-
**CommGrpCat.isZero_of_iff_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `CommGrpCat`。
形式化陈述：isZero_of_iff_subsingleton {G : Type*} [CommGroup G] : Limits.IsZero (Comm
GrpCat.of G) ↔ Subsingleton G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CommGrpCat.isZero_iff_subsingleton`：isZero_iff_subsingleton {G : CommGrp
Cat} : Limits.IsZero G ↔ Subsingleton G
-/
lemma isZero_of_iff_subsingleton {G : Type*} [CommGroup G] :
    Limits.IsZero (CommGrpCat.of G) ↔ Subsingleton G :=
  isZero_iff_subsingleton

end CommGrpCat

