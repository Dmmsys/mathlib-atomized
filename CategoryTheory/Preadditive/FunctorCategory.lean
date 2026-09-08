/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Preadditive structure on functor categories

If `C` and `D` are categories and `D` is preadditive,
then `C ⥤ D` is also preadditive.

-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Limits Preadditive

variable {C D : Type*} [Category* C] [Category* D] [Preadditive D]

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F G : C ⥤ D} : Zero (F ⟶ G) where
  zero := { app := fun _ => 0 }
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F G : C ⥤ D} : Add (F ⟶ G) where
  add α β := { app := fun X => α.app X + β.app X }
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F G : C ⥤ D} : Neg (F ⟶ G) where
  neg α := { app := fun X => -α.app X }
/-
**CategoryTheory.functorCategoryPreadditive** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory`。
形式化陈述：functorCategoryPreadditive : Preadditive (C ⥤ D) where homGroup F G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance functorCategoryPreadditive : Preadditive (C ⥤ D) where
  homGroup F G :=
    { nsmul n α :=
        { app := n • α.app
          naturality X Y f := by
            simp only [Pi.smul_apply, comp_nsmul, NatTrans.naturality, nsmul_comp] }
      zsmul n α :=
        { app := n • α.app
          naturality X Y f := by
            simp only [Pi.smul_apply, comp_zsmul, NatTrans.naturality, zsmul_comp] }
      sub α β := { app := fun X => α.app X - β.app X }
      add_assoc _ _ _ := NatTrans.ext <| add_assoc _ _ _
      zero_add _ := NatTrans.ext <| zero_add _
      add_zero _ := NatTrans.ext <| add_zero _
      nsmul_zero _ := NatTrans.ext <| zero_nsmul _
      nsmul_succ _ _ := NatTrans.ext <| succ_nsmul _ _
      sub_eq_add_neg _ _ := NatTrans.ext <| sub_eq_add_neg _ _
      zsmul_zero' _ := NatTrans.ext <| zero_zsmul _
      zsmul_succ' _ _ := NatTrans.ext <| SubNegMonoid.zsmul_succ' _ _
      zsmul_neg' _ _ := NatTrans.ext <| SubNegMonoid.zsmul_neg' _ _
      neg_add_cancel _ := NatTrans.ext <| neg_add_cancel _
      add_comm _ _ := NatTrans.ext <| add_comm _ _ }
  add_comp _ _ _ _ _ _ := NatTrans.ext <| funext fun _ ↦ add_comp _ _ _ _ _ _
  comp_add _ _ _ _ _ _ := NatTrans.ext <| funext fun _ ↦ comp_add _ _ _ _ _ _

namespace NatTrans

variable {F G : C ⥤ D}

/-- Application of a natural transformation at a fixed object,
as group homomorphism -/
@[simps]
/-
**CategoryTheory.NatTrans.appHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.NatTr
ans`。
形式化陈述：appHom (X : C) : (F ⟶ G) ->+ (F.obj X ⟶ G.obj X) where toFun α
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Application of a natural transformation at a fixed object,
as group homomorphism
-/
def appHom (X : C) : (F ⟶ G) →+ (F.obj X ⟶ G.obj X) where
  toFun α := α.app X
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
/-
**CategoryTheory.NatTrans.app_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Nat
Trans`。
形式化陈述：app_zero (X : C) : (0 : F ⟶ G).app X = 0
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem app_zero (X : C) : (0 : F ⟶ G).app X = 0 :=
  rfl

@[simp]
/-
**CategoryTheory.NatTrans.app_add** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.NatT
rans`。
形式化陈述：app_add (X : C) (α β : F ⟶ G) : (α + β).app X = α.app X + β.app X
参数：X : C；α β : F ⟶ G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem app_add (X : C) (α β : F ⟶ G) : (α + β).app X = α.app X + β.app X :=
  rfl

@[simp]
/-
**CategoryTheory.NatTrans.app_sub** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.NatT
rans`。
形式化陈述：app_sub (X : C) (α β : F ⟶ G) : (α - β).app X = α.app X - β.app X
参数：X : C；α β : F ⟶ G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem app_sub (X : C) (α β : F ⟶ G) : (α - β).app X = α.app X - β.app X :=
  rfl

@[simp]
/-
**CategoryTheory.NatTrans.app_neg** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.NatT
rans`。
形式化陈述：app_neg (X : C) (α : F ⟶ G) : (-α).app X = -α.app X
参数：X : C；α : F ⟶ G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem app_neg (X : C) (α : F ⟶ G) : (-α).app X = -α.app X :=
  rfl

@[simp]
/-
**CategoryTheory.NatTrans.app_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Na
tTrans`。
形式化陈述：app_nsmul (X : C) (α : F ⟶ G) (n : Nat) : (n • α).app X = n • α.app X
参数：X : C；α : F ⟶ G；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem app_nsmul (X : C) (α : F ⟶ G) (n : ℕ) : (n • α).app X = n • α.app X :=
  rfl

@[simp]
/-
**CategoryTheory.NatTrans.app_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Na
tTrans`。
形式化陈述：app_zsmul (X : C) (α : F ⟶ G) (n : Int) : (n • α).app X = n • α.app X
参数：X : C；α : F ⟶ G；n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem app_zsmul (X : C) (α : F ⟶ G) (n : ℤ) : (n • α).app X = n • α.app X :=
  rfl

@[simp]
/-
**CategoryTheory.NatTrans.app_units_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.NatTrans`。
形式化陈述：app_units_zsmul (X : C) (α : F ⟶ G) (n : Intˣ) : (n • α).app X = n • α.app
 X
参数：X : C；α : F ⟶ G；n : Intˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem app_units_zsmul (X : C) (α : F ⟶ G) (n : ℤˣ) : (n • α).app X = n • α.app X :=
  rfl

@[simp]
/-
**CategoryTheory.NatTrans.app_sum** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.NatT
rans`。
形式化陈述：app_sum {ι : Type*} (s : Finset ι) (X : C) (α : ι -> (F ⟶ G)) : (∑ i in s,
 α i).app X = ∑ i in s, (α i).app X
参数：s : Finset ι；X : C；α : ι -> (F ⟶ G)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem app_sum {ι : Type*} (s : Finset ι) (X : C) (α : ι → (F ⟶ G)) :
    (∑ i ∈ s, α i).app X = ∑ i ∈ s, (α i).app X := by
  simp only [← appHom_apply, map_sum]

end NatTrans

end CategoryTheory

