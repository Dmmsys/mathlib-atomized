/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.Grp.Preadditive

/-!
# The forget functor is corepresentable

It is shown that the forget functor `AddCommGrpCat.{u} ⥤ Type u` is corepresentable
by `ULift ℤ`. Similar results are obtained for the variants `CommGrpCat`, `AddGrpCat`
and `GrpCat`.

-/

@[expose] public section

universe u

open CategoryTheory Opposite

/-!
### `(ULift ℤ →+ G) ≃ G`

These universe-monomorphic variants of `zmultiplesHom`/`zpowersHom` are put here since they
shouldn't be useful outside of category theory.
-/

/-- The equivalence `(ULift ℤ →+ G) ≃ G` for any additive group `G`. -/
@[simps!]
/-
**uliftZMultiplesHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：uliftZMultiplesHom (G : Type u) [AddGroup G] : G ≃ (ULift.{u} Int ->+ G)
参数：G : Type u。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The equivalence `(ULift ℤ →+ G) ≃ G` for any additive group `G`.
-/
def uliftZMultiplesHom (G : Type u) [AddGroup G] : G ≃ (ULift.{u} ℤ →+ G) :=
  (zmultiplesHom _).trans AddEquiv.ulift.symm.addMonoidHomCongrLeftEquiv

/-- The equivalence `(ULift (Multiplicative ℤ) →* G) ≃ G` for any group `G`. -/
@[simps!]
/-
**uliftZPowersHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：uliftZPowersHom (G : Type u) [Group G] : G ≃ (ULift.{u} (Multiplicative In
t) ->* G)
参数：G : Type u。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The equivalence `(ULift (Multiplicative ℤ) →* G) ≃ G` for any group `G`.
-/
def uliftZPowersHom (G : Type u) [Group G] : G ≃ (ULift.{u} (Multiplicative ℤ) →* G) :=
  (zpowersHom _).trans MulEquiv.ulift.symm.monoidHomCongrLeftEquiv

/-- The forget functor `GrpCat.{u} ⥤ Type u` is corepresentable. -/
/-
**GrpCat.coyonedaObjIsoForget** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：GrpCat.coyonedaObjIsoForget : coyoneda.obj (op (of (ULift.{u} (Multiplicat
ive Int)))) ≅ forget GrpCat.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The forget functor `GrpCat.{u} ⥤ Type u` is corepresentable.
-/
def GrpCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative ℤ)))) ≅ forget GrpCat.{u} :=
  NatIso.ofComponents fun M ↦
    (ConcreteCategory.homEquiv.trans (uliftZPowersHom M.carrier).symm).toIso

/-- The forget functor `CommGrpCat.{u} ⥤ Type u` is corepresentable. -/
/-
**CommGrpCat.coyonedaObjIsoForget** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CommGrpCat.coyonedaObjIsoForget : coyoneda.obj (op (of (ULift.{u} (Multipl
icative Int)))) ≅ forget CommGrpCat.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The forget functor `CommGrpCat.{u} ⥤ Type u` is corepresentable.
-/
def CommGrpCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative ℤ)))) ≅ forget CommGrpCat.{u} :=
  NatIso.ofComponents fun M ↦
    (ConcreteCategory.homEquiv.trans (uliftZPowersHom M.carrier).symm).toIso

/-- The forget functor `AddGrpCat.{u} ⥤ Type u` is corepresentable. -/
/-
**AddGrpCat.coyonedaObjIsoForget** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddGrpCat.coyonedaObjIsoForget : coyoneda.obj (op (of (ULift.{u} Int))) ≅ 
forget AddGrpCat.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The forget functor `AddGrpCat.{u} ⥤ Type u` is corepresentable.
-/
def AddGrpCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} ℤ))) ≅ forget AddGrpCat.{u} :=
  NatIso.ofComponents fun M ↦
    (ConcreteCategory.homEquiv.trans (uliftZMultiplesHom M.carrier).symm).toIso

/-- The forget functor `AddCommGrpCat.{u} ⥤ Type u` is corepresentable. -/
/-
**AddCommGrpCat.coyonedaObjIsoForget** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddCommGrpCat.coyonedaObjIsoForget : coyoneda.obj (op (of (ULift.{u} Int))
) ≅ forget AddCommGrpCat.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The forget functor `AddCommGrpCat.{u} ⥤ Type u` is corepresentable.
-/
def AddCommGrpCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} ℤ))) ≅ forget AddCommGrpCat.{u} :=
  NatIso.ofComponents fun M ↦
    (ConcreteCategory.homEquiv.trans (uliftZMultiplesHom M.carrier).symm).toIso
/-
**GrpCat.forget_isCorepresentable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：GrpCat.forget_isCorepresentable : (forget GrpCat.{u}).IsCorepresentable
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCorepresentable.mk'`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C (Type v₁)} {X : 
C}   (e : CategoryTheory.coyoneda.…
-/
instance GrpCat.forget_isCorepresentable :
    (forget GrpCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' GrpCat.coyonedaObjIsoForget
/-
**CommGrpCat.forget_isCorepresentable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CommGrpCat.forget_isCorepresentable : (forget CommGrpCat.{u}).IsCorepresen
table
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCorepresentable.mk'`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C (Type v₁)} {X : 
C}   (e : CategoryTheory.coyoneda.…
-/
instance CommGrpCat.forget_isCorepresentable :
    (forget CommGrpCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' CommGrpCat.coyonedaObjIsoForget
/-
**AddGrpCat.forget_isCorepresentable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddGrpCat.forget_isCorepresentable : (forget AddGrpCat.{u}).IsCorepresenta
ble
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCorepresentable.mk'`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C (Type v₁)} {X : 
C}   (e : CategoryTheory.coyoneda.…
-/
instance AddGrpCat.forget_isCorepresentable :
    (forget AddGrpCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' AddGrpCat.coyonedaObjIsoForget
/-
**AddCommGrpCat.forget_isCorepresentable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddCommGrpCat.forget_isCorepresentable : (forget AddCommGrpCat.{u}).IsCore
presentable
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCorepresentable.mk'`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C (Type v₁)} {X : 
C}   (e : CategoryTheory.coyoneda.…
-/
instance AddCommGrpCat.forget_isCorepresentable :
    (forget AddCommGrpCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' AddCommGrpCat.coyonedaObjIsoForget
/-
**uliftZMultiplesHom_apply_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uliftZMultiplesHom_apply_add (G : Type u) [AddCommGroup G] (x y : G) : uli
ftZMultiplesHom G (x + y) = uliftZMultiplesHom G x + uliftZMultiplesHom G y
参数：G : Type u；x y : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uliftZMultiplesHom_apply_apply`：∀ (G : Type u) [inst : AddGroup G] (a : 
G) (x : ULift.{u, 0} ℤ), ((uliftZMultiplesHom G) a) x = AddEquiv.ulift x • a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem uliftZMultiplesHom_apply_add (G : Type u) [AddCommGroup G] (x y : G) :
    uliftZMultiplesHom G (x + y) = uliftZMultiplesHom G x + uliftZMultiplesHom G y := by
  ext
  simp_all only [uliftZMultiplesHom_apply_apply, smul_add, AddMonoidHom.add_apply]

/-- The additive equivalence `(ℤ ⟶ G) ≃+ G` -/
@[simps!]
/-
**AddCommGrpCat.uliftZMultiplesAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddCommGrpCat.uliftZMultiplesAddEquiv (G : AddCommGrpCat) : (of (ULift Int
) ⟶ G) ≃+ G
参数：G : AddCommGrpCat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive equivalence `(ℤ ⟶ G) ≃+ G`
-/
def AddCommGrpCat.uliftZMultiplesAddEquiv (G : AddCommGrpCat) : (of (ULift ℤ) ⟶ G) ≃+ G :=
  AddCommGrpCat.homAddEquiv.trans
    (AddEquiv.mk' (uliftZMultiplesHom G) (uliftZMultiplesHom_apply_add G)).symm
