/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
/-!
# Base change for the dual of a module

* `Module.Dual.congr` : equivalent modules have equivalent duals.

If `f : Module.Dual R V` and `Algebra R A`, then

* `Module.Dual.baseChange A f` is the element
  of `Module.Dual A (A ⊗[R] V)` deduced by base change.

* `Module.Dual.baseChangeHom` is the `R`-linear map
  given by `Module.Dual.baseChange`.

* `IsBaseChange.dual` : for finite free modules, taking dual commutes with base change.

-/

@[expose] public section

namespace Module.Dual

open TensorProduct LinearEquiv

variable {R : Type*} [CommSemiring R]
  {V : Type*} [AddCommMonoid V] [Module R V]
  {W : Type*} [AddCommMonoid W] [Module R W]
  (A : Type*) [CommSemiring A] [Algebra R A]

/-- Equivalent modules have equivalent duals. -/
/-
**Module.Dual.congr** 是 Mathlib 中的一个定义，位于命名空间 `Module.Dual`。
形式化陈述：{R : Type u_1} →   [inst : CommSemiring R] →     {V : Type u_2} →       [i
nst_1 : AddCommMonoid V] →         [inst_2 : _root_.Module R V] →           {W :
 Type u_3} →             [inst_3 : AddCommMonoid W] →               [inst_4 : _r
oot_.Module R W] → (V ≃ₗ[R] W) → Module.Dual R V ≃ₗ[R] Module.Dual R W
参数：V ≃ₗ[R] W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalent modules have equivalent duals.
-/
@[simps!] def congr (e : V ≃ₗ[R] W) :
    Dual R V ≃ₗ[R] Dual R W := congrLeft R R e

/-- `LinearMap.baseChange` for `Module.Dual`. -/
/-
**Module.Dual.baseChange** 是 Mathlib 中的一个定义，位于命名空间 `Module.Dual`。
形式化陈述：baseChange : Dual R V ->ₗ[R] Dual A (A otimes[R] V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearMap.baseChange` for `Module.Dual`.
-/
def baseChange : Dual R V →ₗ[R] Dual A (A ⊗[R] V) :=
  (AlgebraTensorModule.rid R A A).compRight R ∘ₗ LinearMap.baseChangeHom R A V R

@[simp]
/-
**Module.Dual.baseChange_apply_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Module.Dual`。
形式化陈述：baseChange_apply_tmul (f : Dual R V) (a : A) (v : V) : f.baseChange A (a o
timesₜ v) = (f v) • a
参数：f : Dual R V；a : A；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem baseChange_apply_tmul (f : Dual R V) (a : A) (v : V) :
    f.baseChange A (a ⊗ₜ v) = (f v) • a :=
  rfl

variable {B : Type*} [CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

open AlgebraTensorModule in
/-
**Module.Dual.baseChange_baseChange** 是 Mathlib 中的一个定理，位于命名空间 `Module.Dual`。
形式化陈述：baseChange_baseChange (f : Dual R V) : (f.baseChange A).baseChange B = (co
ngr (cancelBaseChange R A B B V)).symm (f.baseChange B)
参数：f : Dual R V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Module.Dual.congr_symm_apply_apply`：∀ {R : Type u_1} [inst : CommSemirin
g R] {V : Type u_2} [inst_1 : AddCommMonoid V] [inst_2 : _root_.Module R V]   {W
 : Type u_3} [inst_3 : A…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem baseChange_baseChange (f : Dual R V) :
    (f.baseChange A).baseChange B = (congr (cancelBaseChange R A B B V)).symm (f.baseChange B) := by
  ext; simp

end Module.Dual

namespace IsBaseChange

open Module TensorProduct

variable {R : Type*} [CommSemiring R]
  {V : Type*} [AddCommMonoid V] [Module R V]
  {W : Type*} [AddCommMonoid W] [Module R W]
  {A : Type*} [CommSemiring A] [Algebra R A] [Module A W] [IsScalarTower R A W]
  {j : V →ₗ[R] W} (ibc : IsBaseChange A j)

/-- The base change of an element of the dual. -/
/-
**IsBaseChange.toDual** 是 Mathlib 中的一个定义，位于命名空间 `IsBaseChange`。
形式化陈述：toDual : Dual R V ->ₗ[R] Dual A W
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The base change of an element of the dual.
-/
noncomputable def toDual :
    Dual R V →ₗ[R] Dual A W :=
  linearMapLeftRightHom ibc (Algebra.linearMap R A)
/-
**IsBaseChange.toDual_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：toDual_comp_apply (f : Dual R V) (v : V) : ibc.toDual f (j v) = algebraMap
 R A (f v)
参数：f : Dual R V；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsBaseChange.linearMapLeftRightHom_comp_apply`：∀ {R : Type u_1} [inst : 
CommSemiring R] {S : Type u_2} [inst_1 : CommSemiring S] [inst_2 : Algebra R S] 
{M : Type u_3}   [inst_3 : AddCommM…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toDual_comp_apply (f : Dual R V) (v : V) :
    ibc.toDual f (j v) = algebraMap R A (f v) := by
  simp [toDual, linearMapLeftRightHom_comp_apply]
/-
**IsBaseChange.toDual_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：toDual_apply (f : Dual R V) : ibc.toDual f = (f.baseChange A).congr ibc.eq
uiv
参数：f : Dual R V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBaseChange.algHom_ext`：IsBaseChange.algHom_ext (g₁ g₂ : N ->ₗ[S] Q) (e
 : forall x, g₁ (f x) = g₂ (f x)) : g₁ = g₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsBaseChange.toDual_comp_apply`：toDual_comp_apply (f : Dual R V) (v : V)
 : ibc.toDual f (j v) = algebraMap R A (f v)
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `Module.Dual.congr_apply_apply`：∀ {R : Type u_1} [inst : CommSemiring R] 
{V : Type u_2} [inst_1 : AddCommMonoid V] [inst_2 : _root_.Module R V]   {W : Ty
pe u_3} [inst_3 : A…
· 使用定理 `IsBaseChange.equiv_symm_apply`：IsBaseChange.equiv_symm_apply (m : M) : h
.equiv.symm (f m) = 1 otimesₜ m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toDual_apply (f : Dual R V) :
    ibc.toDual f = (f.baseChange A).congr ibc.equiv := by
  apply ibc.algHom_ext
  intro v
  simp [toDual_comp_apply, Algebra.algebraMap_eq_smul_one]

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
/-- The linear map underlying `IsBaseChange.toDualBaseChangeLinearEquiv`. -/
/-
**IsBaseChange.toDualBaseChangeAux** 是 Mathlib 中的一个定义，位于命名空间 `IsBaseChange`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map underlying `IsBaseChange.toDualBaseChangeLinearEquiv`.
-/
private noncomputable def toDualBaseChangeAux :
    A ⊗[R] Dual R V →ₗ[A] Dual A W where
  toAddHom := (TensorProduct.lift {
    toFun a := a • ibc.toDual
    map_add' a b := by simp [add_smul]
    map_smul' r a := by simp }).toAddHom
  map_smul' a g := by
    induction g using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => aesop
    | tmul b f => simp [TensorProduct.smul_tmul', mul_smul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
/-
**IsBaseChange.toDualBaseChangeAux_tmul** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem toDualBaseChangeAux_tmul (a : A) (f : Dual R V) (v : V) :
    (ibc.toDualBaseChangeAux (a ⊗ₜ[R] f)) (j v) = a * algebraMap R A (f v) := by
  simp [toDualBaseChangeAux, toDual_comp_apply]

variable [Free R V] [Module.Finite R V]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The linear equivalence underlying `IsBaseChange.dual`. -/
/-
**IsBaseChange.toDualBaseChange** 是 Mathlib 中的一个定义，位于命名空间 `IsBaseChange`。
形式化陈述：toDualBaseChange : A otimes[R] Dual R V ≃ₗ[A] Dual A W
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence underlying `IsBaseChange.dual`.
-/
noncomputable def toDualBaseChange :
    A ⊗[R] Dual R V ≃ₗ[A] Dual A W := by
  apply LinearEquiv.ofBijective ibc.toDualBaseChangeAux
  let b := Free.chooseBasis R V
  set ι := Free.ChooseBasisIndex R V
  have ibc_pow : IsBaseChange A ((Algebra.linearMap R A).compLeft ι) := (linearMap R A).finitePow ι
  suffices ibc.toDualBaseChangeAux =
      (((b.constr R).symm.baseChange ..).trans ibc_pow.equiv).trans ((ibc.basis b).constr A) from
    this ▸ LinearEquiv.bijective _
  ext f w
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  induction w using ibc.inductionOn with
  | zero => simp
  | tmul v =>
    simp only [toDualBaseChangeAux_tmul, one_mul]
    conv_lhs => rw [← Basis.sum_equivFun b v, map_sum]
    simp [LinearEquiv.baseChange, basis_repr_comp_apply]
  | smul a w h => simp [h]
  | add x y hx hy => simp [map_add, hx, hy]
/-
**IsBaseChange.toDualBaseChange_tmul** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：toDualBaseChange_tmul (a : A) (f : Dual R V) (v : V) : (ibc.toDualBaseChan
ge (a otimesₜ[R] f)) (j v) = a * algebraMap R A (f v)
参数：a : A；f : Dual R V；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.LinearAlgebra.Dual.BaseChange.0.IsBaseChange.toDualBase
ChangeAux_tmul`：∀ {R : Type u_1} [inst : CommSemiring R] {V : Type u_2} [inst_1 
: AddCommMonoid V] [inst_2 : _root_.Module R V]   {W : Type u_3} [inst_3 : A…
-/
theorem toDualBaseChange_tmul (a : A) (f : Dual R V) (v : V) :
    (ibc.toDualBaseChange (a ⊗ₜ[R] f)) (j v) = a * algebraMap R A (f v) :=
  toDualBaseChangeAux_tmul ibc a f v

set_option backward.isDefEq.respectTransparency false in
/-
**IsBaseChange.dual** 是 Mathlib 中的一个定理，位于命名空间 `IsBaseChange`。
形式化陈述：dual : IsBaseChange A (ibc.toDual)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsBaseChange.of_equiv`：IsBaseChange.of_equiv (e : S otimes[R] M ≃ₗ[S] N)
 (he : forall x, e (1 otimesₜ x) = f x) : IsBaseChange S f
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dual : IsBaseChange A (ibc.toDual) := by
  apply of_equiv (toDualBaseChange ibc)
  intro f
  simp [toDualBaseChange, toDualBaseChangeAux]

end IsBaseChange

