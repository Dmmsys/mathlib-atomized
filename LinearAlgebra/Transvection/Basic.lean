/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Transvections in a module

* When `f : Module.Dual R V` and `v : V`,
  `LinearMap.transvection f v` is the linear map given by `x ↦ x + f x • v`,

* `LinearMap.transvection.det` shows that the determinant of
  `LinearMap.transvection f v` is equal to `1 + f v`.

* If, moreover, `f v = 0`, then `LinearEquiv.transvection` shows that it is
  a linear equivalence.

* `LinearMap.transvections R V`: the set of transvections.

* `LinearEquiv.dilatransvections R V`: the set of linear equivalences
  whose associated linear map is of the form `LinearMap.transvection f v`.

* `LinearEquiv.transvection.det` shows that it has determinant `1`.

## Note on terminology

In the mathematical literature, linear maps of the form `LinearMap.transvection f v`
are only called “transvections” when `f v = 0`. Otherwise, they are sometimes
called “dilations” (especially if `f v ≠ -1`).

The definition is almost the same as that of `Module.preReflection f v`,
up to a sign change, which are interesting when `f v = 2`, because they give “reflections”.

-/

@[expose] public section

namespace LinearMap

open Module

variable {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]

/-- The transvection associated with a linear form `f` and a vector `v`.

NB. In mathematics, these linear maps are only called “transvections” when `f v = 0`.
See also `Module.preReflection` for a similar definition, up to a sign. -/
/-
**LinearMap.transvection** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：transvection (f : Dual R V) (v : V) : V ->ₗ[R] V where toFun x
参数：f : Dual R V；v : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transvection associated with a linear form `f` and a vector `v`.

NB. In mathematics, these linear maps are only called “transvections” when `f v 
= 0`.
See also `Module.preReflection` for a similar definition, up to a sign.
-/
def transvection (f : Dual R V) (v : V) : V →ₗ[R] V where
  toFun x := x + f x • v
  map_add' x y := by simp [add_add_add_comm, add_smul]
  map_smul' r x := by simp [smul_eq_mul, smul_add, mul_smul]

namespace transvection

open Submodule LinearMap

/-
**LinearMap.transvection.apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.transvection
`。
形式化陈述：apply (f : Dual R V) (v x : V) : transvection f v x = x + f x • v
参数：f : Dual R V；v x : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply (f : Dual R V) (v x : V) :
    transvection f v x = x + f x • v :=
  rfl
/-
**LinearMap.transvection.comp_of_left_eq_apply** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map.transvection`。
形式化陈述：comp_of_left_eq_apply {f : Dual R V} {v w : V} {x : V} (hw : f w = 0) : tr
ansvection f v (transvection f w x) = transvection f (v + w) x
参数：hw : f w = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_of_left_eq_apply {f : Dual R V} {v w : V} {x : V} (hw : f w = 0) :
    transvection f v (transvection f w x) = transvection f (v + w) x := by
  simp [transvection, map_add, hw, add_assoc]
/-
**LinearMap.transvection.comp_of_left_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.tr
ansvection`。
形式化陈述：comp_of_left_eq {f : Dual R V} {v w : V} (hw : f w = 0) : (transvection f 
v) ∘ₗ (transvection f w) = transvection f (v + w)
参数：hw : f w = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.transvection.comp_of_left_eq_apply`：comp_of_left_eq_apply {f :
 Dual R V} {v w : V} {x : V} (hw : f w = 0) : transvection f v (transvection f w
 x) = transvection f (v + w) x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_of_left_eq {f : Dual R V} {v w : V} (hw : f w = 0) :
    (transvection f v) ∘ₗ (transvection f w) = transvection f (v + w) := by
  ext; simp [comp_of_left_eq_apply hw]
/-
**LinearMap.transvection.comp_of_right_eq_apply** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rMap.transvection`。
形式化陈述：comp_of_right_eq_apply {f g : Dual R V} {v : V} {x : V} (hf : f v = 0) : (
transvection f v) (transvection g v x) = transvection (f + g) v x
参数：hf : f v = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_of_right_eq_apply {f g : Dual R V} {v : V} {x : V} (hf : f v = 0) :
    (transvection f v) (transvection g v x) = transvection (f + g) v x := by
  simp [transvection, map_add, hf, add_smul, add_assoc]
/-
**LinearMap.transvection.comp_of_right_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.t
ransvection`。
形式化陈述：comp_of_right_eq {f g : Dual R V} {v : V} (hf : f v = 0) : (transvection f
 v) ∘ₗ (transvection g v) = transvection (f + g) v
参数：hf : f v = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.transvection.comp_of_right_eq_apply`：comp_of_right_eq_apply {f
 g : Dual R V} {v : V} {x : V} (hf : f v = 0) : (transvection f v) (transvection
 g v x) = transvection (f + g) v x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_of_right_eq {f g : Dual R V} {v : V} (hf : f v = 0) :
    (transvection f v) ∘ₗ (transvection g v) = transvection (f + g) v := by
  ext; simp [comp_of_right_eq_apply hf]

@[simp]
/-
**LinearMap.transvection.of_left_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.tr
ansvection`。
形式化陈述：of_left_eq_zero (v : V) : transvection (0 : Dual R V) v = id
参数：v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_left_eq_zero (v : V) :
    transvection (0 : Dual R V) v = id := by
  ext
  simp [transvection]

@[simp]
/-
**LinearMap.transvection.of_right_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.t
ransvection`。
形式化陈述：of_right_eq_zero (f : Dual R V) : transvection f 0 = id
参数：f : Dual R V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_right_eq_zero (f : Dual R V) :
    transvection f 0 = id := by
  ext
  simp [transvection]
/-
**LinearMap.transvection.comp_smul_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.tra
nsvection`。
形式化陈述：comp_smul_smul {f : Dual R V} {v : V} {r s : R} : transvection f (r • v) ∘
ₗ transvection f (s • v) = transvection f ((r + s + s * f v * r) • v)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_smul_smul {f : Dual R V} {v : V} {r s : R} :
    transvection f (r • v) ∘ₗ transvection f (s • v) =
      transvection f ((r + s + s * f v * r) • v) := by
  ext x
  simp only [LinearMap.comp_apply, apply, map_add, map_smul, add_assoc]
  simp only [smul_add, ← mul_smul, ← add_smul, ← mul_add (f x), mul_assoc]
/-
**LinearMap.transvection.eq_id_of_finrank_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap.transvection`。
形式化陈述：eq_id_of_finrank_le_one {R V : Type*} [CommSemiring R] [AddCommMonoid V] [
Module R V] [Free R V] [Module.Finite R V] [StrongRankCondition R] {f : Dual R V
} {v : V} (hfv : f v = 0) (h1 : finrank R V <= 1) : transvection f v = id
参数：hfv : f v = 0；h1 : finrank R V <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Basis.sum_equivFun`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6
} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] 
[inst_3 : Finty…
· 使用定理 `Finset.sum_eq_single_of_mem`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] {s : Finset ι} {f : ι → M},   ∀ a ∈ s, (∀ b ∈ s, b ≠ a → f b = 0) 
→ ∑ x ∈ s, f x = …
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Mathlib.Tactic.IntervalCases.of_le_right`：of_le_right [LE α] (h : (a : α
) <= b) (eq : b = b') : a <= b'
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.finrank_eq_zero_iff_of_free`：finrank_eq_zero_iff_of_free [Module.
Free R M] [Module.Finite R M] : Module.finrank R M = 0 ↔ Subsingleton M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
（共 34 条，此处仅展示前 30 条）
-/
theorem eq_id_of_finrank_le_one
    {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
    [Free R V] [Module.Finite R V] [StrongRankCondition R]
    {f : Dual R V} {v : V} (hfv : f v = 0) (h1 : finrank R V ≤ 1) :
    transvection f v = id := by
  interval_cases h : finrank R V
  · have : Subsingleton V := (finrank_eq_zero_iff_of_free R V).mp h
    simp [Subsingleton.eq_zero v]
  · let b := finBasis R V
    ext x
    suffices f x • v = 0 by
      simp [apply, this]
    let i : Fin (finrank R V) := ⟨0, by simp [h]⟩
    suffices ∀ x, x = b.repr x i • (b i) by
      rw [this v, map_smul, smul_eq_mul, mul_comm] at hfv
      rw [this x, this v, map_smul, smul_eq_mul, ← mul_smul, mul_assoc, hfv, mul_zero, zero_smul]
    intro x
    have : x = ∑ i, b.repr x i • b i := (b.sum_equivFun x).symm
    rwa [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (by grind)] at this
/-
**LinearMap.transvection.congr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.transvection
`。
形式化陈述：congr {W : Type*} [AddCommMonoid W] [Module R W] (f : Dual R V) (v : V) (e
 : V ≃ₗ[R] W) : e ∘ₗ (transvection f v) ∘ₗ e.symm = transvection (f ∘ₗ e.symm) (
e v)
参数：f : Dual R V；v : V；e : V ≃ₗ[R] W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem congr {W : Type*} [AddCommMonoid W] [Module R W]
    (f : Dual R V) (v : V) (e : V ≃ₗ[R] W) :
    e ∘ₗ (transvection f v) ∘ₗ e.symm = transvection (f ∘ₗ e.symm) (e v) := by
  ext; simp [transvection.apply]

end LinearMap.transvection

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

namespace LinearEquiv

open LinearMap LinearMap.transvection Module Submodule

/-- The transvection associated with a linear form `f` and a vector `v` such that `f v = 0`. -/
/-
**LinearEquiv.transvection** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：{R : Type u_1} →   {V : Type u_2} →     [inst : Ring R] →       [inst_1 : 
AddCommGroup V] → [inst_2 : _root_.Module R V] → {f : Module.Dual R V} → {v : V}
 → f v = 0 → V ≃ₗ[R] V
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transvection associated with a linear form `f` and a vector `v` such that `f
 v = 0`.
-/
def transvection {f : Dual R V} {v : V} (h : f v = 0) :
    V ≃ₗ[R] V where
  toFun := LinearMap.transvection f v
  invFun := LinearMap.transvection f (-v)
  map_add' x y := by simp [map_add]
  map_smul' r x := by simp
  left_inv x := by
    simp [comp_of_left_eq_apply h]
  right_inv x := by
    have h' : f (-v) = 0 := by simp [h]
    simp [comp_of_left_eq_apply h']

namespace transvection

/-
**LinearEquiv.transvection.apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv.transvec
tion`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V]   {f : Module.Dual R V} {v : V} (h : f v = 0) (x : 
V), (LinearEquiv.transvection h) x = x + f x • v
参数：h : f v = 0；x : V；LinearEquiv.transvection h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply {f : Dual R V} {v : V} (h : f v = 0) (x : V) :
    transvection h x = x + f x • v :=
  rfl

@[simp]
/-
**LinearEquiv.transvection.coe_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearEqui
v.transvection`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V]   {f : Module.Dual R V} {v : V} (h : f v = 0), ↑(Li
nearEquiv.transvection h) = LinearMap.transvection f v
参数：h : f v = 0；LinearEquiv.transvection h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLinearMap {f : Dual R V} {v : V} (h : f v = 0) :
    LinearEquiv.transvection h = LinearMap.transvection f v :=
  rfl

@[simp]
/-
**LinearEquiv.transvection.coe_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv.tran
svection`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V]   {f : Module.Dual R V} {v x : V} {h : f v = 0}, (L
inearEquiv.transvection h) x = (LinearMap.transvection f v) x
参数：LinearEquiv.transvection h；LinearMap.transvection f v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_apply {f : Dual R V} {v x : V} {h : f v = 0} :
    LinearEquiv.transvection h x = LinearMap.transvection f v x :=
  rfl
/-
**LinearEquiv.transvection.trans_of_left_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearEqu
iv.transvection`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V]   {f : Module.Dual R V} {v w : V} (hv : f v = 0) (h
w : f w = 0)   (hvw : autoParam (f (v + w) = 0) LinearEquiv.transvection.trans_o
f_left_eq._auto_1),   LinearEquiv.transvection hw ≪≫ₗ LinearEquiv.transvection h
v = LinearEquiv.transvection hvw
参数：hv : f v = 0；hw : f w = 0；hvw : autoParam (f (v + w) = 0) LinearEquiv.transve
ction.trans_of_left_eq._auto_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.transvection.comp_of_left_eq_apply`：comp_of_left_eq_apply {f :
 Dual R V} {v w : V} {x : V} (hw : f w = 0) : transvection f v (transvection f w
 x) = transvection f (v + w) x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trans_of_left_eq {f : Dual R V} {v w : V}
    (hv : f v = 0) (hw : f w = 0) (hvw : f (v + w) = 0 := by simp [hv, hw]) :
    (transvection hw).trans (transvection hv) = transvection hvw := by
  ext; simp [comp_of_left_eq_apply hw]
/-
**LinearEquiv.transvection.trans_of_right_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearEq
uiv.transvection`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V]   {f g : Module.Dual R V} {v : V} (hf : f v = 0) (h
g : g v = 0)   (hfg : autoParam ((f + g) v = 0) LinearEquiv.transvection.trans_o
f_right_eq._auto_1),   LinearEquiv.transvection hg ≪≫ₗ LinearEquiv.transvection 
hf = LinearEquiv.transvection hfg
参数：hf : f v = 0；hg : g v = 0；hfg : autoParam ((f + g) v = 0) LinearEquiv.transve
ction.trans_of_right_eq._auto_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.transvection.comp_of_right_eq_apply`：comp_of_right_eq_apply {f
 g : Dual R V} {v : V} {x : V} (hf : f v = 0) : (transvection f v) (transvection
 g v x) = transvection (f + g) v x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trans_of_right_eq {f g : Dual R V} {v : V}
    (hf : f v = 0) (hg : g v = 0) (hfg : (f + g) v = 0 := by simp [hf, hg]) :
    (transvection hg).trans (transvection hf) = transvection hfg := by
  ext; simp [comp_of_right_eq_apply hf]

@[simp]
/-
**LinearEquiv.transvection.of_left_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearEqui
v.transvection`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V] (v : V)   (hv : optParam (0 v = 0) ⋯), LinearEquiv.
transvection hv = LinearEquiv.refl R V
参数：v : V；hv : optParam (0 v = 0) ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.transvection.of_left_eq_zero`：of_left_eq_zero (v : V) : transv
ection (0 : Dual R V) v = id
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `LinearEquiv.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Sem
iring R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomI
nvPair σ σ'] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_left_eq_zero (v : V) (hv := LinearMap.zero_apply v) :
    transvection hv = refl R V := by
  ext; simp [transvection]

@[simp]
/-
**LinearEquiv.transvection.of_right_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearEqu
iv.transvection`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V]   (f : Module.Dual R V) (hf : optParam (f 0 = 0) ⋯)
, LinearEquiv.transvection hf = LinearEquiv.refl R V
参数：f : Module.Dual R V；hf : optParam (f 0 = 0) ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.transvection.of_right_eq_zero`：of_right_eq_zero (f : Dual R V)
 : transvection f 0 = id
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `LinearEquiv.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Sem
iring R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomI
nvPair σ σ'] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_right_eq_zero (f : Dual R V) (hf := f.map_zero) :
    transvection hf = refl R V := by
  ext; simp [transvection]
/-
**LinearEquiv.transvection.symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv.transv
ection`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V]   {f : Module.Dual R V} {v : V} (hv : f v = 0) (hv'
 : autoParam (f (-v) = 0) LinearEquiv.transvection.symm_eq._auto_1),   (LinearEq
uiv.transvection hv).symm = LinearEquiv.transvection hv'
参数：hv : f v = 0；hv' : autoParam (f (-v) = 0) LinearEquiv.transvection.symm_eq._a
uto_1；LinearEquiv.transvection hv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.transvection.comp_of_left_eq_apply`：comp_of_left_eq_apply {f :
 Dual R V} {v w : V} {x : V} (hw : f w = 0) : transvection f v (transvection f w
 x) = transvection f (v + w) x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `LinearMap.transvection.of_right_eq_zero`：of_right_eq_zero (f : Dual R V)
 : transvection f 0 = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symm_eq {f : Dual R V} {v : V}
    (hv : f v = 0) (hv' : f (-v) = 0 := by simp [hv]) :
    (transvection hv).symm = transvection hv' := by
  ext;
  simp [symm_apply_eq, comp_of_left_eq_apply hv']
/-
**LinearEquiv.transvection.inv_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv.transve
ction`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V]   {f : Module.Dual R V} {v : V} (hv : f v = 0) (hv'
 : autoParam (f (-v) = 0) LinearEquiv.transvection.inv_eq._auto_1),   (LinearEqu
iv.transvection hv)⁻¹ = LinearEquiv.transvection hv'
参数：hv : f v = 0；hv' : autoParam (f (-v) = 0) LinearEquiv.transvection.inv_eq._au
to_1；LinearEquiv.transvection hv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.transvection.symm_eq`：∀ {R : Type u_1} {V : Type u_2} [inst 
: Ring R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R V]   {f : Module.D
ual R V} {v : V} (hv :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_eq {f : Dual R V} {v : V}
    (hv : f v = 0) (hv' : f (-v) = 0 := by simp [hv]) :
    (transvection hv)⁻¹ = transvection hv' :=
  symm_eq hv
/-
**LinearEquiv.transvection.symm_eq'** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv.trans
vection`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V]   {f : Module.Dual R V} {v : V} (hf : f v = 0) (hf'
 : autoParam ((-f) v = 0) LinearEquiv.transvection.symm_eq'._auto_1),   (LinearE
quiv.transvection hf).symm = LinearEquiv.transvection hf'
参数：hf : f v = 0；hf' : autoParam ((-f) v = 0) LinearEquiv.transvection.symm_eq'._
auto_1；LinearEquiv.transvection hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.transvection.comp_of_right_eq_apply`：comp_of_right_eq_apply {f
 g : Dual R V} {v : V} {x : V} (hf : f v = 0) : (transvection f v) (transvection
 g v x) = transvection (f + g) v x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `LinearMap.transvection.of_left_eq_zero`：of_left_eq_zero (v : V) : transv
ection (0 : Dual R V) v = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem symm_eq' {f : Dual R V} {v : V}
    (hf : f v = 0) (hf' : (-f) v = 0 := by simp [hf]) :
    (transvection hf).symm = transvection hf' := by
  ext; simp [symm_apply_eq, comp_of_right_eq_apply hf]
/-
**LinearEquiv.transvection.inv_eq'** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv.transv
ection`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V]   {f : Module.Dual R V} {v : V} (hf : f v = 0) (hf'
 : autoParam ((-f) v = 0) LinearEquiv.transvection.inv_eq'._auto_1),   (LinearEq
uiv.transvection hf)⁻¹ = LinearEquiv.transvection hf'
参数：hf : f v = 0；hf' : autoParam ((-f) v = 0) LinearEquiv.transvection.inv_eq'._a
uto_1；LinearEquiv.transvection hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.transvection.symm_eq'`：∀ {R : Type u_1} {V : Type u_2} [inst
 : Ring R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R V]   {f : Module.
Dual R V} {v : V} (hf :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_eq' {f : Dual R V} {v : V}
    (hf : f v = 0) (hf' : (-f) v = 0 := by simp [hf]) :
    (transvection hf)⁻¹ = transvection hf' :=
  symm_eq' hf

end transvection

/-
**LinearEquiv.mem_fixedSubmodule_transvection_iff** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earEquiv`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V]   {f : Module.Dual R V} {v : V} {hfv : f v = 0} {x 
: V},   x ∈ (↑(LinearEquiv.transvection hfv)).fixedSubmodule ↔ f x • v = 0
参数：↑(LinearEquiv.transvection hfv)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_fixedSubmodule_transvection_iff {f : Dual R V} {v : V} {hfv : f v = 0} {x : V} :
    x ∈ (LinearEquiv.transvection hfv).fixedSubmodule ↔ f x • v = 0 := by
  simp [LinearMap.transvection.apply, add_eq_left]
/-
**LinearEquiv.ker_le_fixedSubmodule_transvection** 是 Mathlib 中的一个定理，位于命名空间 `Line
arEquiv`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V]   {f : Module.Dual R V} {v : V} (hfv : f v = 0), Li
nearMap.ker f ≤ (↑(LinearEquiv.transvection hfv)).fixedSubmodule
参数：hfv : f v = 0；↑(LinearEquiv.transvection hfv)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ker_le_fixedSubmodule_transvection {f : Dual R V} {v : V} (hfv : f v = 0) :
    LinearMap.ker f ≤ (transvection hfv).fixedSubmodule := by
  intro x hx
  rw [mem_ker] at hx
  simp [LinearMap.transvection.apply, hx]

section dilatransvections

variable (R V) in
/-- The set of transvections in the group of linear equivalences -/
/-
**LinearEquiv.transvections** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：(R : Type u_1) →   (V : Type u_2) → [inst : Ring R] → [inst_1 : AddCommGro
up V] → [inst_2 : _root_.Module R V] → Set (V ≃ₗ[R] V)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of transvections in the group of linear equivalences
-/
def transvections : Set (V ≃ₗ[R] V) :=
  { e | ∃ (f : Dual R V) (v : V) (hfv : f v = 0), e = transvection hfv }
/-
**LinearEquiv.mem_transvections_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V] {e : V ≃ₗ[R] V},   e ∈ LinearEquiv.transvections R 
V ↔ ∃ f v, ∃ (hfv : f v = 0), e = LinearEquiv.transvection hfv
参数：hfv : f v = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_transvections_iff {e : V ≃ₗ[R] V} :
    e ∈ transvections R V ↔
      ∃ (f : Dual R V) (v : V) (hfv : f v = 0), e = LinearEquiv.transvection hfv :=
  Iff.rfl
/-
**LinearEquiv.mem_transvections** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V]   {f : Module.Dual R V} {v : V} (hfv : f v = 0), Li
nearEquiv.transvection hfv ∈ LinearEquiv.transvections R V
参数：hfv : f v = 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem mem_transvections {f : Dual R V} {v : V} (hfv : f v = 0) :
    transvection hfv ∈ transvections R V :=
  ⟨f, v, hfv, rfl⟩
/-
**LinearEquiv.refl_mem_transvections** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V],   LinearEquiv.refl R V ∈ LinearEquiv.transvections
 R V
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.transvection.of_left_eq_zero`：∀ {R : Type u_1} {V : Type u_2
} [inst : Ring R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R V] (v : V)
   (hv : optParam (0 v = 0) ⋯)…
-/
@[simp] theorem refl_mem_transvections :
    refl R V ∈ transvections R V :=
  ⟨0, 0, by simp, by aesop⟩
/-
**LinearEquiv.one_mem_transvections** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V],   1 ∈ LinearEquiv.transvections R V
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.refl_mem_transvections`：∀ {R : Type u_1} {V : Type u_2} [ins
t : Ring R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R V],   LinearEqui
v.refl R V ∈ LinearEquiv…
-/
@[simp] theorem one_mem_transvections :
    1 ∈ transvections R V :=
  refl_mem_transvections

@[simp]
/-
**LinearEquiv.symm_mem_transvections_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`
。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V] {e : V ≃ₗ[R] V},   e.symm ∈ LinearEquiv.transvectio
ns R V ↔ e ∈ LinearEquiv.transvections R V
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearEquiv.transvection.symm_eq`：∀ {R : Type u_1} {V : Type u_2} [inst 
: Ring R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R V]   {f : Module.D
ual R V} {v : V} (hv :…
· 使用定理 `LinearEquiv.mem_transvections`：∀ {R : Type u_1} {V : Type u_2} [inst : R
ing R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R V]   {f : Module.Dual
 R V} {v : V} (hfv …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.symm_symm`：symm_symm (e : M ≃ₛₗ[σ] M₂) : e.symm.symm = e
-/
theorem symm_mem_transvections_iff {e : V ≃ₗ[R] V} :
    e.symm ∈ transvections R V ↔ e ∈ transvections R V := by
  suffices ∀ e ∈ transvections R V, e.symm ∈ transvections R V by
    refine ⟨fun h ↦ ?_, this e⟩
    rw [← symm_symm e]
    exact this _ h
  rintro _ ⟨f, v, hv, rfl⟩
  rw [transvection.symm_eq]
  apply mem_transvections

@[simp]
/-
**LinearEquiv.inv_mem_transvections_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V] {e : V ≃ₗ[R] V},   e⁻¹ ∈ LinearEquiv.transvections 
R V ↔ e ∈ LinearEquiv.transvections R V
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.symm_mem_transvections_iff`：∀ {R : Type u_1} {V : Type u_2} 
[inst : Ring R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R V] {e : V ≃ₗ
[R] V},   e.symm ∈ LinearEqu…
-/
theorem inv_mem_transvections_iff {e : V ≃ₗ[R] V} :
    e⁻¹ ∈ transvections R V ↔ e ∈ transvections R V :=
  symm_mem_transvections_iff

open scoped Pointwise in
/-
**LinearEquiv.transvections_pow_mono** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V],   Monotone fun n => LinearEquiv.transvections R V 
^ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pow_right_monotone`：∀ {α : Type u_2} [inst : Monoid α] {s : Set α}, 
1 ∈ s → Monotone fun x => s ^ x
· 使用定理 `LinearEquiv.one_mem_transvections`：∀ {R : Type u_1} {V : Type u_2} [inst
 : Ring R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R V],   1 ∈ LinearE
quiv.transvections R V
-/
theorem transvections_pow_mono :
    Monotone (fun n : ℕ ↦ (transvections R V) ^ n) :=
  Set.pow_right_monotone one_mem_transvections

variable (R V) in
/-- Dilatransvections are linear equivalences `V ≃ₗ[R] V` whose associated linear map are given by
`LinearMap.transvection`, i.e., are of the form `x ↦ x + f x • v` for `f : Dual R V` and `v : V`.

Over a division ring, `LinearEquiv.mem_dilatransvections_iff_rank` shows that they correspond
to the linear equivalences which differ from the identity map by a linear map of rank at most 1. -/
/-
**LinearEquiv.dilatransvections** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：(R : Type u_1) →   (V : Type u_2) → [inst : Ring R] → [inst_1 : AddCommGro
up V] → [inst_2 : _root_.Module R V] → Set (V ≃ₗ[R] V)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dilatransvections are linear equivalences `V ≃ₗ[R] V` whose associated linear ma
p are given by
`LinearMap.transvection`, i.e., are of the form `x ↦ x + f x • v` for `f : Dual 
R V` and `v : V`.

Over a division ring, `LinearEquiv.mem_dilatransvections_iff_rank` shows that th
ey correspond
to the linear equivalences which differ from the identity map by a linear map of
 rank at most 1.
-/
def dilatransvections : Set (V ≃ₗ[R] V) :=
  { e : V ≃ₗ[R] V | ∃ (f : Dual R V) (v : V), e = LinearMap.transvection f v }
/-
**LinearEquiv.transvections_subset_dilatransvections** 是 Mathlib 中的一个定理，位于命名空间 `
LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V],   LinearEquiv.transvections R V ⊆ LinearEquiv.dila
transvections R V
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem transvections_subset_dilatransvections :
    transvections R V ⊆ dilatransvections R V := by
  rintro e ⟨f, v, hfv, rfl⟩
  exact ⟨f, v, by simp⟩

@[simp]
/-
**LinearEquiv.refl_mem_dilatransvections** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`
。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V],   LinearEquiv.refl R V ∈ LinearEquiv.dilatransvect
ions R V
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.transvections_subset_dilatransvections`：∀ {R : Type u_1} {V 
: Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R 
V],   LinearEquiv.transvections R V ⊆ Li…
· 使用定理 `LinearEquiv.one_mem_transvections`：∀ {R : Type u_1} {V : Type u_2} [inst
 : Ring R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R V],   1 ∈ LinearE
quiv.transvections R V
-/
theorem refl_mem_dilatransvections : refl R V ∈ dilatransvections R V :=
  transvections_subset_dilatransvections one_mem_transvections
/-
**LinearEquiv.transvection_mem_transvections** 是 Mathlib 中的一个定理，位于命名空间 `LinearEq
uiv`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V]   {f : Module.Dual R V} {v : V} {hfv : f v = 0}, Li
nearEquiv.transvection hfv ∈ LinearEquiv.transvections R V
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem transvection_mem_transvections {f : Dual R V} {v : V} {hfv : f v = 0} :
    transvection hfv ∈ transvections R V :=
  ⟨f, v, hfv, rfl⟩
/-
**LinearEquiv.transvection_mem_dilatransvections** 是 Mathlib 中的一个定理，位于命名空间 `Line
arEquiv`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V]   {f : Module.Dual R V} {v : V} (hfv : f v = 0), Li
nearEquiv.transvection hfv ∈ LinearEquiv.dilatransvections R V
参数：hfv : f v = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.transvections_subset_dilatransvections`：∀ {R : Type u_1} {V 
: Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R 
V],   LinearEquiv.transvections R V ⊆ Li…
· 使用定理 `LinearEquiv.transvection_mem_transvections`：∀ {R : Type u_1} {V : Type u
_2} [inst : Ring R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R V]   {f 
: Module.Dual R V} {v : V} {hfv …
-/
theorem transvection_mem_dilatransvections {f : Dual R V} {v : V} (hfv : f v = 0) :
    transvection hfv ∈ dilatransvections R V :=
  transvections_subset_dilatransvections transvection_mem_transvections

@[simp]
/-
**LinearEquiv.one_mem_dilatransvections** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V],   1 ∈ LinearEquiv.dilatransvections R V
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.refl_mem_dilatransvections`：∀ {R : Type u_1} {V : Type u_2} 
[inst : Ring R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R V],   Linear
Equiv.refl R V ∈ LinearEquiv…
-/
theorem one_mem_dilatransvections : 1 ∈ dilatransvections R V :=
  refl_mem_dilatransvections

@[simp]
/-
**LinearEquiv.symm_mem_dilatransvections_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearEq
uiv`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V] {e : V ≃ₗ[R] V},   e.symm ∈ LinearEquiv.dilatransve
ctions R V ↔ e ∈ LinearEquiv.dilatransvections R V
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.coe_coe`：coe_coe : ⇑(e : M ->ₛₗ[σ] M₂) = e
· 使用定理 `LinearMap.transvection.apply`：apply (f : Dual R V) (v x : V) : transvect
ion f v x = x + f x • v
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
theorem symm_mem_dilatransvections_iff {e : V ≃ₗ[R] V} :
    e.symm ∈ dilatransvections R V ↔ e ∈ dilatransvections R V := by
  suffices ∀ e ∈ dilatransvections R V, e.symm ∈ dilatransvections R V from
    ⟨by simpa using this e.symm, this e⟩
  rintro e ⟨f, v, he⟩
  use f, - e.symm v
  ext x
  suffices x = e x - f x • v by
    simpa [LinearMap.transvection.apply, ← sub_eq_add_neg, symm_apply_eq]
  rw [eq_comm, sub_eq_iff_eq_add, ← coe_coe, he, LinearMap.transvection.apply]

@[simp]
/-
**LinearEquiv.inv_mem_dilatransvections_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearEqu
iv`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V] {e : V ≃ₗ[R] V},   e⁻¹ ∈ LinearEquiv.dilatransvecti
ons R V ↔ e ∈ LinearEquiv.dilatransvections R V
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.symm_mem_dilatransvections_iff`：∀ {R : Type u_1} {V : Type u
_2} [inst : Ring R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R V] {e : 
V ≃ₗ[R] V},   e.symm ∈ LinearEqu…
-/
theorem inv_mem_dilatransvections_iff {e : V ≃ₗ[R] V} :
    e⁻¹ ∈ dilatransvections R V ↔ e ∈ dilatransvections R V :=
  symm_mem_dilatransvections_iff

/-- The dilatransvection associated with a linear form `f`
and a vector `v` such that `1 + f v` is a unit. -/
/-
**LinearEquiv.dilatransvection** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：{R : Type u_1} →   {V : Type u_2} →     [inst : Ring R] →       [inst_1 : 
AddCommGroup V] →         [inst_2 : _root_.Module R V] → {f : Module.Dual R V} →
 {v : V} → IsUnit (1 + f v) → V ≃ₗ[R] V
参数：1 + f v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dilatransvection associated with a linear form `f`
and a vector `v` such that `1 + f v` is a unit.
-/
noncomputable def dilatransvection {f : Dual R V} {v : V} (h : IsUnit (1 + f v)) :
    V ≃ₗ[R] V where
  toFun := LinearMap.transvection f v
  invFun := LinearMap.transvection f (-h.unit⁻¹ • v)
  map_add' x y := by simp [map_add]
  map_smul' r x := by simp
  left_inv x := by
    nth_rewrite 3 [← one_smul R v]
    rw [← LinearMap.comp_apply, Units.smul_def, LinearMap.transvection.comp_smul_smul]
    simp only [Units.val_neg, one_mul, mul_neg, ← sub_eq_add_neg]
    suffices (-h.unit⁻¹) + 1 - f v * (h.unit⁻¹) = 0 by simp [this]
    rw [sub_eq_zero, neg_add_eq_iff_eq_add]
    nth_rewrite 1 [← one_mul (h.unit⁻¹), Units.val_mul, ← add_mul]
    simp
  right_inv x := by
    simp only [LinearMap.transvection.apply, add_assoc, add_eq_left,
      Units.smul_def]
    rw [smul_smul, ← add_smul]
    suffices (f x * ↑(-h.unit⁻¹) + f (x + (f x * ↑(-h.unit⁻¹)) • v)) = 0 by rw [this, zero_smul]
    rw [LinearMap.map_add, LinearMap.map_smul, smul_eq_mul]
    nth_rewrite 2 [← mul_one (f x)]
    rw [mul_assoc, ← mul_add, ← mul_add]
    rw [← add_assoc, add_comm _ 1, add_assoc]
    nth_rewrite 1 [← mul_one (-h.unit⁻¹), Units.val_mul, Units.val_one, ← mul_add]
    simp

@[simp]
/-
**LinearEquiv.dilatransvection.coe_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Equiv.dilatransvection`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V]   {f : Module.Dual R V} {v : V} {h : IsUnit (1 + f 
v)}, ↑(LinearEquiv.dilatransvection h) = LinearMap.transvection f v
参数：1 + f v；LinearEquiv.dilatransvection h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dilatransvection.coe_toLinearMap {f : Dual R V} {v : V} {h : IsUnit (1 + f v)} :
    (dilatransvection h).toLinearMap = LinearMap.transvection f v :=
  rfl
/-
**LinearEquiv.dilatransvection.apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv.dila
transvection`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V]   {f : Module.Dual R V} {v : V} {h : IsUnit (1 + f 
v)} {x : V}, (LinearEquiv.dilatransvection h) x = x + f x • v
参数：1 + f v；LinearEquiv.dilatransvection h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.neg_smul`：Units.neg_smul [Ring R] [AddCommGroup M] [Module R M] (u
 : Rˣ) (x : M) : -u • x = -(u • x)
· 使用定理 `LinearEquiv.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Sem
iring R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomI
nvPair σ σ'] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dilatransvection.apply {f : Dual R V} {v : V} {h : IsUnit (1 + f v)} {x : V} :
    dilatransvection h x = x + f x • v := by
  simp [dilatransvection, LinearMap.transvection.apply]

@[simp]
/-
**LinearEquiv.dilatransvection_mem_dilatransvections** 是 Mathlib 中的一个定理，位于命名空间 `
LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V]   {f : Module.Dual R V} {v : V} {h : IsUnit (1 + f 
v)},   LinearEquiv.dilatransvection h ∈ LinearEquiv.dilatransvections R V
参数：1 + f v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dilatransvection_mem_dilatransvections {f : Dual R V} {v : V} {h : IsUnit (1 + f v)} :
    dilatransvection h ∈ dilatransvections R V := by
  simp only [dilatransvections, Set.mem_ofPred_eq]
  refine ⟨f, v, by simp⟩

open scoped Pointwise in
/-
**LinearEquiv.dilatransvections_pow_mono** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`
。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module R V],   Monotone fun n => LinearEquiv.dilatransvections 
R V ^ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pow_right_monotone`：∀ {α : Type u_2} [inst : Monoid α] {s : Set α}, 
1 ∈ s → Monotone fun x => s ^ x
· 使用定理 `LinearEquiv.one_mem_dilatransvections`：∀ {R : Type u_1} {V : Type u_2} [
inst : Ring R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R V],   1 ∈ Lin
earEquiv.dilatransvections …
-/
theorem dilatransvections_pow_mono :
    Monotone (fun n : ℕ ↦ (dilatransvections R V) ^ n) :=
  Set.pow_right_monotone one_mem_dilatransvections

section divisionRing

variable {K : Type*} [DivisionRing K] [Module K V]

/-- Over a division ring, `dilatransvections` correspond to linear
equivalences `e` such that the linear map `e - id` has rank at most 1.

See also `LinearEquiv.mem_dilatransvections_iff_finrank`. -/
/-
**LinearEquiv.mem_dilatransvections_iff_rank** 是 Mathlib 中的一个定理，位于命名空间 `LinearEq
uiv`。
形式化陈述：∀ {V : Type u_2} [inst : AddCommGroup V] {K : Type u_3} [inst_1 : Division
Ring K] [inst_2 : _root_.Module K V]   {e : V ≃ₗ[K] V}, e ∈ LinearEquiv.dilatran
svections K V ↔ Module.rank K ↥(↑e - LinearMap.id).range ≤ 1
参数：↑e - LinearMap.id。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `Submodule.rank_mono`：Submodule.rank_mono {s t : Submodule R M} (h : s <=
 t) : Module.rank R s <= Module.rank R t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `rank_span_le`：rank_span_le (s : Set M) : Module.rank R (span R s) <= #s
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
· 使用定理 `Subsingleton.allEq`：∀ {α : Sort u} [self : Subsingleton α] (a b : α), a 
= b
· 使用定理 `rank_zero_iff`：rank_zero_iff : Module.rank R M = 0 ↔ Subsingleton M
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `Ideal.instIsTorsionFreeSubtypeMemSubmodule`：∀ {R : Type u} [inst : Semir
ing R] {S : Type u_1} {A : Type u_2} [inst_1 : Semiring S] [inst_2 : SMul R S]  
 [inst_3 : AddCommMonoid A] [ins…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LinearMap.transvection.of_right_eq_zero`：of_right_eq_zero (f : Dual R V)
 : transvection f 0 = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
Over a division ring, `dilatransvections` correspond to linear
equivalences `e` such that the linear map `e - id` has rank at most 1.

See also `LinearEquiv.mem_dilatransvections_iff_finrank`.
-/
theorem mem_dilatransvections_iff_rank {e : V ≃ₗ[K] V} :
    e ∈ dilatransvections K V ↔
      Module.rank K (range ((e : V →ₗ[K] V) - LinearMap.id (R := K))) ≤ 1 := by
  simp only [dilatransvections]
  constructor
  · simp only [Set.mem_ofPred_eq]
    rintro ⟨f, v, he⟩
    apply le_trans (rank_mono (t := K ∙ v) ?_)
    · apply le_trans (rank_span_le _) (by simp)
    rintro _ ⟨x, rfl⟩
    simp [mem_span_singleton, he, LinearMap.transvection.apply]
  · intro he
    simp only [Set.mem_ofPred_eq]
    set u := (e : V →ₗ[K] V) - LinearMap.id with hu
    rw [eq_sub_iff_add_eq] at hu
    by_cases hr : Module.rank K (range u) = 0
    · use 0, 0
      ext x
      suffices u x = 0 by simp [← hu, this]
      rw [rank_zero_iff] at hr
      simpa [← Subtype.coe_inj] using Subsingleton.allEq (⟨u x , mem_range_self u x⟩ : range u) 0
    rw [← ne_eq, ← Cardinal.one_le_iff_ne_zero] at hr
    replace he : Module.rank K (range u) = 1 := le_antisymm he hr
    rw [rank_eq_one_iff_finrank_eq_one, finrank_eq_one_iff Unit] at he
    obtain ⟨b⟩ := he
    use (b.coord default) ∘ₗ u.rangeRestrict, b default
    ext x
    rw [← hu, LinearMap.transvection.apply, add_comm]
    suffices u x = b.repr (u.rangeRestrict x) default • b default by
      simp [this]
    suffices u.rangeRestrict x = u x by
      rw [← this, ← Submodule.coe_smul, Subtype.coe_inj]
      nth_rewrite 1 [← b.linearCombination_repr (u.rangeRestrict x)]
      rw [Finsupp.linearCombination_apply, Finsupp.sum_eq_single default] <;> simp
    exact codRestrict_apply (range u) u x

open Cardinal in
/-- Over a division ring, `dilatransvections` correspond to linear
equivalences `e` such that the linear map `e - id` has rank at most 1.

See also `LinearEquiv.mem_dilatransvections_iff_rank`. -/
/-
**LinearEquiv.mem_dilatransvections_iff_finrank** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rEquiv`。
形式化陈述：∀ {V : Type u_2} [inst : AddCommGroup V] {K : Type u_3} [inst_1 : Division
Ring K] [inst_2 : _root_.Module K V]   [Module.Finite K V] {e : V ≃ₗ[K] V},   e 
∈ LinearEquiv.dilatransvections K V ↔ Module.finrank K ↥(↑e - LinearMap.id).rang
e ≤ 1
参数：↑e - LinearMap.id。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.mem_dilatransvections_iff_rank`：∀ {V : Type u_2} [inst : Add
CommGroup V] {K : Type u_3} [inst_1 : DivisionRing K] [inst_2 : _root_.Module K 
V]   {e : V ≃ₗ[K] V}, e ∈ Linear…
· 使用定理 `Module.finrank.eq_1`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.finrank R M =
 Cardinal…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.one_toNat`：one_toNat : toNat 1 = 1
· 使用定理 `Cardinal.toNat_le_iff_le_of_lt_aleph0`：toNat_le_iff_le_of_lt_aleph0 (hc 
: c < ℵ₀) (hd : d < ℵ₀) : toNat c <= toNat d ↔ c <= d
· 使用定理 `Module.rank_lt_aleph0`：rank_lt_aleph0 [Module.Finite R M] : Module.rank 
R M < ℵ₀
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `Cardinal.one_lt_aleph0`：one_lt_aleph0 : 1 < ℵ₀
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Over a division ring, `dilatransvections` correspond to linear
equivalences `e` such that the linear map `e - id` has rank at most 1.

See also `LinearEquiv.mem_dilatransvections_iff_rank`.
-/
theorem mem_dilatransvections_iff_finrank [Module.Finite K V] {e : V ≃ₗ[K] V} :
    e ∈ dilatransvections K V ↔
      finrank K (range ((e : V →ₗ[K] V) - LinearMap.id (R := K))) ≤ 1 := by
  rw [mem_dilatransvections_iff_rank, finrank, ← one_toNat,
    toNat_le_iff_le_of_lt_aleph0 (rank_lt_aleph0 K _) one_lt_aleph0]
/-
**LinearEquiv.mem_dilatransvections_iff_finrank_quotient** 是 Mathlib 中的一个定理，位于命名
空间 `LinearEquiv`。
形式化陈述：∀ {V : Type u_2} [inst : AddCommGroup V] {K : Type u_3} [inst_1 : Division
Ring K] [inst_2 : _root_.Module K V]   [Module.Finite K V] {e : V ≃ₗ[K] V},   e 
∈ LinearEquiv.dilatransvections K V ↔ Module.finrank K (V ⧸ (↑e).fixedSubmodule)
 ≤ 1
参数：V ⧸ (↑e).fixedSubmodule。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.mem_dilatransvections_iff_finrank`：∀ {V : Type u_2} [inst : 
AddCommGroup V] {K : Type u_3} [inst_1 : DivisionRing K] [inst_2 : _root_.Module
 K V]   [Module.Finite K V] {e : V …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `LinearMap.fixedSubmodule_eq_ker`：fixedSubmodule_eq_ker {R : Type*} [Ring
 R] {V : Type*} [AddCommGroup V] [Module R V] (f : V ->ₗ[R] V) : f.fixedSubmodul
e = LinearMap.ker (f …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_dilatransvections_iff_finrank_quotient [Module.Finite K V] {e : V ≃ₗ[K] V} :
    e ∈ dilatransvections K V ↔ finrank K (V ⧸ e.fixedSubmodule) ≤ 1 := by
  rw [mem_dilatransvections_iff_finrank, ← (quotKerEquivRange _).finrank_eq,
    ← fixedSubmodule_eq_ker]
/-
**LinearEquiv.mem_dilatransvections_iff_rank_quotient** 是 Mathlib 中的一个定理，位于命名空间 
`LinearEquiv`。
形式化陈述：∀ {V : Type u_2} [inst : AddCommGroup V] {K : Type u_3} [inst_1 : Division
Ring K] [inst_2 : _root_.Module K V]   {e : V ≃ₗ[K] V}, e ∈ LinearEquiv.dilatran
svections K V ↔ Module.rank K (V ⧸ (↑e).fixedSubmodule) ≤ 1
参数：V ⧸ (↑e).fixedSubmodule。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.mem_dilatransvections_iff_rank`：∀ {V : Type u_2} [inst : Add
CommGroup V] {K : Type u_3} [inst_1 : DivisionRing K] [inst_2 : _root_.Module K 
V]   {e : V ≃ₗ[K] V}, e ∈ Linear…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁
· 使用定理 `LinearMap.fixedSubmodule_eq_ker`：fixedSubmodule_eq_ker {R : Type*} [Ring
 R] {V : Type*} [AddCommGroup V] [Module R V] (f : V ->ₗ[R] V) : f.fixedSubmodul
e = LinearMap.ker (f …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_dilatransvections_iff_rank_quotient {e : V ≃ₗ[K] V} :
    e ∈ dilatransvections K V ↔ Module.rank K (V ⧸ e.fixedSubmodule) ≤ 1 := by
  rw [mem_dilatransvections_iff_rank, ← (quotKerEquivRange _).rank_eq, ← fixedSubmodule_eq_ker]

variable (e f : V ≃ₗ[K] V)

/-- Characterization of transvections within dilatransvections. -/
/-
**LinearEquiv.mem_transvections_iff_mem_dilatransvections_and_fixedReduce_eq_one
** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {V : Type u_2} [inst : AddCommGroup V] {K : Type u_3} [inst_1 : Division
Ring K] [inst_2 : _root_.Module K V]   [Module.Finite K V] (e : V ≃ₗ[K] V),   e 
∈ LinearEquiv.transvections K V ↔ e ∈ LinearEquiv.dilatransvections K V ∧ e.fixe
dReduce = 1
参数：e : V ≃ₗ[K] V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.transvection_mem_dilatransvections`：∀ {R : Type u_1} {V : Ty
pe u_2} [inst : Ring R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R V]  
 {f : Module.Dual R V} {v : V} (hfv …
· 使用引理 `LinearEquiv.one_eq_refl`：one_eq_refl : (1 : M ≃ₗ[R] M) = refl R M
· 使用定理 `LinearEquiv.fixedReduce_eq_one`：fixedReduce_eq_one (e : V ≃ₗ[R] V) : e.f
ixedReduce = LinearEquiv.refl R _ ↔ forall v, e v - v in e.fixedSubmodule
· 使用定理 `LinearEquiv.ker_le_fixedSubmodule_transvection`：∀ {R : Type u_1} {V : Ty
pe u_2} [inst : Ring R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R V]  
 {f : Module.Dual R V} {v : V} (hfv …
· 使用定理 `LinearEquiv.transvection.apply`：∀ {R : Type u_1} {V : Type u_2} [inst : 
Ring R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R V]   {f : Module.Dua
l R V} {v : V} (h : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearEquiv.transvection.of_left_eq_zero`：∀ {R : Type u_1} {V : Type u_2
} [inst : Ring R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R V] (v : V)
   (hv : optParam (0 v = 0) ⋯)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `LinearEquiv.fixedSubmodule_eq_top_iff`：fixedSubmodule_eq_top_iff {f : V 
≃ₗ[R] V} : f.fixedSubmodule = ⊤ ↔ f = .refl R V
· 使用引理 `SetLike.exists_not_mem_of_ne_top`：exists_not_mem_of_ne_top [LE A] [Order
Top A] (s : A) (hs : s != ⊤) (h_top : ((⊤ : A) : Set B) = Set.univ
· 使用定理 `Submodule.exists_dual_map_eq_bot_of_notMem`：exists_dual_map_eq_bot_of_no
tMem {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {p : Submodule R M} {x
 : M} (hx : x ∉ p) (hp' : Projec…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Nat.add_left_inj`：∀ {m k n : ℕ}, m + n = k + n ↔ m = k
· 使用引理 `Submodule.finrank_quotient_add_finrank`：Submodule.finrank_quotient_add_f
inrank [Module.Finite R M] (N : Submodule R M) : finrank R (M ⧸ N) + finrank R N
 = finrank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用引理 `Module.Dual.finrank_ker_add_one_of_ne_zero`：finrank_ker_add_one_of_ne_ze
ro : finrank K (LinearMap.ker f) + 1 = finrank K V₁
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
（共 103 条，此处仅展示前 30 条）

--- 原说明 ---
Characterization of transvections within dilatransvections.
-/
theorem mem_transvections_iff_mem_dilatransvections_and_fixedReduce_eq_one
    [Module.Finite K V] (e : V ≃ₗ[K] V) :
    e ∈ transvections K V ↔ e ∈ dilatransvections K V ∧ e.fixedReduce = 1 := by
  refine ⟨fun ⟨f, v, hfv, he⟩ ↦ ?_, fun ⟨he, he'⟩ ↦ ?_⟩
  · constructor
    · rw [he]
      exact transvection_mem_dilatransvections hfv
    · rw [one_eq_refl, fixedReduce_eq_one, he]
      intro x
      apply ker_le_fixedSubmodule_transvection hfv
      rw [transvection.apply]
      simp [hfv]
  · by_cases he_one : e = 1
    · use 0, 0, by simp, by aesop
    have hefixed_ne_top : e.fixedSubmodule ≠ ⊤ := by
      rwa [ne_eq, LinearEquiv.fixedSubmodule_eq_top_iff]
    obtain ⟨w : V, hw : w ∉ e.fixedSubmodule⟩ :=
      SetLike.exists_not_mem_of_ne_top e.fixedSubmodule hefixed_ne_top rfl
    obtain ⟨f, hfw, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hw inferInstance
    rw [mem_dilatransvections_iff_finrank_quotient] at he
    have hf' : e.fixedSubmodule = LinearMap.ker f := by
      suffices finrank K (V ⧸ LinearMap.ker f) = 1 by
        apply Submodule.eq_of_le_of_finrank_le
        · intro x
          rw [mem_ker, ← Submodule.mem_bot K, ← hf]
          exact mem_map_of_mem
        rw [← Nat.add_le_add_iff_right, finrank_quotient_add_finrank] at he
        have := (LinearMap.ker f).finrank_quotient_add_finrank
        linarith
      rw [← Nat.add_left_inj, Submodule.finrank_quotient_add_finrank]
      rw [← f.finrank_ker_add_one_of_ne_zero, add_comm]
      aesop
    have eq_top : e.fixedSubmodule ⊔ Submodule.span K {w} = ⊤ := by
      rw [Submodule.sup_span_singleton_eq_top_iff hw]
      apply le_antisymm he
      apply Nat.one_le_of_lt
      rw [← Nat.ne_zero_iff_zero_lt]
      contrapose hefixed_ne_top
      apply eq_top_of_finrank_eq
      rw [← Nat.add_left_cancel_iff, finrank_quotient_add_finrank, hefixed_ne_top, zero_add]
    set v := (f w)⁻¹ • (e w - w)
    suffices hfv : f v = 0 by
      use f, v, hfv
      rw [← LinearEquiv.toLinearMap_inj,
        ← sub_eq_zero, ← LinearMap.ker_eq_top, eq_top_iff, ← eq_top]
      simp only [LinearEquiv.transvection.coe_toLinearMap,
        sup_le_iff, Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearEquiv.coe_coe]
      constructor
      · intro x hx
        suffices f x = 0 by
          simpa [this, LinearMap.transvection.apply, sub_eq_zero] using hx
        rwa [hf', LinearMap.mem_ker] at hx
      · simp_all [v, LinearMap.transvection.apply]
    suffices e w - w ∈ LinearMap.ker f by
      simp only [LinearMap.mem_ker, map_sub] at this
      simp only [v, LinearMap.map_smul, map_sub, this, smul_zero]
    rw [← hf', ← Submodule.ker_mkQ e.fixedSubmodule, LinearMap.mem_ker]
    simp [Submodule.mkQ_apply, Submodule.Quotient.mk_sub, ← fixedReduce_mk, he']

end divisionRing

end LinearEquiv.dilatransvections

section baseChange

open IsBaseChange LinearMap LinearEquiv Module

open scoped TensorProduct

section

variable
    {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
    (A : Type*) [CommSemiring A] [Algebra R A]

/-
**LinearMap.transvection.baseChange** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.transve
ction.LinearEquiv`。
形式化陈述：LinearMap.transvection.baseChange (f : Dual R V) (v : V) : (transvection f
 v).baseChange A = transvection (f.baseChange A) (1 otimesₜ[R] v)
参数：f : Dual R V；v : V。
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
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
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
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearMap.transvection.baseChange (f : Dual R V) (v : V) :
    (transvection f v).baseChange A = transvection (f.baseChange A) (1 ⊗ₜ[R] v) := by
  ext; simp [transvection, TensorProduct.tmul_add]

variable {W : Type*} [AddCommMonoid W] [Module R W] [Module A W]
  [IsScalarTower R A W] {ε : V →ₗ[R] W} (ibc : IsBaseChange A ε)
/-
**IsBaseChange.transvection** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.transvection.Li
nearEquiv`。
形式化陈述：IsBaseChange.transvection (f : Dual R V) (v : V) : ibc.endHom (transvectio
n f v) = transvection (ibc.toDual f) (ε v)
参数：f : Dual R V；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsBaseChange.inductionOn`：∀ {R : Type u_1} {M : Type v₁} {N : Type v₂} {
S : Type v₃} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : Com
mSemiring R] […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsBaseChange.endHom_comp_apply`：endHom_comp_apply {α : M ->ₗ[R] P} (j : 
IsBaseChange S α) (f : M ->ₗ[R] M) (m : M) : endHom j f (α m) = α (f m)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsBaseChange.toDual_comp_apply`：toDual_comp_apply (f : Dual R V) (v : V)
 : ibc.toDual f (j v) = algebraMap R A (f v)
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
-/
theorem IsBaseChange.transvection (f : Dual R V) (v : V) :
    ibc.endHom (transvection f v) = transvection (ibc.toDual f) (ε v) := by
  ext w
  induction w using ibc.inductionOn with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | smul a w hw => simp [hw]
  | tmul x => simp [LinearMap.transvection.apply, endHom_comp_apply, toDual_comp_apply]

end

section

variable {R V A : Type*} [CommRing R] [AddCommGroup V]
    [Module R V] [CommRing A] [Algebra R A]
    {f : Module.Dual R V} {v : V} (h : f v = 0)
    {W : Type*} [AddCommMonoid W] [Module R W] [Module A W]
  [IsScalarTower R A W] {ε : V →ₗ[R] W} (ibc : IsBaseChange A ε)

/-
**LinearEquiv.transvection.baseChange** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.trans
vection.LinearEquiv`。
形式化陈述：LinearEquiv.transvection.baseChange (hA : f.baseChange A (1 otimesₜ[R] v) 
= 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.transvection.baseChange`：LinearMap.transvection.baseChange (f 
: Dual R V) (v : V) : (transvection f v).baseChange A = transvection (f.baseChan
ge A) (1 otimesₜ[R] v)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearEquiv.transvection.baseChange
    (hA : f.baseChange A (1 ⊗ₜ[R] v) = 0 := by simp [Algebra.algebraMap_eq_smul_one]) :
    (LinearEquiv.transvection h).baseChange R A V V = LinearEquiv.transvection hA := by
  simp [← toLinearMap_inj, coe_baseChange,
    LinearEquiv.transvection.coe_toLinearMap, LinearMap.transvection.baseChange]
/-
**LinearEquiv.dilatransvection.baseChange** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.t
ransvection.LinearEquiv`。
形式化陈述：LinearEquiv.dilatransvection.baseChange (e : V ≃ₗ[R] V) (he : e in LinearE
quiv.dilatransvections R V) : e.baseChange R A V V in LinearEquiv.dilatransvecti
ons A (A otimes[R] V)
参数：e : V ≃ₗ[R] V；he : e in LinearEquiv.dilatransvections R V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.transvection.baseChange`：LinearMap.transvection.baseChange (f 
: Dual R V) (v : V) : (transvection f v).baseChange A = transvection (f.baseChan
ge A) (1 otimesₜ[R] v)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearEquiv.dilatransvection.baseChange (e : V ≃ₗ[R] V)
    (he : e ∈ LinearEquiv.dilatransvections R V) :
    e.baseChange R A V V ∈ LinearEquiv.dilatransvections A (A ⊗[R] V) := by
  obtain ⟨f, v, he⟩ := he
  use (f.baseChange A), (1 ⊗ₜ[R] v)
  simp [he, LinearMap.transvection.baseChange]

end

end baseChange

section determinant

namespace LinearMap.transvection

open Polynomial Module

open scoped TensorProduct

section Field

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Determinant of transvections, over a field.

See `LinearMap.Transvection.det` for the general result. -/
/-
**LinearMap.transvection.det_ofField** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.transv
ection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Determinant of transvections, over a field.

See `LinearMap.Transvection.det` for the general result.
-/
private theorem det_ofField [FiniteDimensional K V] (f : Dual K V) (v : V) :
    (LinearMap.transvection f v).det = 1 + f v := by
  classical
  by_cases hfv : f v = 0
  · by_cases hv : v = 0
    · simp [hv]
    by_cases hf : f = 0
    · simp [hf]
    obtain ⟨ι, b, i, j, hi, hj⟩ := exists_basis_of_pairing_eq_zero hfv hf hv
    have : Fintype ι := FiniteDimensional.fintypeBasisIndex b
    rw [← det_toMatrix b]
    suffices toMatrix b b (LinearMap.transvection f v) = Matrix.transvection i j 1 by
      rw [this, Matrix.det_transvection_of_ne i j hi 1, hfv, add_zero]
    ext x y
    rw [toMatrix_apply, transvection.apply, Matrix.transvection]
    simp only [hj.2, Basis.coord_apply, Basis.repr_self, hj.1, map_add, map_smul,
      Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.coe_add, Pi.add_apply, Matrix.add_apply]
    apply congr_arg₂
    · by_cases h : x = y
      · rw [h]; simp
      · rw [Finsupp.single_eq_of_ne h, Matrix.one_apply_ne h]
    · by_cases h : i = x ∧ j = y
      · rw [h.1, h.2]; simp
      · rcases not_and_or.mp h with h' | h' <;>
          simp [Finsupp.single_eq_of_ne' h',
            Finsupp.single_eq_of_ne h',
            Matrix.single_apply_of_ne (h := h)]
  · obtain ⟨ι, b, i, hv, hf⟩ := exists_basis_of_pairing_ne_zero hfv
    have : Fintype ι := FiniteDimensional.fintypeBasisIndex b
    rw [← det_toMatrix b]
    suffices toMatrix b b (transvection f v) =
      Matrix.diagonal (Function.update 1 i (1 + f v)) by
      rw [this]
      simp only [Matrix.det_diagonal]
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hj
        simp [Function.update_of_ne hj]
      · simp
    ext x y
    rw [toMatrix_apply, transvection.apply, Matrix.diagonal]
    simp only [map_add, Basis.repr_self, map_smul, Finsupp.coe_add, Finsupp.coe_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply]
    rw [hv, Function.update_apply, Basis.repr_self, Pi.one_apply, hf]
    simp only [smul_apply, Basis.coord_apply, Basis.repr_self, smul_eq_mul,
      Finsupp.single_eq_same, mul_one]
    split_ifs with hxy hxi
    · simp [← hxy, hxi]
    · rw [Finsupp.single_eq_of_ne hxi]; simp [hxy]
    · rw [Finsupp.single_eq_of_ne hxy, zero_add, mul_assoc]
      convert! mul_zero _
      by_cases hxi : x = i
      · simp [← hxi, Finsupp.single_eq_of_ne hxy]
      · simp [Finsupp.single_eq_of_ne hxi]

end Field

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Determinant of a transvection, over a domain.

See `LinearMap.transvection.det` for the general case. -/
/-
**LinearMap.transvection.det_ofDomain** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.trans
vection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Determinant of a transvection, over a domain.

See `LinearMap.transvection.det` for the general case.
-/
private theorem det_ofDomain [Free R V] [Module.Finite R V] [IsDomain R] (f : Dual R V) (v : V) :
    (transvection f v).det = 1 + f v := by
  let K := FractionRing R
  let : Field K := inferInstance
  apply FaithfulSMul.algebraMap_injective R K
  have := det_ofField (f.baseChange K) (1 ⊗ₜ[R] v)
  rw [← transvection.baseChange, det_baseChange,
    ← algebraMap.coe_one (R := R) (A := K)] at this
  simpa [Algebra.algebraMap_eq_smul_one, add_smul] using this

open IsBaseChange
/-
**LinearMap.transvection.det** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.transvection`。
形式化陈述：∀ {R : Type u_3} {V : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup
 V] [inst_2 : _root_.Module R V]   [Module.Free R V] [Module.Finite R V] (f : Mo
dule.Dual R V) (v : V),   LinearMap.det (LinearMap.transvection f v) = 1 + f v
参数：f : Module.Dual R V；v : V；LinearMap.transvection f v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} {σ : Type u_1} [i
nst : CommSemiring R] [IsCancelAdd R] [IsDomain R], IsDomain (MvPolynomial σ R)
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsScalarTower.of_compHom`：of_compHom : letI
· 使用定理 `IsBaseChange.of_fintype_basis`：of_fintype_basis [Fintype ι] : IsBaseChan
ge R (Fintype.linearCombination A b)
· 使用定理 `Fintype.linearCombination_apply_single`：Fintype.linearCombination_apply_
single [DecidableEq α] (i : α) (r : R) : Fintype.linearCombination R v (Pi.singl
e i r) = r • v i
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsBaseChange.toDual_comp_apply`：toDual_comp_apply (f : Dual R V) (v : V)
 : ibc.toDual f (j v) = algebraMap R A (f v)
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsBaseChange.of_fintype_basis_eq`：of_fintype_basis_eq [Fintype ι] {a : ι
 -> A} {v : V} : (Fintype.linearCombination A b) a = v ↔ algebraMap A R ∘ a = b.
equivFun v
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsBaseChange.transvection`：IsBaseChange.transvection (f : Dual R V) (v :
 V) : ibc.endHom (transvection f v) = transvection (ibc.toDual f) (ε v)
· 使用定理 `IsBaseChange.det_endHom`：det_endHom {α : M ->ₗ[R] P} (j : IsBaseChange S
 α) (f : M ->ₗ[R] M) : LinearMap.det (endHom j f) = algebraMap R S (LinearMap.de
t f)
· 使用定理 `Module.Free.function`：∀ (ι : Type u_1) (R : Type u_2) (M : Type u_3) [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Fini
te ι] [Mod…
· 使用定理 `_private.Mathlib.LinearAlgebra.Transvection.Basic.0.LinearMap.transvecti
on.det_ofDomain`：∀ {R : Type u_3} {V : Type u_4} [inst : CommRing R] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module R V]   [Module.Free R V] [Module.Finit…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
（共 37 条，此处仅展示前 30 条）
-/
@[simp] theorem det [Free R V] [Module.Finite R V] (f : Dual R V) (v : V) :
    (transvection f v).det = 1 + f v := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · subsingleton
  let b := finBasis R V
  set n := finrank R V
  let S := MvPolynomial (Fin n ⊕ Fin n) ℤ
  let γ : S →+* R :=
    (MvPolynomial.aeval (Sum.elim (fun i ↦ f (b i)) (fun i ↦ b.coord i v)) :
      MvPolynomial (Fin n ⊕ Fin n) ℤ →ₐ[ℤ] R)
  have : IsDomain S := inferInstance
  let _ : Algebra S R := RingHom.toAlgebra γ
  let _ : Module S V := compHom V γ
  have _ : IsScalarTower S R V := IsScalarTower.of_compHom S R V
  have ibc := IsBaseChange.of_fintype_basis S b
  set ε := Fintype.linearCombination S (fun i ↦ b i)
  set M := Fin n → S
  have hε (i) : ε (Pi.single i 1) = b i := by
    rw [Fintype.linearCombination_apply_single, one_smul]
  let fM : Dual S M :=
    Fintype.linearCombination S fun i ↦ MvPolynomial.X (Sum.inl i)
  let vM : M := fun i ↦ MvPolynomial.X (Sum.inr i)
  have hf : ibc.toDual fM = f := by
    apply b.ext
    intro i
    rw [← hε, toDual_comp_apply, Fintype.linearCombination_apply_single,
      one_smul, RingHom.algebraMap_toAlgebra, hε]
    apply MvPolynomial.aeval_X
  have hv : ε vM = v := by
    rw [of_fintype_basis_eq]
    ext i
    rw [RingHom.algebraMap_toAlgebra]
    simp only [vM, γ, Function.comp_apply]
    apply MvPolynomial.aeval_X
  rw [← hf, ← hv, ← IsBaseChange.transvection, det_endHom, det_ofDomain]
  rw [map_add, map_one, add_right_inj, toDual_comp_apply]

/-- Determinant of a transvection.

It is not necessary to assume that the module is finite and free
because `LinearMap.det` is identically 1 otherwise. -/
/-
**LinearMap.transvection._root_.LinearEquiv.transvection.det_eq_one** 是 Mathlib 
中的一个定理，位于命名空间 `LinearMap.transvection`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Determinant of a transvection.

It is not necessary to assume that the module is finite and free
because `LinearMap.det` is identically 1 otherwise.
-/
@[simp] theorem _root_.LinearEquiv.transvection.det_eq_one
    {f : Dual R V} {v : V} (hfv : f v = 0) :
    (LinearEquiv.transvection hfv).det = 1 := by
  rw [← Units.val_inj, LinearEquiv.coe_det,
    LinearEquiv.transvection.coe_toLinearMap hfv, Units.val_one]
  by_contra! h
  have : Free R V := Free.of_det_ne_one h
  have : Module.Finite R V := finite_of_det_ne_one h
  apply h
  rw [transvection.det, hfv, add_zero]

end transvection

end LinearMap

end determinant

end

