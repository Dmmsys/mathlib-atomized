/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Tactic.ApplyFun

/-!
# Sums as a linear map

Given an `R`-module `M`, the `R`-module structure on `α →₀ M` is defined in
`Data.Finsupp.Basic`.

## Main definitions

* `Finsupp.lsum`: `Finsupp.sum` or `Finsupp.liftAddHom` as a `LinearMap`;

## Tags

function with finite support, module, linear algebra
-/

@[expose] public section

noncomputable section

open Set LinearMap Submodule

namespace Finsupp

section SMul

variable {α : Type*} {β : Type*} {R R₂ : Type*} {M M₂ : Type*}

/-
**Finsupp.smul_sum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：smul_sum [Zero β] [AddCommMonoid M] [DistribSMul R M] {v : α ->₀ β} {c : R
} {h : α -> β -> M} : c • v.sum h = v.sum fun a b => c • h a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
-/
theorem smul_sum [Zero β] [AddCommMonoid M] [DistribSMul R M] {v : α →₀ β} {c : R} {h : α → β → M} :
    c • v.sum h = v.sum fun a b => c • h a b :=
  Finset.smul_sum

@[simp]
/-
**Finsupp.sum_smul_index_semilinearMap'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_smul_index_semilinearMap' [Semiring R] [Semiring R₂] [AddCommMonoid M]
 [Module R M] [AddCommMonoid M₂] [Module R₂ M₂] {σ : R ->+* R₂} {v : α ->₀ M} {c
 : R} {h : α -> M ->ₛₗ[σ] M₂} : ((c • v).sum fun a => h a) = σ c • v.sum fun a =
> h a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_smul_index'`：sum_smul_index' [Zero M] [SMulZeroClass R M] [A
ddCommMonoid N] {g : α ->₀ M} {b : R} {h : α -> M -> N} (h0 : forall i, h i 0 = 
0) : (b • g).…
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `Finsupp.smul_sum`：smul_sum [Zero β] [AddCommMonoid M] [DistribSMul R M] 
{v : α ->₀ β} {c : R} {h : α -> β -> M} : c • v.sum h = v.sum fun a b => c • h a
 b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_smul_index_semilinearMap' [Semiring R] [Semiring R₂] [AddCommMonoid M] [Module R M]
    [AddCommMonoid M₂] [Module R₂ M₂] {σ : R →+* R₂} {v : α →₀ M} {c : R} {h : α → M →ₛₗ[σ] M₂} :
    ((c • v).sum fun a => h a) = σ c • v.sum fun a => h a := by
  rw [Finsupp.sum_smul_index', Finsupp.smul_sum]
  · simp only [map_smulₛₗ]
  · intro i
    exact (h i).map_zero
/-
**Finsupp.sum_smul_index_linearMap'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_smul_index_linearMap' [Semiring R] [AddCommMonoid M] [Module R M] [Add
CommMonoid M₂] [Module R M₂] {v : α ->₀ M} {c : R} {h : α -> M ->ₗ[R] M₂} : ((c 
• v).sum fun a => h a) = c • v.sum fun a => h a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_smul_index_semilinearMap'`：sum_smul_index_semilinearMap' [Se
miring R] [Semiring R₂] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Modul
e R₂ M₂] {σ : R ->+* R₂} {v…
-/
theorem sum_smul_index_linearMap' [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂]
    [Module R M₂] {v : α →₀ M} {c : R} {h : α → M →ₗ[R] M₂} :
    ((c • v).sum fun a => h a) = c • v.sum fun a => h a :=
  sum_smul_index_semilinearMap'

end SMul

variable {α : Type*} {M N P : Type*} {R R₂ R₃ : Type*} {S : Type*}
variable [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring S]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R₂ N]
variable [AddCommMonoid P] [Module R₃ P]

variable {σ : R →+* R₂} {σ_inv : R₂ →+* R}

section CompatibleSMul

variable (R S M N ι : Type*)
variable [Semiring S] [AddCommMonoid M] [AddCommMonoid N] [Module S M] [Module S N]

/-
**Finsupp._root_.LinearMap.CompatibleSMul.finsupp_dom** 是 Mathlib 中的一个实例，位于命名空间 
`Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.LinearMap.CompatibleSMul.finsupp_dom [SMulZeroClass R M] [DistribSMul R N]
    [LinearMap.CompatibleSMul M N R S] : LinearMap.CompatibleSMul (ι →₀ M) N R S where
  map_smul f r m := by
    conv_rhs => rw [← sum_single m, map_finsuppSum, smul_sum]
    erw [← sum_single (r • m), sum_mapRange_index single_zero, map_finsuppSum]
    congr; ext i m; exact (f.comp <| lsingle i).map_smul_of_tower r m
/-
**Finsupp._root_.LinearMap.CompatibleSMul.finsupp_cod** 是 Mathlib 中的一个实例，位于命名空间 
`Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.LinearMap.CompatibleSMul.finsupp_cod [SMul R M] [SMulZeroClass R N]
    [LinearMap.CompatibleSMul M N R S] : LinearMap.CompatibleSMul M (ι →₀ N) R S where
  map_smul f r m := by ext i; apply ((lapply i).comp f).map_smul_of_tower

end CompatibleSMul

section LSum

variable (S)
variable [Module S N] [SMulCommClass R₂ S N]

set_option backward.isDefEq.respectTransparency false in
/-- Lift a family of linear maps `M →ₗ[R] N` indexed by `x : α` to a linear map from `α →₀ M` to
`N` using `Finsupp.sum`. This is an upgraded version of `Finsupp.liftAddHom`.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used.
-/
/-
**Finsupp.lsum** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：lsum : (α -> M ->ₛₗ[σ] N) ≃ₗ[S] (α ->₀ M) ->ₛₗ[σ] N where toFun F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a family of linear maps `M →ₗ[R] N` indexed by `x : α` to a linear map from
 `α →₀ M` to
`N` using `Finsupp.sum`. This is an upgraded version of `Finsupp.liftAddHom`.

See note [bundled maps over different rings] for why separate `R` and `S` semiri
ngs are used.
-/
def lsum : (α → M →ₛₗ[σ] N) ≃ₗ[S] (α →₀ M) →ₛₗ[σ] N where
  toFun F :=
    { toFun := fun d => d.sum fun i => F i
      map_add' := (liftAddHom (α := α) (M := M) (N := N) fun x => (F x).toAddMonoidHom).map_add
      map_smul' := fun c f => by simp [sum_smul_index', smul_sum] }
  invFun F x := F.comp (lsingle x)
  left_inv F := by
    ext x y
    simp
  right_inv F := by
    ext x y
    simp
  map_add' F G := by
    ext x y
    simp
  map_smul' F G := by
    ext x y
    simp

@[simp]
/-
**Finsupp.coe_lsum** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：coe_lsum (f : α -> M ->ₛₗ[σ] N) : (lsum S f : (α ->₀ M) -> N) = fun d => d
.sum fun i => f i
参数：f : α -> M ->ₛₗ[σ] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_lsum (f : α → M →ₛₗ[σ] N) : (lsum S f : (α →₀ M) → N) = fun d => d.sum fun i => f i :=
  rfl
/-
**Finsupp.lsum_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lsum_apply (f : α -> M ->ₛₗ[σ] N) (l : α ->₀ M) : Finsupp.lsum S f l = l.s
um fun b => f b
参数：f : α -> M ->ₛₗ[σ] N；l : α ->₀ M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lsum_apply (f : α → M →ₛₗ[σ] N) (l : α →₀ M) : Finsupp.lsum S f l = l.sum fun b => f b :=
  rfl
/-
**Finsupp.lsum_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lsum_single (f : α -> M ->ₛₗ[σ] N) (i : α) (m : M) : Finsupp.lsum S f (Fin
supp.single i m) = f i m
参数：f : α -> M ->ₛₗ[σ] N；i : α；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
-/
theorem lsum_single (f : α → M →ₛₗ[σ] N) (i : α) (m : M) :
    Finsupp.lsum S f (Finsupp.single i m) = f i m :=
  Finsupp.sum_single_index (f i).map_zero
/-
**Finsupp.lsum_comp_lsingle** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} {N : Type u_3} {R : Type u_5} {R₂ : Type u
_6} (S : Type u_8) [inst : Semiring R]   [inst_1 : Semiring R₂] [inst_2 : Semiri
ng S] [inst_3 : AddCommMonoid M] [inst_4 : _root_.Module R M]   [inst_5 : AddCom
mMonoid N] [inst_6 : _root_.Module R₂ N] {σ : R →+* R₂} [inst_7 : _root_.Module 
S N]   [inst_8 : SMulCommClass R₂ S N] (f : α → M →ₛₗ[σ] N) (i : α), (Finsupp.ls
um S) f ∘ₛₗ Finsupp.lsingle i = f i
参数：S : Type u_8；f : α → M →ₛₗ[σ] N；i : α；Finsupp.lsum S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
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
-/
@[simp] theorem lsum_comp_lsingle (f : α → M →ₛₗ[σ] N) (i : α) :
    Finsupp.lsum S f ∘ₛₗ lsingle i = f i := by ext; simp
/-
**Finsupp.lsum_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lsum_symm_apply (f : (α ->₀ M) ->ₛₗ[σ] N) (x : α) : (lsum S).symm f x = f.
comp (lsingle x)
参数：f : (α ->₀ M) ->ₛₗ[σ] N；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lsum_symm_apply (f : (α →₀ M) →ₛₗ[σ] N) (x : α) : (lsum S).symm f x = f.comp (lsingle x) :=
  rfl

end LSum

section

variable (M) (R) (X : Type*) (S)
variable [Module S M] [SMulCommClass R S M]

/-- A slight rearrangement from `lsum` gives us
the bijection underlying the free-forgetful adjunction for R-modules.
-/
/-
**Finsupp.lift** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：lift : (X -> M) ≃+ ((X ->₀ R) ->ₗ[R] M)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
A slight rearrangement from `lsum` gives us
the bijection underlying the free-forgetful adjunction for R-modules.
-/
noncomputable def lift : (X → M) ≃+ ((X →₀ R) →ₗ[R] M) :=
  (AddEquiv.arrowCongr (Equiv.refl X) (ringLmapEquivSelf R ℕ M).toAddEquiv.symm).trans
    (lsum _ : _ ≃ₗ[ℕ] _).toAddEquiv

@[simp]
/-
**Finsupp.lift_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lift_symm_apply (f) (x) : ((lift M R X).symm f) x = f (single x 1)
参数：f；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_symm_apply (f) (x) : ((lift M R X).symm f) x = f (single x 1) :=
  rfl

@[simp]
/-
**Finsupp.lift_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lift_apply (f) (g) : ((lift M R X) f) g = g.sum fun x r => r • f x
参数：f；g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_apply (f) (g) : ((lift M R X) f) g = g.sum fun x r => r • f x :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- Given compatible `S` and `R`-module structures on `M` and a type `X`, the set of functions
`X → M` is `S`-linearly equivalent to the `R`-linear maps from the free `R`-module
on `X` to `M`. -/
/-
**Finsupp.llift** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：llift : (X -> M) ≃ₗ[S] (X ->₀ R) ->ₗ[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given compatible `S` and `R`-module structures on `M` and a type `X`, the set of
 functions
`X → M` is `S`-linearly equivalent to the `R`-linear maps from the free `R`-modu
le
on `X` to `M`.
-/
noncomputable def llift : (X → M) ≃ₗ[S] (X →₀ R) →ₗ[R] M :=
  { lift M R X with
    map_smul' := by
      intros
      dsimp
      ext
      simp only [coe_comp, Function.comp_apply, lsingle_apply, lift_apply, Pi.smul_apply,
        sum_single_index, zero_smul, one_smul, LinearMap.smul_apply] }

@[simp]
/-
**Finsupp.llift_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：llift_apply (f : X -> M) (x : X ->₀ R) : llift M R S X f x = lift M R X f 
x
参数：f : X -> M；x : X ->₀ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem llift_apply (f : X → M) (x : X →₀ R) : llift M R S X f x = lift M R X f x :=
  rfl

@[simp]
/-
**Finsupp.llift_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：llift_symm_apply (f : (X ->₀ R) ->ₗ[R] M) (x : X) : (llift M R S X).symm f
 x = f (single x 1)
参数：f : (X ->₀ R) ->ₗ[R] M；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem llift_symm_apply (f : (X →₀ R) →ₗ[R] M) (x : X) :
    (llift M R S X).symm f x = f (single x 1) :=
  rfl

end

/-- An equivalence of domains induces a linear equivalence of finitely supported functions.

This is `Finsupp.domCongr` as a `LinearEquiv`.
See also `LinearMap.funCongrLeft` for the case of arbitrary functions. -/
/-
**Finsupp.domLCongr** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：{M : Type u_2} →   {R : Type u_5} →     [inst : Semiring R] →       [inst_
1 : AddCommMonoid M] →         [inst_2 : _root_.Module R M] → {α₁ : Type u_9} → 
{α₂ : Type u_10} → α₁ ≃ α₂ → (α₁ →₀ M) ≃ₗ[R] α₂ →₀ M
参数：α₁ →₀ M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of domains induces a linear equivalence of finitely supported fun
ctions.

This is `Finsupp.domCongr` as a `LinearEquiv`.
See also `LinearMap.funCongrLeft` for the case of arbitrary functions.
-/
protected def domLCongr {α₁ α₂ : Type*} (e : α₁ ≃ α₂) : (α₁ →₀ M) ≃ₗ[R] α₂ →₀ M :=
  (Finsupp.domCongr e : (α₁ →₀ M) ≃+ (α₂ →₀ M)).toLinearEquiv <| by
    simpa only [equivMapDomain_eq_mapDomain, domCongr_apply] using! (lmapDomain M R e).map_smul

@[simp]
/-
**Finsupp.domLCongr_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：domLCongr_apply {α₁ : Type*} {α₂ : Type*} (e : α₁ ≃ α₂) (v : α₁ ->₀ M) : (
Finsupp.domLCongr e : _ ≃ₗ[R] _) v = Finsupp.domCongr e v
参数：e : α₁ ≃ α₂；v : α₁ ->₀ M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domLCongr_apply {α₁ : Type*} {α₂ : Type*} (e : α₁ ≃ α₂) (v : α₁ →₀ M) :
    (Finsupp.domLCongr e : _ ≃ₗ[R] _) v = Finsupp.domCongr e v :=
  rfl

@[simp]
/-
**Finsupp.domLCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：domLCongr_refl : Finsupp.domLCongr (Equiv.refl α) = LinearEquiv.refl R (α 
->₀ M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Finsupp.equivMapDomain_refl`：equivMapDomain_refl (l : α ->₀ M) : equivMa
pDomain (Equiv.refl _) l = l
-/
theorem domLCongr_refl : Finsupp.domLCongr (Equiv.refl α) = LinearEquiv.refl R (α →₀ M) :=
  LinearEquiv.ext fun _ => equivMapDomain_refl _
/-
**Finsupp.domLCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：domLCongr_trans {α₁ α₂ α₃ : Type*} (f : α₁ ≃ α₂) (f₂ : α₂ ≃ α₃) : (Finsupp
.domLCongr f).trans (Finsupp.domLCongr f₂) = (Finsupp.domLCongr (f.trans f₂) : (
_ ->₀ M) ≃ₗ[R] _)
参数：f : α₁ ≃ α₂；f₂ : α₂ ≃ α₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.equivMapDomain_trans`：equivMapDomain_trans (f : α ≃ β) (g : β ≃ 
γ) (l : α ->₀ M) : equivMapDomain (f.trans g) l = equivMapDomain g (equivMapDoma
in f l)
-/
theorem domLCongr_trans {α₁ α₂ α₃ : Type*} (f : α₁ ≃ α₂) (f₂ : α₂ ≃ α₃) :
    (Finsupp.domLCongr f).trans (Finsupp.domLCongr f₂) =
      (Finsupp.domLCongr (f.trans f₂) : (_ →₀ M) ≃ₗ[R] _) :=
  LinearEquiv.ext fun _ => (equivMapDomain_trans _ _ _).symm

@[simp]
/-
**Finsupp.domLCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：domLCongr_symm {α₁ α₂ : Type*} (f : α₁ ≃ α₂) : ((Finsupp.domLCongr f).symm
 : (_ ->₀ M) ≃ₗ[R] _) = Finsupp.domLCongr f.symm
参数：f : α₁ ≃ α₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem domLCongr_symm {α₁ α₂ : Type*} (f : α₁ ≃ α₂) :
    ((Finsupp.domLCongr f).symm : (_ →₀ M) ≃ₗ[R] _) = Finsupp.domLCongr f.symm :=
  LinearEquiv.ext fun _ => rfl
/-
**Finsupp.domLCongr_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：domLCongr_single {α₁ : Type*} {α₂ : Type*} (e : α₁ ≃ α₂) (i : α₁) (m : M) 
: (Finsupp.domLCongr e : _ ≃ₗ[R] _) (Finsupp.single i m) = Finsupp.single (e i) 
m
参数：e : α₁ ≃ α₂；i : α₁；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.domCongr_apply`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [
inst : AddCommMonoid M] (e : α ≃ β) (l : α →₀ M),   (Finsupp.domCongr e) l = Fin
supp.equivMa…
· 使用定理 `Finsupp.equivMapDomain_single`：equivMapDomain_single (f : α ≃ β) (a : α)
 (b : M) : equivMapDomain f (single a b) = single (f a) b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem domLCongr_single {α₁ : Type*} {α₂ : Type*} (e : α₁ ≃ α₂) (i : α₁) (m : M) :
    (Finsupp.domLCongr e : _ ≃ₗ[R] _) (Finsupp.single i m) = Finsupp.single (e i) m := by
  simp

section Equiv

variable [RingHomInvPair σ σ_inv] [RingHomInvPair σ_inv σ]

/-- An equivalence of domain and a linear equivalence of codomain induce a linear equivalence of the
corresponding finitely supported functions. -/
/-
**Finsupp.lcongr** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：lcongr {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) : (ι ->₀ M) ≃ₛₗ[σ] κ 
->₀ N
参数：e₁ : ι ≃ κ；e₂ : M ≃ₛₗ[σ] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of domain and a linear equivalence of codomain induce a linear eq
uivalence of the
corresponding finitely supported functions.
-/
def lcongr {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) : (ι →₀ M) ≃ₛₗ[σ] κ →₀ N :=
  (Finsupp.domLCongr e₁).trans (mapRange.linearEquiv e₂)

@[simp]
/-
**Finsupp.lcongr_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lcongr_single {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) (i : ι) (m : M
) : lcongr e₁ e₂ (Finsupp.single i m) = Finsupp.single (e₁ i) (e₂ m)
参数：e₁ : ι ≃ κ；e₂ : M ≃ₛₗ[σ] N；i : ι；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.map_zero`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂
 : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst_…
· 使用定理 `Finsupp.domCongr_apply`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [
inst : AddCommMonoid M] (e : α ≃ β) (l : α →₀ M),   (Finsupp.domCongr e) l = Fin
supp.equivMa…
· 使用定理 `Finsupp.equivMapDomain_single`：equivMapDomain_single (f : α ≃ β) (a : α)
 (b : M) : equivMapDomain f (single a b) = single (f a) b
· 使用定理 `Finsupp.mapRange.linearEquiv_apply`：∀ {α : Type u_1} {M : Type u_2} {N :
 Type u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring
 R₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lcongr_single {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) (i : ι) (m : M) :
    lcongr e₁ e₂ (Finsupp.single i m) = Finsupp.single (e₁ i) (e₂ m) := by simp [lcongr]

@[simp]
/-
**Finsupp.lcongr_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lcongr_apply_apply {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) (f : ι ->
₀ M) (k : κ) : lcongr e₁ e₂ f k = e₂ (f (e₁.symm k))
参数：e₁ : ι ≃ κ；e₂ : M ≃ₛₗ[σ] N；f : ι ->₀ M；k : κ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lcongr_apply_apply {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) (f : ι →₀ M) (k : κ) :
    lcongr e₁ e₂ f k = e₂ (f (e₁.symm k)) :=
  rfl
/-
**Finsupp.lcongr_symm_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lcongr_symm_single {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) (k : κ) (
n : N) : (lcongr e₁ e₂).symm (Finsupp.single k n) = Finsupp.single (e₁.symm k) (
e₂.symm n)
参数：e₁ : ι ≃ κ；e₂ : M ≃ₛₗ[σ] N；k : κ；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `Finsupp.lcongr_single`：lcongr_single {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M
 ≃ₛₗ[σ] N) (i : ι) (m : M) : lcongr e₁ e₂ (Finsupp.single i m) = Finsupp.single 
(e₁ i) (e₂ …
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lcongr_symm_single {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) (k : κ) (n : N) :
    (lcongr e₁ e₂).symm (Finsupp.single k n) = Finsupp.single (e₁.symm k) (e₂.symm n) := by
  apply_fun (lcongr e₁ e₂ : (ι →₀ M) → (κ →₀ N)) using (lcongr e₁ e₂).injective
  simp

@[simp]
/-
**Finsupp.lcongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：lcongr_symm {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) : (lcongr e₁ e₂)
.symm = lcongr e₁.symm e₂.symm
参数：e₁ : ι ≃ κ；e₂ : M ≃ₛₗ[σ] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
-/
theorem lcongr_symm {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ[σ] N) :
    (lcongr e₁ e₂).symm = lcongr e₁.symm e₂.symm := by
  ext
  rfl

end Equiv

end Finsupp

variable {R : Type*} {M : Type*} {N : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

open Finsupp

section

variable (R)

/-
**Submodule.finsuppSum_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ (R : Type u_1) {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {ι : Type u_4} {β : Type u_5} [inst_3 : Zero
 β] (S : Submodule R M) (f : ι →₀ β) (g : ι → β → M),   (∀ (c : ι), f c ≠ 0 → g 
c (f c) ∈ S) → f.sum g ∈ S
参数：R : Type u_1；S : Submodule R M；f : ι →₀ β；g : ι → β → M；∀ (c : ι), f c ≠ 0 → 
g c (f c) ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.finsuppSum_mem`：∀ {α : Type u_1} {M : Type u_8} {N : T
ype u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] {S : Type u_16}   [inst_2 :
 SetLike S N] [AddSubm…
-/
protected theorem Submodule.finsuppSum_mem {ι β : Type*} [Zero β] (S : Submodule R M) (f : ι →₀ β)
    (g : ι → β → M) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) : f.sum g ∈ S :=
  AddSubmonoidClass.finsuppSum_mem S f g h

end

namespace LinearMap

variable {α : Type*}

open Finsupp Function

-- See also `LinearMap.splittingOfFunOnFintypeSurjective`
/-- A surjective linear map to finitely supported functions has a splitting. -/
/-
**LinearMap.splittingOfFinsuppSurjective** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：splittingOfFinsuppSurjective (f : M ->ₗ[R] α ->₀ R) (s : Surjective f) : (
α ->₀ R) ->ₗ[R] M
参数：f : M ->ₗ[R] α ->₀ R；s : Surjective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A surjective linear map to finitely supported functions has a splitting.
-/
def splittingOfFinsuppSurjective (f : M →ₗ[R] α →₀ R) (s : Surjective f) : (α →₀ R) →ₗ[R] M :=
  Finsupp.lift _ _ _ fun x : α => (s (Finsupp.single x 1)).choose
/-
**LinearMap.splittingOfFinsuppSurjective_splits** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rMap`。
形式化陈述：splittingOfFinsuppSurjective_splits (f : M ->ₗ[R] α ->₀ R) (s : Surjective
 f) : f.comp (splittingOfFinsuppSurjective f s) = LinearMap.id
参数：f : M ->ₗ[R] α ->₀ R；s : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem splittingOfFinsuppSurjective_splits (f : M →ₗ[R] α →₀ R) (s : Surjective f) :
    f.comp (splittingOfFinsuppSurjective f s) = LinearMap.id := by
  ext x
  dsimp [splittingOfFinsuppSurjective]
  congr
  rw [sum_single_index, one_smul]
  · exact (s (Finsupp.single x 1)).choose_spec
  · rw [zero_smul]
/-
**LinearMap.leftInverse_splittingOfFinsuppSurjective** 是 Mathlib 中的一个定理，位于命名空间 `
LinearMap`。
形式化陈述：leftInverse_splittingOfFinsuppSurjective (f : M ->ₗ[R] α ->₀ R) (s : Surje
ctive f) : LeftInverse f (splittingOfFinsuppSurjective f s)
参数：f : M ->ₗ[R] α ->₀ R；s : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `LinearMap.splittingOfFinsuppSurjective_splits`：splittingOfFinsuppSurject
ive_splits (f : M ->ₗ[R] α ->₀ R) (s : Surjective f) : f.comp (splittingOfFinsup
pSurjective f s) = LinearMap.id
-/
theorem leftInverse_splittingOfFinsuppSurjective (f : M →ₗ[R] α →₀ R) (s : Surjective f) :
    LeftInverse f (splittingOfFinsuppSurjective f s) := fun g =>
  LinearMap.congr_fun (splittingOfFinsuppSurjective_splits f s) g
/-
**LinearMap.splittingOfFinsuppSurjective_injective** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearMap`。
形式化陈述：splittingOfFinsuppSurjective_injective (f : M ->ₗ[R] α ->₀ R) (s : Surject
ive f) : Injective (splittingOfFinsuppSurjective f s)
参数：f : M ->ₗ[R] α ->₀ R；s : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `LinearMap.leftInverse_splittingOfFinsuppSurjective`：leftInverse_splittin
gOfFinsuppSurjective (f : M ->ₗ[R] α ->₀ R) (s : Surjective f) : LeftInverse f (
splittingOfFinsuppSurjective f s)
-/
theorem splittingOfFinsuppSurjective_injective (f : M →ₗ[R] α →₀ R) (s : Surjective f) :
    Injective (splittingOfFinsuppSurjective f s) :=
  (leftInverse_splittingOfFinsuppSurjective f s).injective

end LinearMap

namespace LinearMap

section AddCommMonoid

variable {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} {ι : Type*}
variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂] {σ₁₂ : R →+* R₂}
variable [Module R M] [Module R₂ M₂]
variable {γ : Type*} [Zero γ]

section Finsupp

/-
**LinearMap.coe_finsupp_sum** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_finsupp_sum (t : ι ->₀ γ) (g : ι -> γ -> M ->ₛₗ[σ₁₂] M₂) : ⇑(t.sum g) 
= t.sum fun i d => g i d
参数：t : ι ->₀ γ；g : ι -> γ -> M ->ₛₗ[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_finsupp_sum (t : ι →₀ γ) (g : ι → γ → M →ₛₗ[σ₁₂] M₂) :
    ⇑(t.sum g) = t.sum fun i d => g i d := rfl

@[simp]
/-
**LinearMap.finsupp_sum_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：finsupp_sum_apply (t : ι ->₀ γ) (g : ι -> γ -> M ->ₛₗ[σ₁₂] M₂) (b : M) : (
t.sum g) b = t.sum fun i d => g i d b
参数：t : ι ->₀ γ；g : ι -> γ -> M ->ₛₗ[σ₁₂] M₂；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.sum_apply`：sum_apply (t : Finset ι) (f : ι -> M ->ₛₗ[σ₁₂] M₂) 
(b : M) : (∑ d in t, f d) b = ∑ d in t, f d b
-/
theorem finsupp_sum_apply (t : ι →₀ γ) (g : ι → γ → M →ₛₗ[σ₁₂] M₂) (b : M) :
    (t.sum g) b = t.sum fun i d => g i d b :=
  sum_apply _ _ _

end Finsupp

end AddCommMonoid

end LinearMap

namespace Submodule

variable {S : Type*} [Semiring S] [Module R S] [SMulCommClass R R S]

section
variable [SMulCommClass R S S]

/-- If `M` and `N` are submodules of an `R`-algebra `S`, `m : ι → M` is a family of elements, then
there is an `R`-linear map from `ι →₀ N` to `S` which maps `{ n_i }` to the sum of `m_i * n_i`.
This is used in the definition of linearly disjointness. -/
/-
**Submodule.mulLeftMap** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：mulLeftMap {M : Submodule R S} (N : Submodule R S) {ι : Type*} (m : ι -> M
) : (ι ->₀ N) ->ₗ[R] S
参数：N : Submodule R S；m : ι -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` and `N` are submodules of an `R`-algebra `S`, `m : ι → M` is a family of 
elements, then
there is an `R`-linear map from `ι →₀ N` to `S` which maps `{ n_i }` to the sum 
of `m_i * n_i`.
This is used in the definition of linearly disjointness.
-/
def mulLeftMap {M : Submodule R S} (N : Submodule R S) {ι : Type*} (m : ι → M) :
    (ι →₀ N) →ₗ[R] S := Finsupp.lsum R fun i ↦ (m i).1 • N.subtype
/-
**Submodule.mulLeftMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mulLeftMap_apply {M N : Submodule R S} {ι : Type*} (m : ι -> M) (n : ι ->₀
 N) : mulLeftMap N m n = Finsupp.sum n fun (i : ι) (n : N) => (m i).1 * n.1
参数：m : ι -> M；n : ι ->₀ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulLeftMap_apply {M N : Submodule R S} {ι : Type*} (m : ι → M) (n : ι →₀ N) :
    mulLeftMap N m n = Finsupp.sum n fun (i : ι) (n : N) ↦ (m i).1 * n.1 := rfl

@[simp]
/-
**Submodule.mulLeftMap_apply_single** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mulLeftMap_apply_single {M N : Submodule R S} {ι : Type*} (m : ι -> M) (i 
: ι) (n : N) : mulLeftMap N m (Finsupp.single i n) = (m i).1 * n.1
参数：m : ι -> M；i : ι；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulLeftMap_apply_single {M N : Submodule R S} {ι : Type*} (m : ι → M) (i : ι) (n : N) :
    mulLeftMap N m (Finsupp.single i n) = (m i).1 * n.1 := by
  simp [mulLeftMap]

end

variable [IsScalarTower R S S]

/-- If `M` and `N` are submodules of an `R`-algebra `S`, `n : ι → N` is a family of elements, then
there is an `R`-linear map from `ι →₀ M` to `S` which maps `{ m_i }` to the sum of `m_i * n_i`.
This is used in the definition of linearly disjointness. -/
/-
**Submodule.mulRightMap** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：mulRightMap (M : Submodule R S) {N : Submodule R S} {ι : Type*} (n : ι -> 
N) : (ι ->₀ M) ->ₗ[R] S
参数：M : Submodule R S；n : ι -> N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` and `N` are submodules of an `R`-algebra `S`, `n : ι → N` is a family of 
elements, then
there is an `R`-linear map from `ι →₀ M` to `S` which maps `{ m_i }` to the sum 
of `m_i * n_i`.
This is used in the definition of linearly disjointness.
-/
def mulRightMap (M : Submodule R S) {N : Submodule R S} {ι : Type*} (n : ι → N) :
    (ι →₀ M) →ₗ[R] S := Finsupp.lsum R fun i ↦ MulOpposite.op (n i).1 • M.subtype
/-
**Submodule.mulRightMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mulRightMap_apply {M N : Submodule R S} {ι : Type*} (n : ι -> N) (m : ι ->
₀ M) : mulRightMap M n m = Finsupp.sum m fun (i : ι) (m : M) => m.1 * (n i).1
参数：n : ι -> N；m : ι ->₀ M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulRightMap_apply {M N : Submodule R S} {ι : Type*} (n : ι → N) (m : ι →₀ M) :
    mulRightMap M n m = Finsupp.sum m fun (i : ι) (m : M) ↦ m.1 * (n i).1 := rfl

@[simp]
/-
**Submodule.mulRightMap_apply_single** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mulRightMap_apply_single {M N : Submodule R S} {ι : Type*} (n : ι -> N) (i
 : ι) (m : M) : mulRightMap M n (Finsupp.single i m) = m.1 * (n i).1
参数：n : ι -> N；i : ι；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulRightMap_apply_single {M N : Submodule R S} {ι : Type*} (n : ι → N) (i : ι) (m : M) :
    mulRightMap M n (Finsupp.single i m) = m.1 * (n i).1 := by
  simp [mulRightMap]
/-
**Submodule.mulLeftMap_eq_mulRightMap_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `Subm
odule`。
形式化陈述：mulLeftMap_eq_mulRightMap_of_commute [SMulCommClass R S S] {M : Submodule 
R S} (N : Submodule R S) {ι : Type*} (m : ι -> M) (hc : forall (i : ι) (n : N), 
Commute (m i).1 n.1) : mulLeftMap N m = mulRightMap N m
参数：N : Submodule R S；m : ι -> M；hc : forall (i : ι) (n : N), Commute (m i).1 n.1
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mulLeftMap_apply_single`：mulLeftMap_apply_single {M N : Submod
ule R S} {ι : Type*} (m : ι -> M) (i : ι) (n : N) : mulLeftMap N m (Finsupp.sing
le i n) = (m i).1 * n.1
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Submodule.mulRightMap_apply_single`：mulRightMap_apply_single {M N : Subm
odule R S} {ι : Type*} (n : ι -> N) (i : ι) (m : M) : mulRightMap M n (Finsupp.s
ingle i m) = m.1 * (n i)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulLeftMap_eq_mulRightMap_of_commute [SMulCommClass R S S]
    {M : Submodule R S} (N : Submodule R S) {ι : Type*} (m : ι → M)
    (hc : ∀ (i : ι) (n : N), Commute (m i).1 n.1) : mulLeftMap N m = mulRightMap N m := by
  ext i n; simp [(hc i n).eq]
/-
**Submodule.mulLeftMap_eq_mulRightMap** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mulLeftMap_eq_mulRightMap {S : Type*} [CommSemiring S] [Module R S] [SMulC
ommClass R R S] [SMulCommClass R S S] [IsScalarTower R S S] {M : Submodule R S} 
(N : Submodule R S) {ι : Type*} (m : ι -> M) : mulLeftMap N m = mulRightMap N m
参数：N : Submodule R S；m : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mulLeftMap_eq_mulRightMap_of_commute`：mulLeftMap_eq_mulRightMa
p_of_commute [SMulCommClass R S S] {M : Submodule R S} (N : Submodule R S) {ι : 
Type*} (m : ι -> M) (hc : forall (i …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem mulLeftMap_eq_mulRightMap {S : Type*} [CommSemiring S] [Module R S] [SMulCommClass R R S]
    [SMulCommClass R S S] [IsScalarTower R S S] {M : Submodule R S} (N : Submodule R S)
    {ι : Type*} (m : ι → M) : mulLeftMap N m = mulRightMap N m :=
  mulLeftMap_eq_mulRightMap_of_commute N m fun _ _ ↦ mul_comm _ _

end Submodule

