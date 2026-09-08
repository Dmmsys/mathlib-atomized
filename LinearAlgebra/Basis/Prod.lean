/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Bases for the product of modules
-/

@[expose] public section

assert_not_exists Ordinal

noncomputable section

universe u

open Function Set Submodule Finsupp

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

namespace Module.Basis

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

section Prod

variable (b' : Basis ι' R M')

/-- `Basis.prod` maps an `ι`-indexed basis for `M` and an `ι'`-indexed basis for `M'`
to an `ι ⊕ ι'`-index basis for `M × M'`.
For the specific case of `R × R`, see also `Basis.finTwoProd`. -/
/-
**Module.Basis.prod** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：{ι : Type u_1} →   {ι' : Type u_2} →     {R : Type u_3} →       {M : Type 
u_5} →         {M' : Type u_6} →           [inst : Semiring R] →             [in
st_1 : AddCommMonoid M] →               [inst_2 : _root_.Module R M] →          
       [inst_3 : AddCommMonoid M'] →                   [inst_4 : _root_.Module R
 M'] →                     Module.Basis ι R M → Module.Basis ι' R M' → Module.Ba
sis (ι ⊕ ι') R (M × M')
参数：ι ⊕ ι'；M × M'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Basis.prod` maps an `ι`-indexed basis for `M` and an `ι'`-indexed basis for `M'
`
to an `ι ⊕ ι'`-index basis for `M × M'`.
For the specific case of `R × R`, see also `Basis.finTwoProd`.
-/
protected def prod : Basis (ι ⊕ ι') R (M × M') :=
  ofRepr ((b.repr.prodCongr b'.repr).trans (Finsupp.sumFinsuppLEquivProdFinsupp R).symm)

@[simp]
/-
**Module.Basis.prod_repr_inl** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：prod_repr_inl (x) (i) : (b.prod b').repr x (Sum.inl i) = b.repr x.1 i
参数：x；i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_repr_inl (x) (i) : (b.prod b').repr x (Sum.inl i) = b.repr x.1 i :=
  rfl

@[simp]
/-
**Module.Basis.prod_repr_inr** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：prod_repr_inr (x) (i) : (b.prod b').repr x (Sum.inr i) = b'.repr x.2 i
参数：x；i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_repr_inr (x) (i) : (b.prod b').repr x (Sum.inr i) = b'.repr x.2 i :=
  rfl
/-
**Module.Basis.prod_apply_inl_fst** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：prod_apply_inl_fst (i) : (b.prod b' (Sum.inl i)).1 = b i
参数：i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_apply_left`：single_apply_left {f : α -> β} (hf : Function
.Injective f) (x z : α) (y : M) : single (f x) y (f z) = single x y z
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
-/
theorem prod_apply_inl_fst (i) : (b.prod b' (Sum.inl i)).1 = b i :=
  b.repr.injective <| by
    ext j
    simp only [Basis.prod, Basis.coe_ofRepr, LinearEquiv.symm_trans_apply,
      LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply, b.repr.apply_symm_apply,
      LinearEquiv.symm_symm, repr_self, Finsupp.fst_sumFinsuppLEquivProdFinsupp]
    apply Finsupp.single_apply_left Sum.inl_injective
/-
**Module.Basis.prod_apply_inr_fst** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：prod_apply_inr_fst (i) : (b.prod b' (Sum.inr i)).1 = 0
参数：i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `Sum.inl_ne_inr`：∀ {α : Type u_1} {a : α} {β : Type u_2} {b : β}, Sum.inl
 a ≠ Sum.inr b
-/
theorem prod_apply_inr_fst (i) : (b.prod b' (Sum.inr i)).1 = 0 :=
  b.repr.injective <| by
    ext i
    simp only [Basis.prod, Basis.coe_ofRepr, LinearEquiv.symm_trans_apply,
      LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply, b.repr.apply_symm_apply,
      LinearEquiv.symm_symm, Finsupp.fst_sumFinsuppLEquivProdFinsupp,
      map_zero, Finsupp.zero_apply]
    apply Finsupp.single_eq_of_ne Sum.inl_ne_inr
/-
**Module.Basis.prod_apply_inl_snd** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：prod_apply_inl_snd (i) : (b.prod b' (Sum.inl i)).2 = 0
参数：i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `Sum.inr_ne_inl`：∀ {β : Type u_1} {b : β} {α : Type u_2} {a : α}, Sum.inr
 b ≠ Sum.inl a
-/
theorem prod_apply_inl_snd (i) : (b.prod b' (Sum.inl i)).2 = 0 :=
  b'.repr.injective <| by
    ext j
    simp only [Basis.prod, Basis.coe_ofRepr, LinearEquiv.symm_trans_apply,
      LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply, b'.repr.apply_symm_apply,
      LinearEquiv.symm_symm, Finsupp.snd_sumFinsuppLEquivProdFinsupp,
      map_zero, Finsupp.zero_apply]
    apply Finsupp.single_eq_of_ne Sum.inr_ne_inl
/-
**Module.Basis.prod_apply_inr_snd** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：prod_apply_inr_snd (i) : (b.prod b' (Sum.inr i)).2 = b' i
参数：i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_apply_left`：single_apply_left {f : α -> β} (hf : Function
.Injective f) (x z : α) (y : M) : single (f x) y (f z) = single x y z
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
-/
theorem prod_apply_inr_snd (i) : (b.prod b' (Sum.inr i)).2 = b' i :=
  b'.repr.injective <| by
    ext i
    simp only [Basis.prod, Basis.coe_ofRepr, LinearEquiv.symm_trans_apply,
      LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply, b'.repr.apply_symm_apply,
      LinearEquiv.symm_symm, repr_self, Finsupp.snd_sumFinsuppLEquivProdFinsupp]
    apply Finsupp.single_apply_left Sum.inr_injective

@[simp]
/-
**Module.Basis.prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：prod_apply (i) : b.prod b' i = Sum.elim (LinearMap.inl R M M' ∘ b) (Linear
Map.inr R M M' ∘ b') i
参数：i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.prod_apply_inl_fst`：prod_apply_inl_fst (i) : (b.prod b' (Su
m.inl i)).1 = b i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.prod_apply_inr_fst`：prod_apply_inr_fst (i) : (b.prod b' (Su
m.inr i)).1 = 0
· 使用定理 `Module.Basis.prod_apply_inl_snd`：prod_apply_inl_snd (i) : (b.prod b' (Su
m.inl i)).2 = 0
· 使用定理 `Module.Basis.prod_apply_inr_snd`：prod_apply_inr_snd (i) : (b.prod b' (Su
m.inr i)).2 = b' i
-/
theorem prod_apply (i) :
    b.prod b' i = Sum.elim (LinearMap.inl R M M' ∘ b) (LinearMap.inr R M M' ∘ b') i := by
  ext <;> cases i <;>
    simp only [prod_apply_inl_fst, Sum.elim_inl, LinearMap.inl_apply, prod_apply_inr_fst,
      Sum.elim_inr, LinearMap.inr_apply, prod_apply_inl_snd, prod_apply_inr_snd, Function.comp]

end Prod

end Basis

namespace Free

variable (R M N : Type*) [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
/-
**Module.Free.prod** 是 Mathlib 中的一个定理，位于命名空间 `Module.Free`。
形式化陈述：∀ (R : Type u_7) (M : Type u_8) (N : Type u_9) [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : AddCommMonoid N] [i
nst_4 : _root_.Module R N] [Module.Free R M]   [Module.Free R N], Module.Free R 
(M × N)
参数：R : Type u_7；M : Type u_8；N : Type u_9；M × N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
-/
instance prod [Module.Free R M] [Module.Free R N] : Module.Free R (M × N) :=
  .of_basis <| (Module.Free.chooseBasis R M).prod (Module.Free.chooseBasis R N)

end Free

end Module

