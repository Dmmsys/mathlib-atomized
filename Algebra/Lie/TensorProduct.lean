/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Tensor products of Lie modules

Tensor products of Lie modules carry natural Lie module structures.

## Tags

lie module, tensor product, universal property
-/

@[expose] public section

universe u v w w₁ w₂ w₃

variable {R : Type u} [CommRing R]

open LieModule

namespace TensorProduct

open scoped TensorProduct

namespace LieModule

variable {L : Type v} {M : Type w} {N : Type w₁} {P : Type w₂} {Q : Type w₃}
variable [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
variable [AddCommGroup P] [Module R P] [LieRingModule L P] [LieModule R L P]
variable [AddCommGroup Q] [Module R Q] [LieRingModule L Q] [LieModule R L Q]

attribute [local ext] TensorProduct.ext

/-- It is useful to define the bracket via this auxiliary function so that we have a type-theoretic
expression of the fact that `L` acts by linear endomorphisms. It simplifies the proofs in
`lieRingModule` below. -/
/-
**TensorProduct.LieModule.hasBracketAux** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct
.LieModule`。
形式化陈述：hasBracketAux (x : L) : Module.End R (M otimes[R] N)
参数：x : L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
It is useful to define the bracket via this auxiliary function so that we have a
 type-theoretic
expression of the fact that `L` acts by linear endomorphisms. It simplifies the 
proofs in
`lieRingModule` below.
-/
def hasBracketAux (x : L) : Module.End R (M ⊗[R] N) :=
  (toEnd R L M x).rTensor N + (toEnd R L N x).lTensor M

/-- The tensor product of two Lie modules is a Lie ring module. -/
/-
**TensorProduct.LieModule.lieRingModule** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct
.LieModule`。
形式化陈述：lieRingModule : LieRingModule L (M otimes[R] N) where bracket x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two Lie modules is a Lie ring module.
-/
instance lieRingModule : LieRingModule L (M ⊗[R] N) where
  bracket x := hasBracketAux x
  add_lie x y t := by
    simp only [hasBracketAux, LinearMap.lTensor_add, LinearMap.rTensor_add, map_add,
      LinearMap.add_apply]
    abel
  lie_add _ := map_add _
  leibniz_lie x y t := by
    suffices (hasBracketAux x).comp (hasBracketAux y) =
        hasBracketAux ⁅x, y⁆ + (hasBracketAux y).comp (hasBracketAux x) by
      rw [← LinearMap.comp_apply, this]; rfl
    ext m n
    simp only [hasBracketAux, AlgebraTensorModule.curry_apply, curry_apply, sub_tmul, tmul_sub,
      LinearMap.coe_restrictScalars, Function.comp_apply, LinearMap.coe_comp,
      LinearMap.rTensor_tmul, LieHom.map_lie, toEnd_apply_apply, LinearMap.add_apply,
      map_add, LieHom.lie_apply, Module.End.lie_apply, LinearMap.lTensor_tmul]
    abel

set_option backward.isDefEq.respectTransparency false in
/-- The tensor product of two Lie modules is a Lie module. -/
/-
**TensorProduct.LieModule.lieModule** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct.Lie
Module`。
形式化陈述：lieModule : LieModule R L (M otimes[R] N) where smul_lie c x t
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `LieHom.instLinearMapClass`：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [i
nst : CommRing R] [inst_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : L
ieRing L₂] [ins…
· 使用定理 `LinearMap.rTensor_smul`：rTensor_smul (r : R) (f : N ->ₗ[R] P) : (r • f).
rTensor M = r • f.rTensor M
· 使用定理 `LinearMap.lTensor_smul`：lTensor_smul (r : R) (f : N ->ₗ[R] P) : (r • f).
lTensor M = r • f.lTensor M
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The tensor product of two Lie modules is a Lie module.
-/
instance lieModule : LieModule R L (M ⊗[R] N) where
  smul_lie c x t := by
    change hasBracketAux (c • x) _ = c • hasBracketAux _ _
    simp only [hasBracketAux, smul_add, LinearMap.rTensor_smul, LinearMap.smul_apply,
      LinearMap.lTensor_smul, map_smul, LinearMap.add_apply]
  lie_smul c _ := map_smul _ c

@[simp]
/-
**TensorProduct.LieModule.lie_tmul_right** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduc
t.LieModule`。
形式化陈述：lie_tmul_right (x : L) (m : M) (n : N) : ⁅x, m otimesₜ[R] n⁆ = ⁅x, m⁆ otim
esₜ n + m otimesₜ ⁅x, n⁆
参数：x : L；m : M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lie_tmul_right (x : L) (m : M) (n : N) : ⁅x, m ⊗ₜ[R] n⁆ = ⁅x, m⁆ ⊗ₜ n + m ⊗ₜ ⁅x, n⁆ :=
  show hasBracketAux x (m ⊗ₜ[R] n) = _ by
    simp only [hasBracketAux, LinearMap.rTensor_tmul, toEnd_apply_apply,
      LinearMap.add_apply, LinearMap.lTensor_tmul]

variable (R L M N P Q)

/-- The universal property for tensor product of modules of a Lie algebra: the `R`-linear
tensor-hom adjunction is equivariant with respect to the `L` action. -/
/-
**TensorProduct.LieModule.lift** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct.LieModul
e`。
形式化陈述：lift : (M ->ₗ[R] N ->ₗ[R] P) ≃ₗ⁅R,L⁆ M otimes[R] N ->ₗ[R] P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property for tensor product of modules of a Lie algebra: the `R`-l
inear
tensor-hom adjunction is equivariant with respect to the `L` action.
-/
def lift : (M →ₗ[R] N →ₗ[R] P) ≃ₗ⁅R,L⁆ M ⊗[R] N →ₗ[R] P :=
  { TensorProduct.lift.equiv (.id R) M N P with
    map_lie' := fun {x f} => by
      ext m n
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
        lift.equiv_apply, LieHom.lie_apply, LinearMap.sub_apply, lie_tmul_right, map_add]
      abel }

@[simp]
/-
**TensorProduct.LieModule.lift_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct.Li
eModule`。
形式化陈述：lift_apply (f : M ->ₗ[R] N ->ₗ[R] P) (m : M) (n : N) : lift R L M N P f (m
 otimesₜ n) = f m n
参数：f : M ->ₗ[R] N ->ₗ[R] P；m : M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem lift_apply (f : M →ₗ[R] N →ₗ[R] P) (m : M) (n : N) : lift R L M N P f (m ⊗ₜ n) = f m n :=
  rfl

/-- A weaker form of the universal property for tensor product of modules of a Lie algebra.

Note that maps `f` of type `M →ₗ⁅R,L⁆ N →ₗ[R] P` are exactly those `R`-bilinear maps satisfying
`⁅x, f m n⁆ = f ⁅x, m⁆ n + f m ⁅x, n⁆` for all `x, m, n` (see e.g, `LieModuleHom.map_lie₂`). -/
/-
**TensorProduct.LieModule.liftLie** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct.LieMo
dule`。
形式化陈述：liftLie : (M ->ₗ⁅R,L⁆ N ->ₗ[R] P) ≃ₗ[R] M otimes[R] N ->ₗ⁅R,L⁆ P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A weaker form of the universal property for tensor product of modules of a Lie a
lgebra.

Note that maps `f` of type `M →ₗ⁅R,L⁆ N →ₗ[R] P` are exactly those `R`-bilinear 
maps satisfying
`⁅x, f m n⁆ = f ⁅x, m⁆ n + f m ⁅x, n⁆` for all `x, m, n` (see e.g, `LieModuleHom
.map_lie₂`).
-/
def liftLie : (M →ₗ⁅R,L⁆ N →ₗ[R] P) ≃ₗ[R] M ⊗[R] N →ₗ⁅R,L⁆ P :=
  maxTrivLinearMapEquivLieModuleHom.symm ≪≫ₗ ↑(maxTrivEquiv (lift R L M N P)) ≪≫ₗ
    maxTrivLinearMapEquivLieModuleHom

@[simp]
/-
**TensorProduct.LieModule.coe_liftLie_eq_lift_coe** 是 Mathlib 中的一个定理，位于命名空间 `Ten
sorProduct.LieModule`。
形式化陈述：coe_liftLie_eq_lift_coe (f : M ->ₗ⁅R,L⁆ N ->ₗ[R] P) : ⇑(liftLie R L M N P 
f) = lift R L M N P f
参数：f : M ->ₗ⁅R,L⁆ N ->ₗ[R] P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_liftLie_eq_lift_coe (f : M →ₗ⁅R,L⁆ N →ₗ[R] P) :
    ⇑(liftLie R L M N P f) = lift R L M N P f := by
  tauto
/-
**TensorProduct.LieModule.liftLie_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct
.LieModule`。
形式化陈述：liftLie_apply (f : M ->ₗ⁅R,L⁆ N ->ₗ[R] P) (m : M) (n : N) : liftLie R L M 
N P f (m otimesₜ n) = f m n
参数：f : M ->ₗ⁅R,L⁆ N ->ₗ[R] P；m : M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `TensorProduct.LieModule.coe_liftLie_eq_lift_coe`：coe_liftLie_eq_lift_coe
 (f : M ->ₗ⁅R,L⁆ N ->ₗ[R] P) : ⇑(liftLie R L M N P f) = lift R L M N P f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftLie_apply (f : M →ₗ⁅R,L⁆ N →ₗ[R] P) (m : M) (n : N) :
    liftLie R L M N P f (m ⊗ₜ n) = f m n := by
  simp only [coe_liftLie_eq_lift_coe, LieModuleHom.coe_toLinearMap, lift_apply]

variable {R L M N P Q}

/-- A pair of Lie module morphisms `f : M → P` and `g : N → Q`, induce a Lie module morphism:
`M ⊗ N → P ⊗ Q`. -/
nonrec def map (f : M →ₗ⁅R,L⁆ P) (g : N →ₗ⁅R,L⁆ Q) : M ⊗[R] N →ₗ⁅R,L⁆ P ⊗[R] Q :=
  { map (f : M →ₗ[R] P) (g : N →ₗ[R] Q) with
    map_lie' := fun {x t} => by
      simp only [LinearMap.toFun_eq_coe]
      refine t.induction_on ?_ ?_ ?_
      · simp only [map_zero, lie_zero]
      · intro m n
        simp only [LieModuleHom.coe_toLinearMap, lie_tmul_right, LieModuleHom.map_lie, map_tmul,
          map_add]
      · intro t₁ t₂ ht₁ ht₂; simp only [ht₁, ht₂, lie_add, map_add] }

@[simp]
/-
**TensorProduct.LieModule.toLinearMap_map** 是 Mathlib 中的一个定理，位于命名空间 `TensorProdu
ct.LieModule`。
形式化陈述：toLinearMap_map (f : M ->ₗ⁅R,L⁆ P) (g : N ->ₗ⁅R,L⁆ Q) : (map f g : M otime
s[R] N ->ₗ[R] P otimes[R] Q) = TensorProduct.map (f : M ->ₗ[R] P) (g : N ->ₗ[R] 
Q)
参数：f : M ->ₗ⁅R,L⁆ P；g : N ->ₗ⁅R,L⁆ Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_map (f : M →ₗ⁅R,L⁆ P) (g : N →ₗ⁅R,L⁆ Q) :
    (map f g : M ⊗[R] N →ₗ[R] P ⊗[R] Q) = TensorProduct.map (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :=
  rfl

@[simp]
nonrec theorem map_tmul (f : M →ₗ⁅R,L⁆ P) (g : N →ₗ⁅R,L⁆ Q) (m : M) (n : N) :
    map f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
  map_tmul _ _ _ _

/-- Given Lie submodules `M' ⊆ M` and `N' ⊆ N`, this is the natural map: `M' ⊗ N' → M ⊗ N`. -/
/-
**TensorProduct.LieModule.mapIncl** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct.LieMo
dule`。
形式化陈述：mapIncl (M' : LieSubmodule R L M) (N' : LieSubmodule R L N) : M' otimes[R]
 N' ->ₗ⁅R,L⁆ M otimes[R] N
参数：M' : LieSubmodule R L M；N' : LieSubmodule R L N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […

--- 原说明 ---
Given Lie submodules `M' ⊆ M` and `N' ⊆ N`, this is the natural map: `M' ⊗ N' → 
M ⊗ N`.
-/
def mapIncl (M' : LieSubmodule R L M) (N' : LieSubmodule R L N) : M' ⊗[R] N' →ₗ⁅R,L⁆ M ⊗[R] N :=
  map M'.incl N'.incl

@[simp]
/-
**TensorProduct.LieModule.mapIncl_def** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct.L
ieModule`。
形式化陈述：mapIncl_def (M' : LieSubmodule R L M) (N' : LieSubmodule R L N) : mapIncl 
M' N' = map M'.incl N'.incl
参数：M' : LieSubmodule R L M；N' : LieSubmodule R L N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
theorem mapIncl_def (M' : LieSubmodule R L M) (N' : LieSubmodule R L N) :
    mapIncl M' N' = map M'.incl N'.incl :=
  rfl

end LieModule

end TensorProduct

namespace LieModule

open scoped TensorProduct

variable (R) (L : Type v) (M : Type w)
variable [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The action of the Lie algebra on one of its modules, regarded as a morphism of Lie modules. -/
/-
**LieModule.toModuleHom** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：toModuleHom : L otimes[R] M ->ₗ⁅R,L⁆ M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action of the Lie algebra on one of its modules, regarded as a morphism of L
ie modules.
-/
def toModuleHom : L ⊗[R] M →ₗ⁅R,L⁆ M :=
  TensorProduct.LieModule.liftLie R L L M M
    { (toEnd R L M : L →ₗ[R] M →ₗ[R] M) with
      map_lie' := fun {x m} => by ext n; simp [LieRing.of_associative_ring_bracket] }

@[simp]
/-
**LieModule.toModuleHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：toModuleHom_apply (x : L) (m : M) : toModuleHom R L M (x otimesₜ m) = ⁅x, 
m⁆
参数：x : L；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.LieModule.liftLie_apply`：liftLie_apply (f : M ->ₗ⁅R,L⁆ N -
>ₗ[R] P) (m : M) (n : N) : liftLie R L M N P f (m otimesₜ n) = f m n
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LieModuleHom.coe_mk`：coe_mk (f : M ->ₗ[R] N) (h) : ((⟨f, h⟩ : M ->ₗ⁅R,L⁆
 N) : M -> N) = f
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toModuleHom_apply (x : L) (m : M) : toModuleHom R L M (x ⊗ₜ m) = ⁅x, m⁆ := by
  simp only [toModuleHom, TensorProduct.LieModule.liftLie_apply, LieModuleHom.coe_mk,
    LieHom.coe_toLinearMap, toEnd_apply_apply]

end LieModule

namespace LieSubmodule

open scoped TensorProduct

open TensorProduct.LieModule

open LieModule

variable {L : Type v} {M : Type w}
variable [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable (I : LieIdeal R L) (N : LieSubmodule R L M)

/-- A useful alternative characterisation of Lie ideal operations on Lie submodules.

Given a Lie ideal `I ⊆ L` and a Lie submodule `N ⊆ M`, by tensoring the inclusion maps and then
applying the action of `L` on `M`, we obtain morphism of Lie modules `f : I ⊗ N → L ⊗ M → M`.

This lemma states that `⁅I, N⁆ = range f`. -/
/-
**LieSubmodule.lieIdeal_oper_eq_tensor_map_range** 是 Mathlib 中的一个定理，位于命名空间 `LieS
ubmodule`。
形式化陈述：lieIdeal_oper_eq_tensor_map_range : ⁅I, N⁆ = ((toModuleHom R L M).comp (ma
pIncl I N : I otimes[R] N ->ₗ⁅R,L⁆ L otimes[R] M)).range
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_linear_span`：lieIdeal_oper_eq_linear_span 
[LieModule R L M] : (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅(x : L), (n 
: M)⁆ | (x : I) (n : N) }
· 使用定理 `LieModuleHom.toSubmodule_range`：toSubmodule_range : f.range = LinearMap.
range (f : M ->ₗ[R] N)
· 使用定理 `LieModuleHom.toLinearMap_comp`：toLinearMap_comp (f : N ->ₗ⁅R,L⁆ P) (g : 
M ->ₗ⁅R,L⁆ N) : (f.comp g : M ->ₗ[R] P) = (f : N ->ₗ[R] P).comp (g : M ->ₗ[R] N)
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `TensorProduct.LieModule.mapIncl_def`：mapIncl_def (M' : LieSubmodule R L 
M) (N' : LieSubmodule R L N) : mapIncl M' N' = map M'.incl N'.incl
· 使用定理 `TensorProduct.LieModule.toLinearMap_map`：toLinearMap_map (f : M ->ₗ⁅R,L⁆
 P) (g : N ->ₗ⁅R,L⁆ Q) : (map f g : M otimes[R] N ->ₗ[R] P otimes[R] Q) = Tensor
Product.map (f : M ->ₗ[R] P) …
· 使用定理 `TensorProduct.range_map_eq_span_tmul`：range_map_eq_span_tmul (f : M ->ₗ[
R] P) (g : N ->ₗ[R] Q) : range (map f g) = Submodule.span R { t | exists m n, f 
m otimesₜ g n = t }
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieModule.toModuleHom_apply`：toModuleHom_apply (x : L) (m : M) : toModul
eHom R L M (x otimesₜ m) = ⁅x, m⁆
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A useful alternative characterisation of Lie ideal operations on Lie submodules.

Given a Lie ideal `I ⊆ L` and a Lie submodule `N ⊆ M`, by tensoring the inclusio
n maps and then
applying the action of `L` on `M`, we obtain morphism of Lie modules `f : I ⊗ N 
→ L ⊗ M → M`.

This lemma states that `⁅I, N⁆ = range f`.
-/
theorem lieIdeal_oper_eq_tensor_map_range :
    ⁅I, N⁆ = ((toModuleHom R L M).comp (mapIncl I N : I ⊗[R] N →ₗ⁅R,L⁆ L ⊗[R] M)).range := by
  rw [← toSubmodule_inj, lieIdeal_oper_eq_linear_span, LieModuleHom.toSubmodule_range,
    LieModuleHom.toLinearMap_comp, LinearMap.range_comp, mapIncl_def, toLinearMap_map,
    TensorProduct.range_map_eq_span_tmul, Submodule.map_span]
  congr; ext m; constructor
  · rintro ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩; use x ⊗ₜ n; constructor
    · use ⟨x, hx⟩, ⟨n, hn⟩; rfl
    · simp
  · rintro ⟨t, ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩, h⟩; rw [← h]; use ⟨x, hx⟩, ⟨n, hn⟩; rfl

end LieSubmodule

