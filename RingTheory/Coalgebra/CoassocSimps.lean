/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yaël Dillies
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Coalgebra.Basic

import Mathlib.Tactic.Attr.Register

/-!
# Tactic to reassociate comultiplication in a coalgebra

`coassoc_simps` is a simp set useful to prove tautologies on coalgebras.

The general algorithm it follows is to push the associators `TensorProduct.assoc` and
commutators `TensorProduct.comm` inwards (to the right) until they cancel against
co-multiplications.

The simp set makes the following choice of normal form
* It regards `TensorProduct.map`, `TensorProduct.assoc`, `TensorProduct.comm` as the primitive
  constructions and rewrites everything else such as `lTensor`, `leftComm` using them.
* It rewrites both sides into a right associated composition of linear maps.
  In particular `LinearMap.comp_assoc` and `LinearEquiv.coe_trans` are tagged.
* It rewrites `(f₂ ⊗ g₂) ∘ (f₁ ⊗ g₁)` into `(f₂ ∘ f₁) ⊗ (g₂ ∘ g₁)`.

## Notes

- It is not confluent with `(ε ⊗ₘ id) ∘ₗ δ = λ⁻¹`.
  It is often useful to `trans` (or `calc`) with a term containing
  `(ε ⊗ₘ _) ∘ₗ δ` or `(_ ⊗ₘ ε) ∘ₗ δ`,
  and use one of `map_counit_comp_comul_left` `map_counit_comp_comul_right`
  `map_counit_comp_comul_left_assoc` `map_counit_comp_comul_right_assoc` to continue.

- Some lemmas (e.g. `lid_comp_map : λ ∘ₗ (f ⊗ₘ g) = g ∘ₗ λ ∘ₗ (f ⊗ₘ id)`) loops when tagged as simp,
  so we wrap it inside a rudimentary simproc that only fires when `g ≠ id`.
-/

@[expose] public section

open TensorProduct

open LinearMap (id)
open Coalgebra

open Qq
namespace CoassocSimps

variable {R A M N P M' N' P' Q Q' M₁ M₂ M₃ N₁ N₂ N₃ : Type*}
    [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    [AddCommMonoid P'] [Module R P'] [AddCommMonoid Q] [Module R Q] [AddCommMonoid Q'] [Module R Q']
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
    [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
    [Module R M₁] [Module R M₂] [Module R M₃] [Module R N₁] [Module R N₂] [Module R N₃]

local notation3 "α" => (TensorProduct.assoc R _ _ _).toLinearMap
local notation3 "α⁻¹" => (TensorProduct.assoc R _ _ _).symm.toLinearMap
local notation3 "λ" => (TensorProduct.lid R _).toLinearMap
local notation3 "λ⁻¹" => (TensorProduct.lid R _).symm.toLinearMap
local notation3 "ρ" => (TensorProduct.rid R _).toLinearMap
local notation3 "ρ⁻¹" => (TensorProduct.rid R _).symm.toLinearMap
local notation3 "β" => (TensorProduct.comm R _ _).toLinearMap
local infix:90 " ⊗ₘ " => TensorProduct.map
local notation3 "δ" => comul (R := R)
local notation3 "ε" => counit (R := R)

attribute [coassoc_simps] LinearMap.comp_id LinearMap.id_comp TensorProduct.map_id
  LinearMap.lTensor_def LinearMap.rTensor_def LinearMap.comp_assoc
  LinearEquiv.coe_trans LinearEquiv.trans_symm
  LinearEquiv.refl_toLinearMap TensorProduct.toLinearMap_congr
  LinearEquiv.comp_symm LinearEquiv.symm_comp LinearEquiv.symm_symm
  LinearEquiv.coe_lTensor LinearEquiv.symm_lTensor
  LinearEquiv.coe_rTensor LinearEquiv.symm_rTensor
  IsCocomm.comm_comp_comul TensorProduct.AlgebraTensorModule.map_eq
  TensorProduct.AlgebraTensorModule.assoc_eq TensorProduct.AlgebraTensorModule.rightComm_eq
  TensorProduct.tensorTensorTensorComm TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
  TensorProduct.AlgebraTensorModule.congr_eq LinearEquiv.comp_symm_assoc
  LinearEquiv.symm_comp_assoc TensorProduct.rightComm_def TensorProduct.leftComm_def
  TensorProduct.comm_symm TensorProduct.comm_comp_comm TensorProduct.comm_comp_comm_assoc

attribute [coassoc_simps← ] TensorProduct.map_comp TensorProduct.map_map_comp_assoc_eq
  TensorProduct.map_map_comp_assoc_symm_eq

@[coassoc_simps]
/-
**CoassocSimps.TensorProduct.map_comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `CoassocSi
mps.TensorProduct`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {N : Type u_4} {P : Type u_5} {M' : Type u
_6} {N' : Type u_7} {P' : Type u_8}   {M₁ : Type u_11} [inst : CommSemiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst_3 : AddCommMonoid
 N] [inst_4 : _root_.Module R N] [inst_5 : AddCommMonoid P] [inst_6 : _root_.Mod
ule R P]   [inst_7 : AddCommMonoid M'] [inst_8 : _root_.Module R M'] [inst_9 : A
ddCommMonoid N'] [inst_10 : _root_.Module R N']   [inst_11 : AddCommMonoid P'] [
inst_12 : _root_.Module R P'] [inst_13 : AddCommMonoid M₁]   [inst_14 : _root_.M
odule R M₁] (f : M →ₗ[R] N) (g : N →ₗ[R] P) (f' : M' →ₗ[R] N') (g' : N' →ₗ[R] P'
)   (φ : M₁ →ₗ[R] TensorProduct R M M'),   TensorProduct.map g g' ∘ₗ TensorProdu
ct.map f f' ∘ₗ φ = TensorProduct.map (g ∘ₗ f) (g' ∘ₗ f') ∘ₗ φ
参数：f : M →ₗ[R] N；g : N →ₗ[R] P；f' : M' →ₗ[R] N'；g' : N' →ₗ[R] P'；φ : M₁ →ₗ[R] Te
nsorProduct R M M'；g ∘ₗ f；g' ∘ₗ f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `TensorProduct.map_comp`：map_comp (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂
₃] N₃) (f₁ : M ->ₛₗ[σ₁₂] M₂) (g₁ : N ->ₛₗ[σ₁₂] N₂) : map (f₂ ∘ₛₗ f₁) (g₂ ∘ₛₗ g₁)
 = (map f₂ g…
-/
lemma TensorProduct.map_comp_assoc
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (f' : M' →ₗ[R] N') (g' : N' →ₗ[R] P') (φ : M₁ →ₗ[R] M ⊗[R] M') :
    map g g' ∘ₗ map f f' ∘ₗ φ = map (g ∘ₗ f) (g' ∘ₗ f') ∘ₛₗ φ := by
  rw [← LinearMap.comp_assoc, TensorProduct.map_comp]

@[coassoc_simps← ]
/-
**CoassocSimps.TensorProduct.map_map_comp_assoc_eq_assoc** 是 Mathlib 中的一个定理，位于命名
空间 `CoassocSimps.TensorProduct`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {M₁ : Type u_11} {M₂ : Type u_12} {M₃ : Ty
pe u_13} {N₁ : Type u_14} {N₂ : Type u_15}   {N₃ : Type u_16} [inst : CommSemiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst_3 : AddCom
mMonoid M₁] [inst_4 : AddCommMonoid M₂] [inst_5 : AddCommMonoid M₃] [inst_6 : Ad
dCommMonoid N₁]   [inst_7 : AddCommMonoid N₂] [inst_8 : AddCommMonoid N₃] [inst_
9 : _root_.Module R M₁] [inst_10 : _root_.Module R M₂]   [inst_11 : _root_.Modul
e R M₃] [inst_12 : _root_.Module R N₁] [inst_13 : _root_.Module R N₂]   [inst_14
 : _root_.Module R N₃] (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) 
  (f : M →ₗ[R] TensorProduct R (TensorProduct R M₁ M₂) M₃),   TensorProduct.map 
f₁ (TensorProduct.map f₂ f₃) ∘ₗ ↑(TensorProduct.assoc R M₁ M₂ M₃) ∘ₗ f =     ↑(T
ensorProduct.assoc R N₁ N₂ N₃) ∘ₗ TensorProduct.map (TensorProduct.map f₁ f₂) f₃
 ∘ₗ f
参数：f₁ : M₁ →ₗ[R] N₁；f₂ : M₂ →ₗ[R] N₂；f₃ : M₃ →ₗ[R] N₃；f : M →ₗ[R] TensorProduct 
R (TensorProduct R M₁ M₂) M₃；TensorProduct.map f₂ f₃；TensorProduct.assoc R M₁ M₂
 M₃；TensorProduct.assoc R N₁ N₂ N₃；TensorProduct.map f₁ f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用引理 `TensorProduct.map_map_comp_assoc_eq`：map_map_comp_assoc_eq (f : M ->ₗ[R]
 Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) : map f (map g h) ∘ₗ TensorProduct.assoc R
 M N P = TensorProduct.as…
-/
lemma TensorProduct.map_map_comp_assoc_eq_assoc
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f : M →ₗ[R] M₁ ⊗[R] M₂ ⊗[R] M₃) :
    f₁ ⊗ₘ (f₂ ⊗ₘ f₃) ∘ₗ α ∘ₗ f = α ∘ₗ ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ∘ₗ f := by
  rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, TensorProduct.map_map_comp_assoc_eq]

@[coassoc_simps← ]
/-
**CoassocSimps.TensorProduct.map_map_comp_assoc_symm_eq_assoc** 是 Mathlib 中的一个定理
，位于命名空间 `CoassocSimps.TensorProduct`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {M₁ : Type u_11} {M₂ : Type u_12} {M₃ : Ty
pe u_13} {N₁ : Type u_14} {N₂ : Type u_15}   {N₃ : Type u_16} [inst : CommSemiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst_3 : AddCom
mMonoid M₁] [inst_4 : AddCommMonoid M₂] [inst_5 : AddCommMonoid M₃] [inst_6 : Ad
dCommMonoid N₁]   [inst_7 : AddCommMonoid N₂] [inst_8 : AddCommMonoid N₃] [inst_
9 : _root_.Module R M₁] [inst_10 : _root_.Module R M₂]   [inst_11 : _root_.Modul
e R M₃] [inst_12 : _root_.Module R N₁] [inst_13 : _root_.Module R N₂]   [inst_14
 : _root_.Module R N₃] (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) 
  (f : M →ₗ[R] TensorProduct R M₁ (TensorProduct R M₂ M₃)),   TensorProduct.map 
(TensorProduct.map f₁ f₂) f₃ ∘ₗ ↑(TensorProduct.assoc R M₁ M₂ M₃).symm ∘ₗ f =   
  ↑(TensorProduct.assoc R N₁ N₂ N₃).symm ∘ₗ TensorProduct.map f₁ (TensorProduct.
map f₂ f₃) ∘ₗ f
参数：f₁ : M₁ →ₗ[R] N₁；f₂ : M₂ →ₗ[R] N₂；f₃ : M₃ →ₗ[R] N₃；f : M →ₗ[R] TensorProduct 
R M₁ (TensorProduct R M₂ M₃)；TensorProduct.map f₁ f₂；TensorProduct.assoc R M₁ M₂
 M₃；TensorProduct.assoc R N₁ N₂ N₃；TensorProduct.map f₂ f₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用引理 `TensorProduct.map_map_comp_assoc_symm_eq`：map_map_comp_assoc_symm_eq (f 
: M ->ₗ[R] Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) : map (map f g) h ∘ₗ (TensorProd
uct.assoc R M N P).symm = (Ten…
-/
lemma TensorProduct.map_map_comp_assoc_symm_eq_assoc
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f : M →ₗ[R] M₁ ⊗[R] (M₂ ⊗[R] M₃)) :
    (f₁ ⊗ₘ f₂) ⊗ₘ f₃ ∘ₗ α⁻¹ ∘ₗ f = α⁻¹ ∘ₗ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) ∘ₗ f := by
  rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, TensorProduct.map_map_comp_assoc_symm_eq]

@[coassoc_simps]
/-
**CoassocSimps.assoc_comp_map_map_comp** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`。
形式化陈述：assoc_comp_map_map_comp (f₁ : M₁ ->ₗ[R] N₁) (f₂ : M₂ ->ₗ[R] N₂) (f₃ : M₃ -
>ₗ[R] N₃) (f₁₂ : M ->ₗ[R] M₁ otimes[R] M₂) : α ∘ₗ (((f₁ otimesₘ f₂) ∘ₗ f₁₂) otim
esₘ f₃) = (f₁ otimesₘ (f₂ otimesₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ otimesₘ id)
参数：f₁ : M₁ ->ₗ[R] N₁；f₂ : M₂ ->ₗ[R] N₂；f₃ : M₃ ->ₗ[R] N₃；f₁₂ : M ->ₗ[R] M₁ otime
s[R] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用引理 `TensorProduct.map_map_comp_assoc_eq`：map_map_comp_assoc_eq (f : M ->ₗ[R]
 Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) : map f (map g h) ∘ₗ TensorProduct.assoc R
 M N P = TensorProduct.as…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma assoc_comp_map_map_comp
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f₁₂ : M →ₗ[R] M₁ ⊗[R] M₂) :
    α ∘ₗ (((f₁ ⊗ₘ f₂) ∘ₗ f₁₂) ⊗ₘ f₃) = (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ ⊗ₘ id) := by
  rw [← LinearMap.comp_assoc, map_map_comp_assoc_eq]
  ext
  rfl

@[coassoc_simps]
/-
**CoassocSimps.assoc_comp_map_map_comp_assoc** 是 Mathlib 中的一个引理，位于命名空间 `CoassocS
imps`。
形式化陈述：assoc_comp_map_map_comp_assoc (f₁ : M₁ ->ₗ[R] N₁) (f₂ : M₂ ->ₗ[R] N₂) (f₃ 
: M₃ ->ₗ[R] N₃) (f₁₂ : M ->ₗ[R] M₁ otimes[R] M₂) (f : M ->ₗ[R] M otimes[R] M₃) :
 α ∘ₗ (((f₁ otimesₘ f₂) ∘ₗ f₁₂) otimesₘ f₃) ∘ₗ f = (f₁ otimesₘ (f₂ otimesₘ f₃)) 
∘ₗ α ∘ₗ (f₁₂ otimesₘ id) ∘ₗ f
参数：f₁ : M₁ ->ₗ[R] N₁；f₂ : M₂ ->ₗ[R] N₂；f₃ : M₃ ->ₗ[R] N₃；f₁₂ : M ->ₗ[R] M₁ otime
s[R] M₂；f : M ->ₗ[R] M otimes[R] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `CoassocSimps.assoc_comp_map_map_comp`：assoc_comp_map_map_comp (f₁ : M₁ -
>ₗ[R] N₁) (f₂ : M₂ ->ₗ[R] N₂) (f₃ : M₃ ->ₗ[R] N₃) (f₁₂ : M ->ₗ[R] M₁ otimes[R] M
₂) : α ∘ₗ (((f₁ otimesₘ f₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma assoc_comp_map_map_comp_assoc
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f₁₂ : M →ₗ[R] M₁ ⊗[R] M₂)
    (f : M →ₗ[R] M ⊗[R] M₃) :
    α ∘ₗ (((f₁ ⊗ₘ f₂) ∘ₗ f₁₂) ⊗ₘ f₃) ∘ₗ f =
      (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ ⊗ₘ id) ∘ₗ f := by
  simp only [← LinearMap.comp_assoc, assoc_comp_map_map_comp]

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `f₃ ≠ id`.
/-
**CoassocSimps.assoc_comp_map** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`。
形式化陈述：assoc_comp_map (f₃ : M₃ ->ₗ[R] N₃) (f₁₂ : M ->ₗ[R] M₁ otimes[R] M₂) : α ∘ₗ
 (f₁₂ otimesₘ f₃) = (id otimesₘ (id otimesₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ otimesₘ id)
参数：f₃ : M₃ ->ₗ[R] N₃；f₁₂ : M ->ₗ[R] M₁ otimes[R] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用引理 `TensorProduct.map_map_comp_assoc_eq`：map_map_comp_assoc_eq (f : M ->ₗ[R]
 Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) : map f (map g h) ∘ₗ TensorProduct.assoc R
 M N P = TensorProduct.as…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.map_id`：map_id : map (id : M ->ₗ[R] M) (id : N ->ₗ[R] N) =
 .id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma assoc_comp_map (f₃ : M₃ →ₗ[R] N₃) (f₁₂ : M →ₗ[R] M₁ ⊗[R] M₂) :
    α ∘ₗ (f₁₂ ⊗ₘ f₃) = (id ⊗ₘ (id ⊗ₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ ⊗ₘ id) := by
  rw [← LinearMap.comp_assoc, map_map_comp_assoc_eq]
  simp only [coassoc_simps]

/-- Simproc version of `assoc_comp_map` that only fires when `f₃ ≠ id`. -/
simproc_decl assoc_comp_map_simproc
    ((TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ (_ ⊗ₘ _)) := .ofQ fun _ t e ↦ do
  let_expr LinearMap R _ _ _ _ T₁ T₂ _ _ _ _ ←  t
    | return .continue
  let_expr TensorProduct _ instR M M₃ instM instM₃ instRM instRM₃ ←  T₁
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ _ M₁ T₃ instM₁ _ instRM₁ _ ←  T₂
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ _ M₂ N₃ instM₂ instN₃ instRM₂ instRN₃ ←  T₃
    | return Lean.Meta.Simp.StepQ.continue
  let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
  let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
  let .succ u₃ := (← Lean.Meta.inferType M₁).sortLevel! | return .continue
  let .succ u₄ := (← Lean.Meta.inferType M₂).sortLevel! | return .continue
  let .succ u₅ := (← Lean.Meta.inferType M₃).sortLevel! | return .continue
  let .succ u₆ := (← Lean.Meta.inferType N₃).sortLevel! | return .continue
  have R  : Q(Type u₁) := R
  have M  : Q(Type u₂) := M
  have M₁ : Q(Type u₃) := M₁
  have M₂ : Q(Type u₄) := M₂
  have M₃ : Q(Type u₅) := M₃
  have N₃ : Q(Type u₆) := N₃
  have : Q(CommSemiring $R) := instR
  have : Q(AddCommMonoid $M) := instM
  have : Q(AddCommMonoid $M₁) := instM₁
  have : Q(AddCommMonoid $M₂) := instM₂
  have : Q(AddCommMonoid $M₃) := instM₃
  have : Q(AddCommMonoid $N₃) := instN₃
  have : Q(Module $R $M) := instRM
  have : Q(Module $R $M₁) := instRM₁
  have : Q(Module $R $M₂) := instRM₂
  have : Q(Module $R $M₃) := instRM₃
  have : Q(Module $R $N₃) := instRN₃
  have e : Q($M ⊗[$R] $M₃ →ₗ[$R] $M₁ ⊗[$R] ($M₂ ⊗[$R] $N₃)) := e
  match e with
  | ~q((TensorProduct.assoc «$R» «$M₁» «$M₂» «$N₃»).toLinearMap ∘ₗ ($f₁₂ ⊗ₘ $f₃)) =>
  match_expr f₃ with
  | LinearMap.id _ _ _ _ _ => return .continue
  | _ =>
  return .visit (e := e) <| .mk q((id ⊗ₘ (id ⊗ₘ $f₃)) ∘ₗ (TensorProduct.assoc _ _ _ _).toLinearMap
    ∘ₗ ($f₁₂ ⊗ₘ id)) (some q(assoc_comp_map ..))

attribute [coassoc_simps] assoc_comp_map_simproc

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `f₃ ≠ id`.
/-
**CoassocSimps.assoc_comp_map_assoc** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`。
形式化陈述：assoc_comp_map_assoc (f₃ : M₃ ->ₗ[R] N₃) (f₁₂ : M ->ₗ[R] M₁ otimes[R] M₂) 
(f : P ->ₗ[R] M otimes[R] M₃) : α ∘ₗ (f₁₂ otimesₘ f₃) ∘ₗ f = (id otimesₘ (id oti
mesₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ otimesₘ id) ∘ₗ f
参数：f₃ : M₃ ->ₗ[R] N₃；f₁₂ : M ->ₗ[R] M₁ otimes[R] M₂；f : P ->ₗ[R] M otimes[R] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `CoassocSimps.assoc_comp_map`：assoc_comp_map (f₃ : M₃ ->ₗ[R] N₃) (f₁₂ : M
 ->ₗ[R] M₁ otimes[R] M₂) : α ∘ₗ (f₁₂ otimesₘ f₃) = (id otimesₘ (id otimesₘ f₃)) 
∘ₗ α ∘ₗ (f₁₂ otim…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma assoc_comp_map_assoc (f₃ : M₃ →ₗ[R] N₃)
    (f₁₂ : M →ₗ[R] M₁ ⊗[R] M₂) (f : P →ₗ[R] M ⊗[R] M₃) :
    α ∘ₗ (f₁₂ ⊗ₘ f₃) ∘ₗ f = (id ⊗ₘ (id ⊗ₘ f₃)) ∘ₗ α ∘ₗ (f₁₂ ⊗ₘ id) ∘ₗ f := by
  rw [← LinearMap.comp_assoc]
  simp only [coassoc_simps]

/-- Simproc version of `assoc_comp_map_assoc` that only fires when `f₃ ≠ id`. -/
simproc_decl assoc_comp_map_assoc_simproc
    ((TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ (_ ⊗ₘ _) ∘ₗ _) := .ofQ fun _ _ e ↦ do
  let_expr LinearMap.comp R _ _ P _ T₂ _ _ _ instP _ _ instRP _ _ _ _ _ _ _ e' ←  e
    | return .continue
  let_expr LinearMap.comp _ _ _ _ T₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ←  e'
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ instR M M₃ instM instM₃ instRM instRM₃ ←  T₁
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ _ M₁ T₃ instM₁ _ instRM₁ _ ←  T₂
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ _ M₂ N₃ instM₂ instN₃ instRM₂ instRN₃ ←  T₃
    | return Lean.Meta.Simp.StepQ.continue
  let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
  let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
  let .succ u₃ := (← Lean.Meta.inferType M₁).sortLevel! | return .continue
  let .succ u₄ := (← Lean.Meta.inferType M₂).sortLevel! | return .continue
  let .succ u₅ := (← Lean.Meta.inferType M₃).sortLevel! | return .continue
  let .succ u₆ := (← Lean.Meta.inferType N₃).sortLevel! | return .continue
  let .succ u₇ := (← Lean.Meta.inferType P).sortLevel! | return .continue
  have R  : Q(Type u₁) := R
  have M  : Q(Type u₂) := M
  have M₁ : Q(Type u₃) := M₁
  have M₂ : Q(Type u₄) := M₂
  have M₃ : Q(Type u₅) := M₃
  have N₃ : Q(Type u₆) := N₃
  have P  : Q(Type u₇) := P
  have : Q(CommSemiring $R) := instR
  have : Q(AddCommMonoid $M) := instM
  have : Q(AddCommMonoid $M₁) := instM₁
  have : Q(AddCommMonoid $M₂) := instM₂
  have : Q(AddCommMonoid $M₃) := instM₃
  have : Q(AddCommMonoid $N₃) := instN₃
  have : Q(AddCommMonoid $P)  := instP
  have : Q(Module $R $M) := instRM
  have : Q(Module $R $M₁) := instRM₁
  have : Q(Module $R $M₂) := instRM₂
  have : Q(Module $R $M₃) := instRM₃
  have : Q(Module $R $N₃) := instRN₃
  have : Q(Module $R $P) := instRP
  have e : Q($P →ₗ[$R] $M₁ ⊗[$R] ($M₂ ⊗[$R] $N₃)) := e
  match e with
  | ~q((TensorProduct.assoc «$R» «$M₁» «$M₂» «$N₃»).toLinearMap ∘ₗ
      ($f₁₂ ⊗ₘ $f₃) ∘ₗ ($f : _ →ₗ[_] «$M» ⊗ «$M₃»)) =>
  match_expr f₃ with
  | LinearMap.id _ _ _ _ _ => return .continue
  | _ =>
  return .visit (e := e) <| .mk q((id ⊗ₘ (id ⊗ₘ $f₃)) ∘ₗ (TensorProduct.assoc _ _ _ _).toLinearMap
    ∘ₗ ($f₁₂ ⊗ₘ id) ∘ₗ $f) (some q(assoc_comp_map_assoc ..))

attribute [coassoc_simps] assoc_comp_map_assoc_simproc

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `f₁ ≠ id`.
/-
**CoassocSimps.assoc_symm_comp_map** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`。
形式化陈述：assoc_symm_comp_map (f₁ : M₁ ->ₗ[R] N₁) (f₂₃ : M ->ₗ[R] M₂ otimes[R] M₃) :
 α⁻¹ ∘ₗ (f₁ otimesₘ f₂₃) = ((f₁ otimesₘ .id) otimesₘ .id) ∘ₗ α⁻¹ ∘ₗ (.id otimesₘ
 f₂₃)
参数：f₁ : M₁ ->ₗ[R] N₁；f₂₃ : M ->ₗ[R] M₂ otimes[R] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用引理 `TensorProduct.map_map_comp_assoc_symm_eq`：map_map_comp_assoc_symm_eq (f 
: M ->ₗ[R] Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) : map (map f g) h ∘ₗ (TensorProd
uct.assoc R M N P).symm = (Ten…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `TensorProduct.map_id`：map_id : map (id : M ->ₗ[R] M) (id : N ->ₗ[R] N) =
 .id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma assoc_symm_comp_map
    (f₁ : M₁ →ₗ[R] N₁) (f₂₃ : M →ₗ[R] M₂ ⊗[R] M₃) :
    α⁻¹ ∘ₗ (f₁ ⊗ₘ f₂₃) = ((f₁ ⊗ₘ .id) ⊗ₘ .id) ∘ₗ α⁻¹ ∘ₗ (.id ⊗ₘ f₂₃) := by
  rw [← LinearMap.comp_assoc, map_map_comp_assoc_symm_eq]
  simp only [coassoc_simps]

/-- Simproc version of `assoc_symm_comp_map` that only fires when `f₁ ≠ id`. -/
simproc_decl assoc_symm_comp_map_simproc
    ((TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ (_ ⊗ₘ _)) := .ofQ fun _ t e ↦ do
  let_expr LinearMap R _ _ _ _ T₁ T₂ _ _ _ _ ←  t
    | return .continue
  let_expr TensorProduct _ instR M₁ M instM₁ instM instRM₁ instRM ←  T₁
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ _ T₃ M₃ _ instM₃ _ instRM₃ ←  T₂
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ _ N₁ M₂ instN₁ instM₂ instRN₁ instRM₂ ←  T₃
    | return Lean.Meta.Simp.StepQ.continue
  let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
  let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
  let .succ u₃ := (← Lean.Meta.inferType M₁).sortLevel! | return .continue
  let .succ u₄ := (← Lean.Meta.inferType M₂).sortLevel! | return .continue
  let .succ u₅ := (← Lean.Meta.inferType M₃).sortLevel! | return .continue
  let .succ u₆ := (← Lean.Meta.inferType N₁).sortLevel! | return .continue
  have R  : Q(Type u₁) := R
  have M  : Q(Type u₂) := M
  have M₁ : Q(Type u₃) := M₁
  have M₂ : Q(Type u₄) := M₂
  have M₃ : Q(Type u₅) := M₃
  have N₁ : Q(Type u₆) := N₁
  have : Q(CommSemiring $R) := instR
  have : Q(AddCommMonoid $M) := instM
  have : Q(AddCommMonoid $M₁) := instM₁
  have : Q(AddCommMonoid $M₂) := instM₂
  have : Q(AddCommMonoid $M₃) := instM₃
  have : Q(AddCommMonoid $N₁) := instN₁
  have : Q(Module $R $M) := instRM
  have : Q(Module $R $M₁) := instRM₁
  have : Q(Module $R $M₂) := instRM₂
  have : Q(Module $R $M₃) := instRM₃
  have : Q(Module $R $N₁) := instRN₁
  have e : Q($M₁ ⊗[$R] $M →ₗ[$R] $N₁ ⊗[$R] $M₂ ⊗[$R] $M₃) := e
  match e with
  | ~q((TensorProduct.assoc «$R» «$N₁» «$M₂» «$M₃»).symm.toLinearMap ∘ₗ ($f₁ ⊗ₘ $f₂₃)) =>
  match_expr f₁ with
  | LinearMap.id _ _ _ _ _ => return .continue
  | _ =>
  return .visit (e := e) <| .mk q((($f₁ ⊗ₘ id) ⊗ₘ id) ∘ₗ
    (TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ (id ⊗ₘ $f₂₃))
      (some q(assoc_symm_comp_map ..))

attribute [coassoc_simps] assoc_symm_comp_map_simproc

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `f₁ ≠ id`.
/-
**CoassocSimps.assoc_symm_comp_map_assoc** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps
`。
形式化陈述：assoc_symm_comp_map_assoc (f₁ : M₁ ->ₗ[R] N₁) (f₂₃ : M ->ₗ[R] M₂ otimes[R]
 M₃) (f : P ->ₗ[R] M₁ otimes[R] M) : α⁻¹ ∘ₗ (f₁ otimesₘ f₂₃) ∘ₗ f = ((f₁ otimesₘ
 .id) otimesₘ .id) ∘ₗ α⁻¹ ∘ₗ (.id otimesₘ f₂₃) ∘ₗ f
参数：f₁ : M₁ ->ₗ[R] N₁；f₂₃ : M ->ₗ[R] M₂ otimes[R] M₃；f : P ->ₗ[R] M₁ otimes[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `CoassocSimps.assoc_symm_comp_map`：assoc_symm_comp_map (f₁ : M₁ ->ₗ[R] N₁
) (f₂₃ : M ->ₗ[R] M₂ otimes[R] M₃) : α⁻¹ ∘ₗ (f₁ otimesₘ f₂₃) = ((f₁ otimesₘ .id)
 otimesₘ .id) ∘ₗ α⁻¹ ∘…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma assoc_symm_comp_map_assoc (f₁ : M₁ →ₗ[R] N₁)
    (f₂₃ : M →ₗ[R] M₂ ⊗[R] M₃) (f : P →ₗ[R] M₁ ⊗[R] M) :
    α⁻¹ ∘ₗ (f₁ ⊗ₘ f₂₃) ∘ₗ f = ((f₁ ⊗ₘ .id) ⊗ₘ .id) ∘ₗ α⁻¹ ∘ₗ (.id ⊗ₘ f₂₃) ∘ₗ f := by
  rw [← LinearMap.comp_assoc]
  simp only [coassoc_simps]

/-- Simproc version of `assoc_symm_comp_map_assoc` that only fires when `f₁ ≠ id`. -/
simproc_decl assoc_symm_comp_map_assoc_simproc
    ((TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ (_ ⊗ₘ _) ∘ₗ _) := .ofQ fun _ _ e ↦ do
  let_expr LinearMap.comp R _ _ P _ T₂ _ _ _ instP _ _ instRP _ _ _ _ _ _ _ e' ← e
    | return .continue
  let_expr LinearMap.comp _ _ _ _ T₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ←  e'
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ instR M₁ M instM₁ instM instRM₁ instRM ←  T₁
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ _ T₃ M₃ _ instM₃ _ instRM₃ ←  T₂
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ _ N₁ M₂ instN₁ instM₂ instRN₁ instRM₂ ←  T₃
    | return Lean.Meta.Simp.StepQ.continue
  let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
  let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
  let .succ u₃ := (← Lean.Meta.inferType M₁).sortLevel! | return .continue
  let .succ u₄ := (← Lean.Meta.inferType M₂).sortLevel! | return .continue
  let .succ u₅ := (← Lean.Meta.inferType M₃).sortLevel! | return .continue
  let .succ u₆ := (← Lean.Meta.inferType N₁).sortLevel! | return .continue
  let .succ u₇ := (← Lean.Meta.inferType P).sortLevel! | return .continue
  have R  : Q(Type u₁) := R
  have M  : Q(Type u₂) := M
  have M₁ : Q(Type u₃) := M₁
  have M₂ : Q(Type u₄) := M₂
  have M₃ : Q(Type u₅) := M₃
  have N₁ : Q(Type u₆) := N₁
  have P  : Q(Type u₇) := P
  have : Q(CommSemiring $R) := instR
  have : Q(AddCommMonoid $M) := instM
  have : Q(AddCommMonoid $M₁) := instM₁
  have : Q(AddCommMonoid $M₂) := instM₂
  have : Q(AddCommMonoid $M₃) := instM₃
  have : Q(AddCommMonoid $N₁) := instN₁
  have : Q(AddCommMonoid $P)  := instP
  have : Q(Module $R $M) := instRM
  have : Q(Module $R $M₁) := instRM₁
  have : Q(Module $R $M₂) := instRM₂
  have : Q(Module $R $M₃) := instRM₃
  have : Q(Module $R $N₁) := instRN₁
  have : Q(Module $R $P) := instRP
  have e : Q($P →ₗ[$R] $N₁ ⊗[$R] $M₂ ⊗[$R] $M₃) := e
  match e with
  | ~q((TensorProduct.assoc «$R» «$N₁» «$M₂» «$M₃»).symm.toLinearMap ∘ₗ
      ($f₁ ⊗ₘ $f₂₃) ∘ₗ ($f : _ →ₗ[_] «$M₁» ⊗ «$M»)) =>
  match_expr f₁ with
  | LinearMap.id _ _ _ _ _ => return .continue
  | _ =>
  return .visit (e := e) <| .mk q((($f₁ ⊗ₘ id) ⊗ₘ id) ∘ₗ
    (TensorProduct.assoc _ _ _ _).symm.toLinearMap ∘ₗ (id ⊗ₘ $f₂₃) ∘ₗ $f)
      (some q(assoc_symm_comp_map_assoc ..))

attribute [coassoc_simps] assoc_symm_comp_map_assoc_simproc

@[coassoc_simps]
/-
**CoassocSimps.assoc_symm_comp_map_map_comp** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSi
mps`。
形式化陈述：assoc_symm_comp_map_map_comp (f₁ : M₁ ->ₗ[R] N₁) (f₂ : M₂ ->ₗ[R] N₂) (f₃ :
 M₃ ->ₗ[R] N₃) (f₂₃ : M ->ₗ[R] M₂ otimes[R] M₃) : α⁻¹ ∘ₗ (f₁ otimesₘ (f₂ otimesₘ
 f₃ ∘ₗ f₂₃)) = ((f₁ otimesₘ f₂) otimesₘ f₃) ∘ₗ α⁻¹ ∘ₗ (id otimesₘ f₂₃)
参数：f₁ : M₁ ->ₗ[R] N₁；f₂ : M₂ ->ₗ[R] N₂；f₃ : M₃ ->ₗ[R] N₃；f₂₃ : M ->ₗ[R] M₂ otime
s[R] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用引理 `TensorProduct.map_map_comp_assoc_symm_eq`：map_map_comp_assoc_symm_eq (f 
: M ->ₗ[R] Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) : map (map f g) h ∘ₗ (TensorProd
uct.assoc R M N P).symm = (Ten…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma assoc_symm_comp_map_map_comp
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f₂₃ : M →ₗ[R] M₂ ⊗[R] M₃) :
    α⁻¹ ∘ₗ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃ ∘ₗ f₂₃)) = ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ∘ₗ α⁻¹ ∘ₗ (id ⊗ₘ f₂₃) := by
  rw [← LinearMap.comp_assoc, map_map_comp_assoc_symm_eq]
  ext
  rfl

@[coassoc_simps]
/-
**CoassocSimps.assoc_symm_comp_map_map_comp_assoc** 是 Mathlib 中的一个引理，位于命名空间 `Coa
ssocSimps`。
形式化陈述：assoc_symm_comp_map_map_comp_assoc (f₁ : M₁ ->ₗ[R] N₁) (f₂ : M₂ ->ₗ[R] N₂)
 (f₃ : M₃ ->ₗ[R] N₃) (f₂₃ : M ->ₗ[R] M₂ otimes[R] M₃) (f : N ->ₗ[R] M₁ otimes[R]
 M) : α⁻¹ ∘ₗ (f₁ otimesₘ (f₂ otimesₘ f₃ ∘ₗ f₂₃)) ∘ₗ f = ((f₁ otimesₘ f₂) otimesₘ
 f₃) ∘ₗ α⁻¹ ∘ₗ (id otimesₘ f₂₃) ∘ₗ f
参数：f₁ : M₁ ->ₗ[R] N₁；f₂ : M₂ ->ₗ[R] N₂；f₃ : M₃ ->ₗ[R] N₃；f₂₃ : M ->ₗ[R] M₂ otime
s[R] M₃；f : N ->ₗ[R] M₁ otimes[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `CoassocSimps.assoc_symm_comp_map_map_comp`：assoc_symm_comp_map_map_comp 
(f₁ : M₁ ->ₗ[R] N₁) (f₂ : M₂ ->ₗ[R] N₂) (f₃ : M₃ ->ₗ[R] N₃) (f₂₃ : M ->ₗ[R] M₂ o
times[R] M₃) : α⁻¹ ∘ₗ (f₁ otime…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma assoc_symm_comp_map_map_comp_assoc
    (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂) (f₃ : M₃ →ₗ[R] N₃) (f₂₃ : M →ₗ[R] M₂ ⊗[R] M₃)
    (f : N →ₗ[R] M₁ ⊗[R] M) :
    α⁻¹ ∘ₗ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃ ∘ₗ f₂₃)) ∘ₗ f = ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ∘ₗ α⁻¹ ∘ₗ (id ⊗ₘ f₂₃) ∘ₗ f := by
  simp only [← LinearMap.comp_assoc, assoc_symm_comp_map_map_comp]

@[coassoc_simps]
/-
**CoassocSimps.assoc_symm_comp_lid_symm** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`
。
形式化陈述：assoc_symm_comp_lid_symm : (α⁻¹ ∘ₗ fun⁻¹ : M otimes[R] N ->ₗ[R] _) = fun⁻¹
 otimesₘ id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma assoc_symm_comp_lid_symm :
    (α⁻¹ ∘ₗ λ⁻¹ : M ⊗[R] N →ₗ[R] _) = λ⁻¹ ⊗ₘ id := rfl

@[coassoc_simps]
/-
**CoassocSimps.assoc_symm_comp_lid_symm_assoc** 是 Mathlib 中的一个引理，位于命名空间 `Coassoc
Simps`。
形式化陈述：assoc_symm_comp_lid_symm_assoc (f : P ->ₗ[R] M otimes[R] N) : α⁻¹ ∘ₗ fun⁻¹
 ∘ₗ f = fun⁻¹ otimesₘ id ∘ₗ f
参数：f : P ->ₗ[R] M otimes[R] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma assoc_symm_comp_lid_symm_assoc (f : P →ₗ[R] M ⊗[R] N) :
    α⁻¹ ∘ₗ λ⁻¹ ∘ₗ f = λ⁻¹ ⊗ₘ id ∘ₗ f := rfl

@[coassoc_simps]
/-
**CoassocSimps.assoc_symm_comp_map_lid_symm** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSi
mps`。
形式化陈述：assoc_symm_comp_map_lid_symm (f : M ->ₗ[R] M') : α⁻¹ ∘ₗ f otimesₘ fun⁻¹ = 
(f otimesₘ id ∘ₗ ρ⁻¹) otimesₘ id (M
参数：f : M ->ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma assoc_symm_comp_map_lid_symm (f : M →ₗ[R] M') :
    α⁻¹ ∘ₗ f ⊗ₘ λ⁻¹ = (f ⊗ₘ id ∘ₗ ρ⁻¹) ⊗ₘ id (M := N) := by
  ext; rfl

@[coassoc_simps]
/-
**CoassocSimps.assoc_symm_comp_map_lid_symm_assoc** 是 Mathlib 中的一个引理，位于命名空间 `Coa
ssocSimps`。
形式化陈述：assoc_symm_comp_map_lid_symm_assoc (f : M ->ₗ[R] M') (g : P ->ₗ[R] M otime
s[R] N) : α⁻¹ ∘ₗ f otimesₘ fun⁻¹ ∘ₗ g = (f otimesₘ id ∘ₗ ρ⁻¹) otimesₘ id ∘ₗ g
参数：f : M ->ₗ[R] M'；g : P ->ₗ[R] M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma assoc_symm_comp_map_lid_symm_assoc (f : M →ₗ[R] M') (g : P →ₗ[R] M ⊗[R] N) :
    α⁻¹ ∘ₗ f ⊗ₘ λ⁻¹ ∘ₗ g = (f ⊗ₘ id ∘ₗ ρ⁻¹) ⊗ₘ id ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, ← assoc_symm_comp_map_lid_symm]

@[coassoc_simps]
/-
**CoassocSimps.assoc_symm_comp_map_rid_symm** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSi
mps`。
形式化陈述：assoc_symm_comp_map_rid_symm (f : M ->ₗ[R] M') : α⁻¹ ∘ₗ f otimesₘ ρ⁻¹ = (f
 otimesₘ id (M
参数：f : M ->ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma assoc_symm_comp_map_rid_symm (f : M →ₗ[R] M') :
    α⁻¹ ∘ₗ f ⊗ₘ ρ⁻¹ = (f ⊗ₘ id (M := N)) ⊗ₘ id ∘ₗ ρ⁻¹ := by
  ext; rfl

@[coassoc_simps]
/-
**CoassocSimps.assoc_symm_comp_map_rid_symm_assoc** 是 Mathlib 中的一个引理，位于命名空间 `Coa
ssocSimps`。
形式化陈述：assoc_symm_comp_map_rid_symm_assoc (f : M ->ₗ[R] M') (g : P ->ₗ[R] M otime
s[R] N) : α⁻¹ ∘ₗ f otimesₘ ρ⁻¹ ∘ₗ g = (f otimesₘ id) otimesₘ id ∘ₗ ρ⁻¹ ∘ₗ g
参数：f : M ->ₗ[R] M'；g : P ->ₗ[R] M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma assoc_symm_comp_map_rid_symm_assoc (f : M →ₗ[R] M') (g : P →ₗ[R] M ⊗[R] N) :
    α⁻¹ ∘ₗ f ⊗ₘ ρ⁻¹ ∘ₗ g = (f ⊗ₘ id) ⊗ₘ id ∘ₗ ρ⁻¹ ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, ← assoc_symm_comp_map_rid_symm]

@[coassoc_simps]
/-
**CoassocSimps.assoc_comp_rid_symm** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`。
形式化陈述：assoc_comp_rid_symm : (α ∘ₗ ρ⁻¹ : M otimes[R] N ->ₗ[R] _) = id otimesₘ ρ⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma assoc_comp_rid_symm :
    (α ∘ₗ ρ⁻¹ : M ⊗[R] N →ₗ[R] _) = id ⊗ₘ ρ⁻¹ := by ext; rfl

@[coassoc_simps]
/-
**CoassocSimps.assoc_comp_rid_symm_assoc** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps
`。
形式化陈述：assoc_comp_rid_symm_assoc (f : P ->ₗ[R] M otimes[R] N) : α ∘ₗ ρ⁻¹ ∘ₗ f = i
d otimesₘ ρ⁻¹ ∘ₗ f
参数：f : P ->ₗ[R] M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma assoc_comp_rid_symm_assoc (f : P →ₗ[R] M ⊗[R] N) :
    α ∘ₗ ρ⁻¹ ∘ₗ f = id ⊗ₘ ρ⁻¹ ∘ₗ f := by
  simp_rw [← assoc_comp_rid_symm, LinearMap.comp_assoc]

@[coassoc_simps]
/-
**CoassocSimps.assoc_comp_map_lid_symm** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`。
形式化陈述：assoc_comp_map_lid_symm (f : N ->ₗ[R] N') : α ∘ₗ fun⁻¹ otimesₘ f = (id oti
mesₘ (id (M
参数：f : N ->ₗ[R] N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma assoc_comp_map_lid_symm (f : N →ₗ[R] N') :
    α ∘ₗ λ⁻¹ ⊗ₘ f = (id ⊗ₘ (id (M := M) ⊗ₘ f)) ∘ₗ λ⁻¹ := by
  ext; rfl

@[coassoc_simps]
/-
**CoassocSimps.assoc_comp_map_lid_symm_assoc** 是 Mathlib 中的一个引理，位于命名空间 `CoassocS
imps`。
形式化陈述：assoc_comp_map_lid_symm_assoc (f : N ->ₗ[R] N') (g : P ->ₗ[R] M otimes[R] 
N) : α ∘ₗ fun⁻¹ otimesₘ f ∘ₗ g = (id otimesₘ (id otimesₘ f)) ∘ₗ fun⁻¹ ∘ₗ g
参数：f : N ->ₗ[R] N'；g : P ->ₗ[R] M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma assoc_comp_map_lid_symm_assoc (f : N →ₗ[R] N') (g : P →ₗ[R] M ⊗[R] N) :
    α ∘ₗ λ⁻¹ ⊗ₘ f ∘ₗ g = (id ⊗ₘ (id ⊗ₘ f)) ∘ₗ λ⁻¹ ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, ← assoc_comp_map_lid_symm]

@[coassoc_simps]
/-
**CoassocSimps.assoc_comp_map_rid_symm** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`。
形式化陈述：assoc_comp_map_rid_symm (f : N ->ₗ[R] N') : α ∘ₗ ρ⁻¹ otimesₘ f = id (M
参数：f : N ->ₗ[R] N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma assoc_comp_map_rid_symm (f : N →ₗ[R] N') :
    α ∘ₗ ρ⁻¹ ⊗ₘ f = id (M := M) ⊗ₘ ((id ⊗ₘ f) ∘ₗ λ⁻¹) := by
  ext; rfl

@[coassoc_simps]
/-
**CoassocSimps.assoc_comp_map_rid_symm_assoc** 是 Mathlib 中的一个引理，位于命名空间 `CoassocS
imps`。
形式化陈述：assoc_comp_map_rid_symm_assoc (f : N ->ₗ[R] N') (g : P ->ₗ[R] M otimes[R] 
N) : α ∘ₗ ρ⁻¹ otimesₘ f ∘ₗ g = id otimesₘ ((id otimesₘ f) ∘ₗ fun⁻¹) ∘ₗ g
参数：f : N ->ₗ[R] N'；g : P ->ₗ[R] M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma assoc_comp_map_rid_symm_assoc (f : N →ₗ[R] N') (g : P →ₗ[R] M ⊗[R] N) :
    α ∘ₗ ρ⁻¹ ⊗ₘ f ∘ₗ g = id ⊗ₘ ((id ⊗ₘ f) ∘ₗ λ⁻¹) ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, ← assoc_comp_map_rid_symm]

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `g ≠ id`.
/-
**CoassocSimps.lid_comp_map** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`。
形式化陈述：lid_comp_map (f : M ->ₗ[R] R) (g : N ->ₗ[R] M') : fun ∘ₗ (f otimesₘ g) = g
 ∘ₗ fun ∘ₗ (f otimesₘ id)
参数：f : M ->ₗ[R] R；g : N ->ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
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
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lid_comp_map (f : M →ₗ[R] R) (g : N →ₗ[R] M') :
    λ ∘ₗ (f ⊗ₘ g) = g ∘ₗ λ ∘ₗ (f ⊗ₘ id) := by
  ext; simp

/-- Simproc version of `lid_comp_map` that only fires when `g ≠ id`. -/
simproc_decl lid_comp_map_simproc
    ((TensorProduct.lid _ _).toLinearMap ∘ₗ (_ ⊗ₘ _)) := .ofQ fun _ t e ↦ do
  let_expr LinearMap R _ _ _ _ T₁ M' _ instM' _ instRM' ←  t
    | return .continue
  let_expr TensorProduct _ instR M N instM instN instRM instRN ←  T₁
    | return Lean.Meta.Simp.StepQ.continue
  let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
  let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
  let .succ u₃ := (← Lean.Meta.inferType M').sortLevel! | return .continue
  let .succ u₄ := (← Lean.Meta.inferType N).sortLevel! | return .continue
  have R  : Q(Type u₁) := R
  have M  : Q(Type u₂) := M
  have M' : Q(Type u₃) := M'
  have N  : Q(Type u₄) := N
  have : Q(CommSemiring $R)   := instR
  have : Q(AddCommMonoid $M)  := instM
  have : Q(AddCommMonoid $M') := instM'
  have : Q(AddCommMonoid $N)  := instN
  have : Q(Module $R $M)  := instRM
  have : Q(Module $R $M') := instRM'
  have : Q(Module $R $N)  := instRN
  have e : Q($M ⊗[$R] $N →ₗ[$R] $M') := e
  match e with
  | ~q((TensorProduct.lid «$R» «$M'»).toLinearMap ∘ₗ ($f ⊗ₘ $g)) =>
  match_expr g with
  | LinearMap.id _ _ _ _ _ => return .continue
  | _ =>
  return .visit (e := e) <| .mk q($g ∘ₗ (TensorProduct.lid $R _).toLinearMap ∘ₗ ($f ⊗ₘ .id))
    (some q(lid_comp_map ..))

attribute [coassoc_simps] lid_comp_map_simproc

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `g ≠ id`.
/-
**CoassocSimps.lid_comp_map_assoc** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`。
形式化陈述：lid_comp_map_assoc (f : M ->ₗ[R] R) (g : N ->ₗ[R] M') (h : P ->ₗ[R] M otim
es[R] N) : fun ∘ₗ (f otimesₘ g) ∘ₗ h = g ∘ₗ fun ∘ₗ (f otimesₘ id) ∘ₗ h
参数：f : M ->ₗ[R] R；g : N ->ₗ[R] M'；h : P ->ₗ[R] M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `CoassocSimps.lid_comp_map`：lid_comp_map (f : M ->ₗ[R] R) (g : N ->ₗ[R] M
') : fun ∘ₗ (f otimesₘ g) = g ∘ₗ fun ∘ₗ (f otimesₘ id)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lid_comp_map_assoc (f : M →ₗ[R] R) (g : N →ₗ[R] M') (h : P →ₗ[R] M ⊗[R] N) :
    λ ∘ₗ (f ⊗ₘ g) ∘ₗ h = g ∘ₗ λ ∘ₗ (f ⊗ₘ id) ∘ₗ h := by
  simp only [← LinearMap.comp_assoc, lid_comp_map _ g]

/-- Simproc version of `lid_comp_map_assoc` that only fires when `g ≠ id`. -/
simproc_decl lid_comp_map_assoc_simproc
    ((TensorProduct.lid _ _).toLinearMap ∘ₗ (_ ⊗ₘ _) ∘ₗ _) := .ofQ fun _ _ e ↦ do
  let_expr LinearMap.comp R _ _ P _ M' _ _ _ instP _ instM' instRP _ instRM' _ _ _ _ _ e' ← e
    | return .continue
  let_expr LinearMap.comp _ _ _ _ T₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ← e'
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ instR M N instM instN instRM instRN ← T₁
    | return Lean.Meta.Simp.StepQ.continue
  let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
  let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
  let .succ u₃ := (← Lean.Meta.inferType M').sortLevel! | return .continue
  let .succ u₄ := (← Lean.Meta.inferType N).sortLevel! | return .continue
  let .succ u₅ := (← Lean.Meta.inferType P).sortLevel! | return .continue
  have R  : Q(Type u₁) := R
  have M  : Q(Type u₂) := M
  have M' : Q(Type u₃) := M'
  have N  : Q(Type u₄) := N
  have P  : Q(Type u₅) := P
  have : Q(CommSemiring $R)   := instR
  have : Q(AddCommMonoid $M)  := instM
  have : Q(AddCommMonoid $M') := instM'
  have : Q(AddCommMonoid $N)  := instN
  have : Q(AddCommMonoid $P)  := instP
  have : Q(Module $R $M)  := instRM
  have : Q(Module $R $M') := instRM'
  have : Q(Module $R $N)  := instRN
  have : Q(Module $R $P)  := instRP
  have e : Q($P →ₗ[$R] $M') := e
  match e with
  | ~q((TensorProduct.lid «$R» «$M'»).toLinearMap ∘ₗ ($f ⊗ₘ $g) ∘ₗ
      ($h : «$P» →ₗ[«$R»] «$M» ⊗[«$R»] «$N»)) =>
  match_expr g with
  | LinearMap.id _ _ _ _ _ => return .continue
  | _ =>
  return .visit (e := e) <| .mk q($g ∘ₗ (TensorProduct.lid $R _).toLinearMap ∘ₗ ($f ⊗ₘ .id) ∘ₗ $h)
    (some q(lid_comp_map_assoc ..))

attribute [coassoc_simps] lid_comp_map_assoc_simproc

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `f ≠ id`.
/-
**CoassocSimps.rid_comp_map** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`。
形式化陈述：rid_comp_map (f : M ->ₗ[R] M') (g : N ->ₗ[R] R) : ρ ∘ₗ (f otimesₘ g) = f ∘
ₗ ρ ∘ₗ (.id otimesₘ g)
参数：f : M ->ₗ[R] M'；g : N ->ₗ[R] R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
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
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rid_comp_map (f : M →ₗ[R] M') (g : N →ₗ[R] R) :
    ρ ∘ₗ (f ⊗ₘ g) = f ∘ₗ ρ ∘ₗ (.id ⊗ₘ g) := by
  ext; simp

/-- Simproc version of `rid_comp_map` that only fires when `g ≠ id`. -/
simproc_decl rid_comp_map_simproc
    ((TensorProduct.rid _ _).toLinearMap ∘ₗ (_ ⊗ₘ _)) := .ofQ fun _ t e ↦ do
  let_expr LinearMap R _ _ _ _ T₁ M' _ instM' _ instRM' ← t
    | return .continue
  let_expr TensorProduct _ instR M N instM instN instRM instRN ← T₁
    | return Lean.Meta.Simp.StepQ.continue
  let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
  let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
  let .succ u₃ := (← Lean.Meta.inferType M').sortLevel! | return .continue
  let .succ u₄ := (← Lean.Meta.inferType N).sortLevel! | return .continue
  have R  : Q(Type u₁) := R
  have M  : Q(Type u₂) := M
  have M' : Q(Type u₃) := M'
  have N  : Q(Type u₄) := N
  have : Q(CommSemiring $R)   := instR
  have : Q(AddCommMonoid $M)  := instM
  have : Q(AddCommMonoid $M') := instM'
  have : Q(AddCommMonoid $N)  := instN
  have : Q(Module $R $M)  := instRM
  have : Q(Module $R $M') := instRM'
  have : Q(Module $R $N)  := instRN
  have e : Q($M ⊗[$R] $N →ₗ[$R] $M') := e
  match e with
  | ~q((TensorProduct.rid «$R» «$M'»).toLinearMap ∘ₗ ($f ⊗ₘ $g)) =>
  match_expr f with
  | LinearMap.id _ _ _ _ _ => return .continue
  | _ =>
  return .visit (e := e) <| .mk q($f ∘ₗ (TensorProduct.rid $R _).toLinearMap ∘ₗ (.id ⊗ₘ $g))
    (some q(rid_comp_map ..))

attribute [coassoc_simps] rid_comp_map_simproc

-- This loops when tagged as a simp lemma,
-- so we turn it into a simproc that only fires when `f ≠ id`.
/-
**CoassocSimps.rid_comp_map_assoc** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`。
形式化陈述：rid_comp_map_assoc (f : M ->ₗ[R] M') (g : N ->ₗ[R] R) (h : P ->ₗ[R] M otim
es[R] N) : ρ ∘ₗ (f otimesₘ g) ∘ₗ h = f ∘ₗ ρ ∘ₗ (.id otimesₘ g) ∘ₗ h
参数：f : M ->ₗ[R] M'；g : N ->ₗ[R] R；h : P ->ₗ[R] M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `CoassocSimps.rid_comp_map`：rid_comp_map (f : M ->ₗ[R] M') (g : N ->ₗ[R] 
R) : ρ ∘ₗ (f otimesₘ g) = f ∘ₗ ρ ∘ₗ (.id otimesₘ g)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rid_comp_map_assoc (f : M →ₗ[R] M') (g : N →ₗ[R] R) (h : P →ₗ[R] M ⊗[R] N) :
    ρ ∘ₗ (f ⊗ₘ g) ∘ₗ h = f ∘ₗ ρ ∘ₗ (.id ⊗ₘ g) ∘ₗ h := by
  simp only [← LinearMap.comp_assoc, rid_comp_map f]

/-- Simproc version of `rid_comp_map_assoc` that only fires when `f ≠ id`. -/
simproc_decl rid_comp_map_assoc_simproc
    ((TensorProduct.rid _ _).toLinearMap ∘ₗ (_ ⊗ₘ _) ∘ₗ _) := .ofQ fun _ _ e ↦ do
  let_expr LinearMap.comp R _ _ P _ M' _ _ _ instP _ instM' instRP _ instRM' _ _ _ _ _ e' ← e
    | return Lean.Meta.Simp.StepQ.continue
  let_expr LinearMap.comp _ _ _ _ T₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ← e'
    | return Lean.Meta.Simp.StepQ.continue
  let_expr TensorProduct _ instR M N instM instN instRM instRN ← T₁
    | return Lean.Meta.Simp.StepQ.continue
  let .succ u₁ := (← Lean.Meta.inferType R).sortLevel! | return .continue
  let .succ u₂ := (← Lean.Meta.inferType M).sortLevel! | return .continue
  let .succ u₃ := (← Lean.Meta.inferType M').sortLevel! | return .continue
  let .succ u₄ := (← Lean.Meta.inferType N).sortLevel! | return .continue
  let .succ u₅ := (← Lean.Meta.inferType P).sortLevel! | return .continue
  have R  : Q(Type u₁) := R
  have M  : Q(Type u₂) := M
  have M' : Q(Type u₃) := M'
  have N  : Q(Type u₄) := N
  have P  : Q(Type u₅) := P
  have : Q(CommSemiring $R)   := instR
  have : Q(AddCommMonoid $M)  := instM
  have : Q(AddCommMonoid $M') := instM'
  have : Q(AddCommMonoid $N)  := instN
  have : Q(AddCommMonoid $P)  := instP
  have : Q(Module $R $M)  := instRM
  have : Q(Module $R $M') := instRM'
  have : Q(Module $R $N)  := instRN
  have : Q(Module $R $P)  := instRP
  have e : Q($P →ₗ[$R] $M') := e
  match e with
  | ~q((TensorProduct.rid «$R» «$M'»).toLinearMap ∘ₗ ($f ⊗ₘ $g) ∘ₗ
      ($h : «$P» →ₗ[«$R»] «$M» ⊗[«$R»] «$N»)) =>
  match_expr f with
  | LinearMap.id _ _ _ _ _ => return .continue
  | _ =>
  return .visit (e := e) <| .mk q($f ∘ₗ (TensorProduct.rid $R _).toLinearMap ∘ₗ (.id ⊗ₘ $g) ∘ₗ $h)
    (some q(rid_comp_map_assoc ..))

attribute [coassoc_simps] rid_comp_map_assoc_simproc

@[coassoc_simps]
/-
**CoassocSimps.lid_symm_comp** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`。
形式化陈述：lid_symm_comp (f : M ->ₗ[R] M') : fun⁻¹ ∘ₗ f = (id otimesₘ f) ∘ₗ fun⁻¹
参数：f : M ->ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
lemma lid_symm_comp (f : M →ₗ[R] M') :
    λ⁻¹ ∘ₗ f = (id ⊗ₘ f) ∘ₗ λ⁻¹ := by
  ext; rfl

@[coassoc_simps]
/-
**CoassocSimps.rid_symm_comp** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`。
形式化陈述：rid_symm_comp (f : M ->ₗ[R] M') : ρ⁻¹ ∘ₗ f = (f otimesₘ id) ∘ₗ ρ⁻¹
参数：f : M ->ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
lemma rid_symm_comp (f : M →ₗ[R] M') :
    ρ⁻¹ ∘ₗ f = (f ⊗ₘ id) ∘ₗ ρ⁻¹ := by
  ext; rfl

@[coassoc_simps]
/-
**CoassocSimps.symm_comp_lid_symm** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`。
形式化陈述：symm_comp_lid_symm : (β ∘ₗ fun⁻¹ : M ->ₗ[R] _) = ρ⁻¹
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_comp_lid_symm :
    (β ∘ₗ λ⁻¹ : M →ₗ[R] _) = ρ⁻¹ := rfl

@[coassoc_simps]
/-
**CoassocSimps.symm_comp_lid_symm_assoc** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`
。
形式化陈述：symm_comp_lid_symm_assoc (f : M ->ₗ[R] M') : β ∘ₗ fun⁻¹ ∘ₗ f = ρ⁻¹ ∘ₗ f
参数：f : M ->ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_comp_lid_symm_assoc (f : M →ₗ[R] M') :
    β ∘ₗ λ⁻¹ ∘ₗ f = ρ⁻¹ ∘ₗ f := rfl

@[coassoc_simps]
/-
**CoassocSimps.symm_comp_rid_symm** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`。
形式化陈述：symm_comp_rid_symm : (β ∘ₗ ρ⁻¹ : M ->ₗ[R] _) = fun⁻¹
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_comp_rid_symm :
    (β ∘ₗ ρ⁻¹ : M →ₗ[R] _) = λ⁻¹ := rfl

@[coassoc_simps]
/-
**CoassocSimps.symm_comp_rid_symm_assoc** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`
。
形式化陈述：symm_comp_rid_symm_assoc (f : M ->ₗ[R] M') : β ∘ₗ ρ⁻¹ ∘ₗ f = fun⁻¹ ∘ₗ f
参数：f : M ->ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_comp_rid_symm_assoc (f : M →ₗ[R] M') :
    β ∘ₗ ρ⁻¹ ∘ₗ f = λ⁻¹ ∘ₗ f := rfl

@[coassoc_simps]
/-
**CoassocSimps.symm_comp_map** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`。
形式化陈述：symm_comp_map (f : M ->ₗ[R] M') (g : N ->ₗ[R] N') : β ∘ₗ (f otimesₘ g) = (
g otimesₘ f) ∘ₗ β
参数：f : M ->ₗ[R] M'；g : N ->ₗ[R] N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
-/
lemma symm_comp_map (f : M →ₗ[R] M') (g : N →ₗ[R] N') :
    β ∘ₗ (f ⊗ₘ g) = (g ⊗ₘ f) ∘ₗ β := by ext; rfl

@[coassoc_simps]
/-
**CoassocSimps.symm_comp_map_assoc** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`。
形式化陈述：symm_comp_map_assoc (f : M ->ₗ[R] M') (g : N ->ₗ[R] N') (h : P ->ₗ[R] M ot
imes[R] N) : β ∘ₗ (f otimesₘ g) ∘ₗ h = (g otimesₘ f) ∘ₗ β ∘ₗ h
参数：f : M ->ₗ[R] M'；g : N ->ₗ[R] N'；h : P ->ₗ[R] M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `CoassocSimps.symm_comp_map`：symm_comp_map (f : M ->ₗ[R] M') (g : N ->ₗ[R
] N') : β ∘ₗ (f otimesₘ g) = (g otimesₘ f) ∘ₗ β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma symm_comp_map_assoc (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] M ⊗[R] N) :
    β ∘ₗ (f ⊗ₘ g) ∘ₗ h = (g ⊗ₘ f) ∘ₗ β ∘ₗ h := by
  simp only [← LinearMap.comp_assoc, symm_comp_map]

@[coassoc_simps]
/-
**CoassocSimps.coassoc_left** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`。
形式化陈述：coassoc_left [Coalgebra R M] (f : M ->ₗ[R] M') : α ∘ₗ (δ otimesₘ f) ∘ₗ δ =
 (id otimesₘ (id otimesₘ f)) ∘ₗ (id otimesₘ δ) ∘ₗ δ
参数：f : M ->ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `TensorProduct.map_map_comp_assoc_eq`：map_map_comp_assoc_eq (f : M ->ₗ[R]
 Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) : map f (map g h) ∘ₗ TensorProduct.assoc R
 M N P = TensorProduct.as…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CoassocSimps.assoc_comp_map`：assoc_comp_map (f₃ : M₃ ->ₗ[R] N₃) (f₁₂ : M
 ->ₗ[R] M₁ otimes[R] M₂) : α ∘ₗ (f₁₂ otimesₘ f₃) = (id otimesₘ (id otimesₘ f₃)) 
∘ₗ α ∘ₗ (f₁₂ otim…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.map_id`：map_id : map (id : M ->ₗ[R] M) (id : N ->ₗ[R] N) =
 .id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coassoc_left [Coalgebra R M] (f : M →ₗ[R] M') :
    α ∘ₗ (δ ⊗ₘ f) ∘ₗ δ = (id ⊗ₘ (id ⊗ₘ f)) ∘ₗ (id ⊗ₘ δ) ∘ₗ δ := by
  simp_rw [← LinearMap.lTensor_def, ← coassoc, ← LinearMap.comp_assoc, LinearMap.lTensor_def,
    map_map_comp_assoc_eq]
  simp only [coassoc_simps]

@[coassoc_simps]
/-
**CoassocSimps.coassoc_left_assoc** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`。
形式化陈述：coassoc_left_assoc [Coalgebra R M] (f : M ->ₗ[R] M') (g : N ->ₗ[R] M) : α 
∘ₗ (δ otimesₘ f) ∘ₗ δ ∘ₗ g = (id otimesₘ (id otimesₘ f)) ∘ₗ (id otimesₘ δ) ∘ₗ δ 
∘ₗ g
参数：f : M ->ₗ[R] M'；g : N ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `CoassocSimps.assoc_comp_map`：assoc_comp_map (f₃ : M₃ ->ₗ[R] N₃) (f₁₂ : M
 ->ₗ[R] M₁ otimes[R] M₂) : α ∘ₗ (f₁₂ otimesₘ f₃) = (id otimesₘ (id otimesₘ f₃)) 
∘ₗ α ∘ₗ (f₁₂ otim…
· 使用引理 `CoassocSimps.coassoc_left`：coassoc_left [Coalgebra R M] (f : M ->ₗ[R] M'
) : α ∘ₗ (δ otimesₘ f) ∘ₗ δ = (id otimesₘ (id otimesₘ f)) ∘ₗ (id otimesₘ δ) ∘ₗ δ
· 使用定理 `TensorProduct.map_id`：map_id : map (id : M ->ₗ[R] M) (id : N ->ₗ[R] N) =
 .id
· 使用定理 `CoassocSimps.TensorProduct.map_comp_assoc`：∀ {R : Type u_1} {M : Type u_
3} {N : Type u_4} {P : Type u_5} {M' : Type u_6} {N' : Type u_7} {P' : Type u_8}
   {M₁ : Type u_11} [inst : Com…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coassoc_left_assoc [Coalgebra R M] (f : M →ₗ[R] M') (g : N →ₗ[R] M) :
    α ∘ₗ (δ ⊗ₘ f) ∘ₗ δ ∘ₗ g = (id ⊗ₘ (id ⊗ₘ f)) ∘ₗ (id ⊗ₘ δ) ∘ₗ δ ∘ₗ g := by
  simp only [← LinearMap.comp_assoc]
  congr 1
  simp only [coassoc_simps]

@[coassoc_simps]
/-
**CoassocSimps.coassoc_right** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`。
形式化陈述：coassoc_right [Coalgebra R M] (f : M ->ₗ[R] M') : α⁻¹ ∘ₗ (f otimesₘ δ) ∘ₗ 
δ = ((f otimesₘ id) otimesₘ id) ∘ₗ (δ otimesₘ id) ∘ₗ δ
参数：f : M ->ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `TensorProduct.map_map_comp_assoc_symm_eq`：map_map_comp_assoc_symm_eq (f 
: M ->ₗ[R] Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) : map (map f g) h ∘ₗ (TensorProd
uct.assoc R M N P).symm = (Ten…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CoassocSimps.assoc_symm_comp_map`：assoc_symm_comp_map (f₁ : M₁ ->ₗ[R] N₁
) (f₂₃ : M ->ₗ[R] M₂ otimes[R] M₃) : α⁻¹ ∘ₗ (f₁ otimesₘ f₂₃) = ((f₁ otimesₘ .id)
 otimesₘ .id) ∘ₗ α⁻¹ ∘…
· 使用定理 `TensorProduct.map_id`：map_id : map (id : M ->ₗ[R] M) (id : N ->ₗ[R] N) =
 .id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coassoc_right [Coalgebra R M] (f : M →ₗ[R] M') :
    α⁻¹ ∘ₗ (f ⊗ₘ δ) ∘ₗ δ = ((f ⊗ₘ id) ⊗ₘ id) ∘ₗ (δ ⊗ₘ id) ∘ₗ δ := by
  simp_rw [← LinearMap.rTensor_def, ← coassoc_symm, ← LinearMap.comp_assoc, LinearMap.rTensor_def,
    map_map_comp_assoc_symm_eq]
  simp only [coassoc_simps]

@[coassoc_simps]
/-
**CoassocSimps.coassoc_right_assoc** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimps`。
形式化陈述：coassoc_right_assoc [Coalgebra R M] (f : M ->ₗ[R] M') (g : N ->ₗ[R] M) : α
⁻¹ ∘ₗ (f otimesₘ δ) ∘ₗ δ ∘ₗ g = ((f otimesₘ id) otimesₘ id) ∘ₗ (δ otimesₘ id) ∘ₗ
 δ ∘ₗ g
参数：f : M ->ₗ[R] M'；g : N ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `CoassocSimps.assoc_symm_comp_map`：assoc_symm_comp_map (f₁ : M₁ ->ₗ[R] N₁
) (f₂₃ : M ->ₗ[R] M₂ otimes[R] M₃) : α⁻¹ ∘ₗ (f₁ otimesₘ f₂₃) = ((f₁ otimesₘ .id)
 otimesₘ .id) ∘ₗ α⁻¹ ∘…
· 使用引理 `CoassocSimps.coassoc_right`：coassoc_right [Coalgebra R M] (f : M ->ₗ[R] 
M') : α⁻¹ ∘ₗ (f otimesₘ δ) ∘ₗ δ = ((f otimesₘ id) otimesₘ id) ∘ₗ (δ otimesₘ id) 
∘ₗ δ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.map_id`：map_id : map (id : M ->ₗ[R] M) (id : N ->ₗ[R] N) =
 .id
· 使用定理 `CoassocSimps.TensorProduct.map_comp_assoc`：∀ {R : Type u_1} {M : Type u_
3} {N : Type u_4} {P : Type u_5} {M' : Type u_6} {N' : Type u_7} {P' : Type u_8}
   {M₁ : Type u_11} [inst : Com…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coassoc_right_assoc [Coalgebra R M] (f : M →ₗ[R] M') (g : N →ₗ[R] M) :
    α⁻¹ ∘ₗ (f ⊗ₘ δ) ∘ₗ δ ∘ₗ g = ((f ⊗ₘ id) ⊗ₘ id) ∘ₗ (δ ⊗ₘ id) ∘ₗ δ ∘ₗ g := by
  simp only [← LinearMap.comp_assoc]
  congr 1
  simp only [coassoc_simps]
/-
**CoassocSimps.map_counit_comp_comul_left** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSimp
s`。
形式化陈述：map_counit_comp_comul_left [Coalgebra R M] (f : M ->ₗ[R] M') : (ε otimesₘ 
f) ∘ₗ δ = (id otimesₘ f) ∘ₗ fun⁻¹
参数：f : M ->ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.lTensor_comp_rTensor`：lTensor_comp_rTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (g.lTensor P).comp (f.rTensor N) = map f g
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `Coalgebra.rTensor_counit_comp_comul`：∀ {R : Type u} {A : Type v} {inst :
 CommSemiring R} {inst_1 : AddCommMonoid A} {inst_2 : _root_.Module R A}   [self
 : Coalgebra R A],   Line…
-/
lemma map_counit_comp_comul_left [Coalgebra R M] (f : M →ₗ[R] M') :
    (ε ⊗ₘ f) ∘ₗ δ = (id ⊗ₘ f) ∘ₗ λ⁻¹ := by
  rw [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_assoc, Coalgebra.rTensor_counit_comp_comul]
  rfl
/-
**CoassocSimps.map_counit_comp_comul_left_assoc** 是 Mathlib 中的一个引理，位于命名空间 `Coass
ocSimps`。
形式化陈述：map_counit_comp_comul_left_assoc [Coalgebra R M] (f : M ->ₗ[R] M') (g : P 
->ₗ[R] M) : (ε otimesₘ f) ∘ₗ δ ∘ₗ g = (id otimesₘ f) ∘ₗ fun⁻¹ ∘ₗ g
参数：f : M ->ₗ[R] M'；g : P ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `CoassocSimps.map_counit_comp_comul_left`：map_counit_comp_comul_left [Coa
lgebra R M] (f : M ->ₗ[R] M') : (ε otimesₘ f) ∘ₗ δ = (id otimesₘ f) ∘ₗ fun⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_counit_comp_comul_left_assoc [Coalgebra R M] (f : M →ₗ[R] M') (g : P →ₗ[R] M) :
    (ε ⊗ₘ f) ∘ₗ δ ∘ₗ g = (id ⊗ₘ f) ∘ₗ λ⁻¹ ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, map_counit_comp_comul_left]
/-
**CoassocSimps.map_counit_comp_comul_right** 是 Mathlib 中的一个引理，位于命名空间 `CoassocSim
ps`。
形式化陈述：map_counit_comp_comul_right [Coalgebra R M] (f : M ->ₗ[R] M') : (f otimesₘ
 ε) ∘ₗ δ = (f otimesₘ id) ∘ₗ ρ⁻¹
参数：f : M ->ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.rTensor_comp_lTensor`：rTensor_comp_lTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (f.rTensor Q).comp (g.lTensor M) = map f g
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Coalgebra.lTensor_counit_comp_comul`：∀ {R : Type u} {A : Type v} {inst :
 CommSemiring R} {inst_1 : AddCommMonoid A} {inst_2 : _root_.Module R A}   [self
 : Coalgebra R A],   Line…
-/
lemma map_counit_comp_comul_right [Coalgebra R M] (f : M →ₗ[R] M') :
    (f ⊗ₘ ε) ∘ₗ δ = (f ⊗ₘ id) ∘ₗ ρ⁻¹ := by
  rw [← LinearMap.rTensor_comp_lTensor, LinearMap.comp_assoc, Coalgebra.lTensor_counit_comp_comul]
  rfl
/-
**CoassocSimps.map_counit_comp_comul_right_assoc** 是 Mathlib 中的一个引理，位于命名空间 `Coas
socSimps`。
形式化陈述：map_counit_comp_comul_right_assoc [Coalgebra R M] (f : M ->ₗ[R] M') (g : P
 ->ₗ[R] M) : (f otimesₘ ε) ∘ₗ δ ∘ₗ g = (f otimesₘ id) ∘ₗ ρ⁻¹ ∘ₗ g
参数：f : M ->ₗ[R] M'；g : P ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `CoassocSimps.map_counit_comp_comul_right`：map_counit_comp_comul_right [C
oalgebra R M] (f : M ->ₗ[R] M') : (f otimesₘ ε) ∘ₗ δ = (f otimesₘ id) ∘ₗ ρ⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_counit_comp_comul_right_assoc [Coalgebra R M] (f : M →ₗ[R] M') (g : P →ₗ[R] M) :
    (f ⊗ₘ ε) ∘ₗ δ ∘ₗ g = (f ⊗ₘ id) ∘ₗ ρ⁻¹ ∘ₗ g := by
  simp_rw [← LinearMap.comp_assoc, map_counit_comp_comul_right]

@[coassoc_simps]
/-
**CoassocSimps.assoc_comp_map_comm_comp_comul_comp_comul** 是 Mathlib 中的一个引理，位于命名
空间 `CoassocSimps`。
形式化陈述：assoc_comp_map_comm_comp_comul_comp_comul [Coalgebra R M] (f : M ->ₗ[R] N)
 : α ∘ₗ ((β ∘ₗ δ) otimesₘ f) ∘ₗ δ = (id otimesₘ ((id otimesₘ f) ∘ₗ β)) ∘ₗ α ∘ₗ δ
 otimesₘ id ∘ₗ β ∘ₗ δ
参数：f : M ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CoassocSimps.symm_comp_map_assoc`：symm_comp_map_assoc (f : M ->ₗ[R] M') 
(g : N ->ₗ[R] N') (h : P ->ₗ[R] M otimes[R] N) : β ∘ₗ (f otimesₘ g) ∘ₗ h = (g ot
imesₘ f) ∘ₗ β ∘ₗ h
· 使用定理 `LinearMap.lTensor_def`：lTensor_def : f.lTensor M = TensorProduct.map Lin
earMap.id f
· 使用定理 `Coalgebra.coassoc`：∀ {R : Type u} {A : Type v} {inst : CommSemiring R} {
inst_1 : AddCommMonoid A} {inst_2 : _root_.Module R A}   [self : Coalgebra R A],
   ↑(Te…
· 使用定理 `LinearMap.comp_id`：comp_id : f.comp id = f
· 使用定理 `TensorProduct.map_comp`：map_comp (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂
₃] N₃) (f₁ : M ->ₛₗ[σ₁₂] M₂) (g₁ : N ->ₛₗ[σ₁₂] N₂) : map (f₂ ∘ₛₗ f₁) (g₂ ∘ₛₗ g₁)
 = (map f₂ g…
· 使用定理 `LinearMap.rTensor_def`：rTensor_def : f.rTensor M = TensorProduct.map f L
inearMap.id
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
lemma assoc_comp_map_comm_comp_comul_comp_comul [Coalgebra R M] (f : M →ₗ[R] N) :
    α ∘ₗ ((β ∘ₗ δ) ⊗ₘ f) ∘ₗ δ = (id ⊗ₘ ((id ⊗ₘ f) ∘ₗ β)) ∘ₗ α ∘ₗ δ ⊗ₘ id ∘ₗ β ∘ₗ δ := by
  rw [← symm_comp_map_assoc, ← LinearMap.lTensor_def, ← LinearMap.lTensor_def,
    ← LinearMap.lTensor_def, ← Coalgebra.coassoc, ← f.comp_id,
    TensorProduct.map_comp, ← LinearMap.rTensor_def]
  simp only [← LinearMap.comp_assoc]
  congr 2
  ext
  rfl

@[coassoc_simps]
/-
**CoassocSimps.assoc_comp_map_comm_comp_comul_comp_comul_assoc** 是 Mathlib 中的一个引
理，位于命名空间 `CoassocSimps`。
形式化陈述：assoc_comp_map_comm_comp_comul_comp_comul_assoc [Coalgebra R M] (f : M ->ₗ
[R] N) (h : Q ->ₗ[R] M) : α ∘ₗ ((β ∘ₗ δ) otimesₘ f) ∘ₗ δ ∘ₗ h = (id otimesₘ ((id
 otimesₘ f) ∘ₗ β)) ∘ₗ α ∘ₗ δ otimesₘ id ∘ₗ β ∘ₗ δ ∘ₗ h
参数：f : M ->ₗ[R] N；h : Q ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `CoassocSimps.assoc_comp_map`：assoc_comp_map (f₃ : M₃ ->ₗ[R] N₃) (f₁₂ : M
 ->ₗ[R] M₁ otimes[R] M₂) : α ∘ₗ (f₁₂ otimesₘ f₃) = (id otimesₘ (id otimesₘ f₃)) 
∘ₗ α ∘ₗ (f₁₂ otim…
· 使用引理 `CoassocSimps.assoc_comp_map_comm_comp_comul_comp_comul`：assoc_comp_map_c
omm_comp_comul_comp_comul [Coalgebra R M] (f : M ->ₗ[R] N) : α ∘ₗ ((β ∘ₗ δ) otim
esₘ f) ∘ₗ δ = (id otimesₘ ((id otimesₘ f) ∘ₗ…
· 使用定理 `TensorProduct.map_id`：map_id : map (id : M ->ₗ[R] M) (id : N ->ₗ[R] N) =
 .id
· 使用定理 `CoassocSimps.TensorProduct.map_comp_assoc`：∀ {R : Type u_1} {M : Type u_
3} {N : Type u_4} {P : Type u_5} {M' : Type u_6} {N' : Type u_7} {P' : Type u_8}
   {M₁ : Type u_11} [inst : Com…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma assoc_comp_map_comm_comp_comul_comp_comul_assoc
    [Coalgebra R M] (f : M →ₗ[R] N) (h : Q →ₗ[R] M) :
    α ∘ₗ ((β ∘ₗ δ) ⊗ₘ f) ∘ₗ δ ∘ₗ h = (id ⊗ₘ ((id ⊗ₘ f) ∘ₗ β)) ∘ₗ α ∘ₗ δ ⊗ₘ id ∘ₗ β ∘ₗ δ ∘ₗ h := by
  simp_rw [← LinearMap.comp_assoc]
  congr 1
  simp only [coassoc_simps]

end CoassocSimps

