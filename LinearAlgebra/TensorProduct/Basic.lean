/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Defs

/-!
# Universal property of the tensor product

Given any bilinear map `f : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂`, there is a unique semilinear map
`TensorProduct.lift f : TensorProduct R M N →ₛₗ[σ₁₂] P₂` whose composition with the canonical
bilinear map `TensorProduct.mk` is the given bilinear map `f`.  Uniqueness is shown in the theorem
`TensorProduct.lift.unique`.

## Tags

bilinear, tensor, tensor product
-/

@[expose] public section

section Semiring

variable {R R₂ R₃ R' R'' : Type*}
variable [CommSemiring R] [CommSemiring R₂] [CommSemiring R₃] [Monoid R'] [Semiring R'']
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}
variable {A M N P Q S : Type*}
variable {M₂ M₃ N₂ N₃ P' P₂ P₃ Q' Q₂ Q₃ : Type*}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [AddCommMonoid S]
variable [AddCommMonoid P'] [AddCommMonoid Q']
variable [AddCommMonoid M₂] [AddCommMonoid N₂] [AddCommMonoid P₂] [AddCommMonoid Q₂]
variable [AddCommMonoid M₃] [AddCommMonoid N₃] [AddCommMonoid P₃] [AddCommMonoid Q₃]
variable [DistribMulAction R' M]
variable [Module R'' M]
variable [Module R M] [Module R N] [Module R S]
variable [Module R P'] [Module R Q']
variable [Module R₂ M₂] [Module R₂ N₂] [Module R₂ P₂] [Module R₂ Q₂]
variable [Module R₃ M₃] [Module R₃ N₃] [Module R₃ P₃] [Module R₃ Q₃]

variable (M N)

namespace TensorProduct

section Module

variable {M N}

/-- Lift an `R`-balanced map to the tensor product.
A map `f : M →+ N →+ P` additive in both components is `R`-balanced, or middle linear with respect
to `R`, if scalar multiplication in either argument is equivalent, `f (r • m) n = f m (r • n)`.
Note that strictly the first action should be a right-action by `R`, but for now `R` is commutative
so it doesn't matter. -/
-- TODO: use this to implement `lift` and `SMul.aux`. For now we do not do this as it causes
-- performance issues elsewhere.
/-
**TensorProduct.liftAddHom** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：liftAddHom (f : M ->+ N ->+ P) (hf : forall (r : R) (m : M) (n : N), f (r 
• m) n = f m (r • n)) : M otimes[R] N ->+ P
参数：f : M ->+ N ->+ P；hf : forall (r : R) (m : M) (n : N), f (r • m) n = f m (r •
 n)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def liftAddHom (f : M →+ N →+ P)
    (hf : ∀ (r : R) (m : M) (n : N), f (r • m) n = f m (r • n)) :
    M ⊗[R] N →+ P :=
  (addConGen (TensorProduct.Eqv R M N)).lift (FreeAddMonoid.lift (fun mn : M × N => f mn.1 mn.2)) <|
    AddCon.addConGen_le.2 fun x y hxy =>
      match x, y, hxy with
      | _, _, .of_zero_left n =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_zero, FreeAddMonoid.lift_eval_of, map_zero,
          AddMonoidHom.zero_apply]
      | _, _, .of_zero_right m =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_zero, FreeAddMonoid.lift_eval_of, map_zero]
      | _, _, .of_add_left m₁ m₂ n =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_add, FreeAddMonoid.lift_eval_of, map_add,
          AddMonoidHom.add_apply]
      | _, _, .of_add_right m n₁ n₂ =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_add, FreeAddMonoid.lift_eval_of, map_add]
      | _, _, .of_smul s m n =>
        (AddCon.ker_rel _).2 <| by rw [FreeAddMonoid.lift_eval_of, FreeAddMonoid.lift_eval_of, hf]
      | _, _, .add_comm x y =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_add, add_comm]

@[simp]
/-
**TensorProduct.liftAddHom_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：liftAddHom_tmul (f : M ->+ N ->+ P) (hf : forall (r : R) (m : M) (n : N), 
f (r • m) n = f m (r • n)) (m : M) (n : N) : liftAddHom f hf (m otimesₜ n) = f m
 n
参数：f : M ->+ N ->+ P；hf : forall (r : R) (m : M) (n : N), f (r • m) n = f m (r •
 n)；m : M；n : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftAddHom_tmul (f : M →+ N →+ P)
    (hf : ∀ (r : R) (m : M) (n : N), f (r • m) n = f m (r • n)) (m : M) (n : N) :
    liftAddHom f hf (m ⊗ₜ n) = f m n :=
  rfl

end Module

variable [Module R P] [Module R Q]

section UniversalProperty

variable {M N}
variable (f : M →ₗ[R] N →ₗ[R] P)
variable (f' : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂)

set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary function to constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
/-
**TensorProduct.liftAux** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：liftAux : M otimes[R] N ->+ P₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary function to constructing a linear map `M ⊗ N → P` given a bilinear map
 `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → 
M ⊗ N` is
the given bilinear map `M → N → P`.
-/
def liftAux : M ⊗[R] N →+ P₂ :=
  liftAddHom (LinearMap.toAddMonoidHom'.comp <| f'.toAddMonoidHom)
    fun r m n => by dsimp; rw [LinearMap.map_smulₛₗ₂, map_smulₛₗ]
/-
**TensorProduct.liftAux_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：liftAux_tmul (m n) : liftAux f' (m otimesₜ n) = f' m n
参数：m n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftAux_tmul (m n) : liftAux f' (m ⊗ₜ n) = f' m n :=
  rfl

variable {f f'}

@[simp]
/-
**TensorProduct.liftAux.smul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct.liftAux`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Type u_7} {N : Type u_8} {P 
: Type u_9} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : Ad
dCommMonoid P] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst
_6 : _root_.Module R P] {f : M →ₗ[R] N →ₗ[R] P} (r : R) (x : TensorProduct R M N
),   (TensorProduct.liftAux f) (r • x) = r • (TensorProduct.liftAux f) x
参数：r : R；x : TensorProduct R M N；TensorProduct.liftAux f；r • x；TensorProduct.lif
tAux f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.liftAux.smulₛₗ`：∀ {R : Type u_1} {R₂ : Type u_2} [inst : C
ommSemiring R] [inst_1 : CommSemiring R₂] {σ₁₂ : R →+* R₂} {M : Type u_7}   {N :
 Type u_8} {P₂ : T…
-/
theorem liftAux.smulₛₗ (r : R) (x) : liftAux f' (r • x) = σ₁₂ r • liftAux f' x :=
  TensorProduct.induction_on x (smul_zero _).symm
    (fun p q => by simp_rw [← tmul_smul, liftAux_tmul, (f' p).map_smulₛₗ])
    fun p q ih1 ih2 => by simp_rw [smul_add, (liftAux f').map_add, ih1, ih2, smul_add]
/-
**TensorProduct.liftAux.smul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct.liftAux`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Type u_7} {N : Type u_8} {P 
: Type u_9} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : Ad
dCommMonoid P] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst
_6 : _root_.Module R P] {f : M →ₗ[R] N →ₗ[R] P} (r : R) (x : TensorProduct R M N
),   (TensorProduct.liftAux f) (r • x) = r • (TensorProduct.liftAux f) x
参数：r : R；x : TensorProduct R M N；TensorProduct.liftAux f；r • x；TensorProduct.lif
tAux f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.liftAux.smulₛₗ`：∀ {R : Type u_1} {R₂ : Type u_2} [inst : C
ommSemiring R] [inst_1 : CommSemiring R₂] {σ₁₂ : R →+* R₂} {M : Type u_7}   {N :
 Type u_8} {P₂ : T…
-/
theorem liftAux.smul (r : R) (x) : liftAux f (r • x) = r • liftAux f x :=
  liftAux.smulₛₗ _ _

variable (f') in
/-- Constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P` with the property that
its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`.

This works for semilinear maps. -/
/-
**TensorProduct.lift** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：lift : M otimes[R] N ->ₛₗ[σ₁₂] P₂
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.liftAux.smulₛₗ`：∀ {R : Type u_1} {R₂ : Type u_2} [inst : C
ommSemiring R] [inst_1 : CommSemiring R₂] {σ₁₂ : R →+* R₂} {M : Type u_7}   {N :
 Type u_8} {P₂ : T…

--- 原说明 ---
Constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P` with the 
property that
its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`.

This works for semilinear maps.
-/
def lift : M ⊗[R] N →ₛₗ[σ₁₂] P₂ :=
  { liftAux f' with map_smul' := liftAux.smulₛₗ }

@[simp]
/-
**TensorProduct.lift.tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct.lift`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} [inst : CommSemiring R] [inst_1 : CommSem
iring R₂] {σ₁₂ : R →+* R₂} {M : Type u_7}   {N : Type u_8} {P₂ : Type u_17} [ins
t_2 : AddCommMonoid M] [inst_3 : AddCommMonoid N] [inst_4 : AddCommMonoid P₂]   
[inst_5 : _root_.Module R M] [inst_6 : _root_.Module R N] [inst_7 : _root_.Modul
e R₂ P₂]   {f' : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂} (x : M) (y : N), (TensorProduct.lift 
f') (x ⊗ₜ[R] y) = (f' x) y
参数：x : M；y : N；TensorProduct.lift f'；x ⊗ₜ[R] y；f' x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift.tmul (x y) : lift f' (x ⊗ₜ y) = f' x y :=
  rfl

@[simp]
/-
**TensorProduct.lift.tmul'** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct.lift`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} [inst : CommSemiring R] [inst_1 : CommSem
iring R₂] {σ₁₂ : R →+* R₂} {M : Type u_7}   {N : Type u_8} {P₂ : Type u_17} [ins
t_2 : AddCommMonoid M] [inst_3 : AddCommMonoid N] [inst_4 : AddCommMonoid P₂]   
[inst_5 : _root_.Module R M] [inst_6 : _root_.Module R N] [inst_7 : _root_.Modul
e R₂ P₂]   {f' : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂} (x : M) (y : N), (TensorProduct.lift 
f').toAddHom (x ⊗ₜ[R] y) = (f' x) y
参数：x : M；y : N；TensorProduct.lift f'；x ⊗ₜ[R] y；f' x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift.tmul' (x y) : (lift f').1 (x ⊗ₜ y) = f' x y :=
  rfl
/-
**TensorProduct.ext'** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall x y, g (x otimesₜ y) =
 h (x otimesₜ y)) : g = h
参数：H : forall x y, g (x otimesₜ y) = h (x otimesₜ y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
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
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
-/
theorem ext' {g h : M ⊗[R] N →ₛₗ[σ₁₂] P₂} (H : ∀ x y, g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h :=
  LinearMap.ext fun z =>
    TensorProduct.induction_on z (by simp_rw [map_zero]) H fun x y ihx ihy => by
      rw [g.map_add, h.map_add, ihx, ihy]
/-
**TensorProduct.lift.unique** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct.lift`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} [inst : CommSemiring R] [inst_1 : CommSem
iring R₂] {σ₁₂ : R →+* R₂} {M : Type u_7}   {N : Type u_8} {P₂ : Type u_17} [ins
t_2 : AddCommMonoid M] [inst_3 : AddCommMonoid N] [inst_4 : AddCommMonoid P₂]   
[inst_5 : _root_.Module R M] [inst_6 : _root_.Module R N] [inst_7 : _root_.Modul
e R₂ P₂]   {f' : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂} {g : TensorProduct R M N →ₛₗ[σ₁₂] P₂}
,   (∀ (x : M) (y : N), g (x ⊗ₜ[R] y) = (f' x) y) → g = TensorProduct.lift f'
参数：∀ (x : M) (y : N), g (x ⊗ₜ[R] y) = (f' x) y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.lift.tmul`：∀ {R : Type u_1} {R₂ : Type u_2} [inst : CommSe
miring R] [inst_1 : CommSemiring R₂] {σ₁₂ : R →+* R₂} {M : Type u_7}   {N : Type
 u_8} {P₂ : T…
-/
theorem lift.unique {g : M ⊗[R] N →ₛₗ[σ₁₂] P₂} (H : ∀ x y, g (x ⊗ₜ y) = f' x y) : g = lift f' :=
  ext' fun m n => by rw [H, lift.tmul]
/-
**TensorProduct.lift_mk** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：lift_mk : lift (mk R M N) = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TensorProduct.lift.unique`：∀ {R : Type u_1} {R₂ : Type u_2} [inst : Comm
Semiring R] [inst_1 : CommSemiring R₂] {σ₁₂ : R →+* R₂} {M : Type u_7}   {N : Ty
pe u_8} {P₂ : T…
-/
theorem lift_mk : lift (mk R M N) = LinearMap.id :=
  Eq.symm <| lift.unique fun _ _ => rfl
/-
**TensorProduct.lift_compr** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_compr₂ₛₗ [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (h : P₂ →ₛₗ[σ₂₃] P₃) :
    lift (f'.compr₂ₛₗ h) = h.comp (lift f') :=
  Eq.symm <| lift.unique fun _ _ => by simp
/-
**TensorProduct.lift_compr** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_compr₂ (g : P →ₗ[R] Q) : lift (f.compr₂ g) = g.comp (lift f) :=
  Eq.symm <| lift.unique fun _ _ => by simp
/-
**TensorProduct.lift_mk_compr** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_mk_compr₂ₛₗ (g : M ⊗ N →ₛₗ[σ₁₂] P₂) : lift ((mk R M N).compr₂ₛₗ g) = g := by
  rw [lift_compr₂ₛₗ g, lift_mk, LinearMap.comp_id]
/-
**TensorProduct.lift_mk_compr** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_mk_compr₂ (f : M ⊗ N →ₗ[R] P) : lift ((mk R M N).compr₂ f) = f := by
  rw [lift_compr₂ f, lift_mk, LinearMap.comp_id]

/-- This used to be an `@[ext]` lemma, but it fails very slowly when the `ext` tactic tries to apply
it in some cases, notably when one wants to show equality of two linear maps. The `@[ext]`
attribute is now added locally where it is needed. Using this as the `@[ext]` lemma instead of
`TensorProduct.ext'` allows `ext` to apply lemmas specific to `M →ₗ _` and `N →ₗ _`.

See note [partially-applied ext lemmas]. -/
/-
**TensorProduct.ext** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).compr₂ₛₗ g = (mk R M N
).compr₂ₛₗ h) : g = h
参数：H : (mk R M N).compr₂ₛₗ g = (mk R M N).compr₂ₛₗ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TensorProduct.lift_mk_compr₂ₛₗ`：lift_mk_compr₂ₛₗ (g : M otimes N ->ₛₗ[σ₁
₂] P₂) : lift ((mk R M N).compr₂ₛₗ g) = g

--- 原说明 ---
This used to be an `@[ext]` lemma, but it fails very slowly when the `ext` tacti
c tries to apply
it in some cases, notably when one wants to show equality of two linear maps. Th
e `@[ext]`
attribute is now added locally where it is needed. Using this as the `@[ext]` le
mma instead of
`TensorProduct.ext'` allows `ext` to apply lemmas specific to `M →ₗ _` and `N →ₗ
 _`.

See note [partially-applied ext lemmas].
-/
theorem ext {g h : M ⊗ N →ₛₗ[σ₁₂] P₂} (H : (mk R M N).compr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) :
    g = h := by
  rw [← lift_mk_compr₂ₛₗ g, H, lift_mk_compr₂ₛₗ]

attribute [local ext high] ext

variable (M N P₂ σ₁₂) in
/-- Linearly constructing a semilinear map `M ⊗ N → P` given a bilinear map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
/-
**TensorProduct.uncurry** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：uncurry : (M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂) ->ₗ[R₂] M otimes[R] N ->ₛₗ[σ₁₂] P₂ 
where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linearly constructing a semilinear map `M ⊗ N → P` given a bilinear map `M → N →
 P`
with the property that its composition with the canonical bilinear map `M → N → 
M ⊗ N` is
the given bilinear map `M → N → P`.
-/
def uncurry : (M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂) →ₗ[R₂] M ⊗[R] N →ₛₗ[σ₁₂] P₂ where
  toFun := lift
  map_add' f g := by ext; rfl
  map_smul' _ _ := by ext; rfl

@[simp]
/-
**TensorProduct.uncurry_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：uncurry_apply (f : M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂) (m : M) (n : N) : uncurry σ
₁₂ M N P₂ f (m otimesₜ n) = f m n
参数：f : M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂；m : M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem uncurry_apply (f : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂) (m : M) (n : N) :
    uncurry σ₁₂ M N P₂ f (m ⊗ₜ n) = f m n := rfl

variable (M N P₂ σ₁₂)

/-- A linear equivalence constructing a semilinear map `M ⊗ N → P` given a bilinear map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
/-
**TensorProduct.lift.equiv** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct.lift`。
形式化陈述：{R : Type u_1} →   {R₂ : Type u_2} →     [inst : CommSemiring R] →       [
inst_1 : CommSemiring R₂] →         (σ₁₂ : R →+* R₂) →           (M : Type u_7) 
→             (N : Type u_8) →               (P₂ : Type u_17) →                 
[inst_2 : AddCommMonoid M] →                   [inst_3 : AddCommMonoid N] →     
                [inst_4 : AddCommMonoid P₂] →                       [inst_5 : _r
oot_.Module R M] →                         [inst_6 : _root_.Module R N] →       
                    [inst_7 : _root_.Module R₂ P₂] →                            
 (M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂) ≃ₗ[R₂] TensorProduct R M N →ₛₗ[σ₁₂] P₂
参数：σ₁₂ : R →+* R₂；M : Type u_7；N : Type u_8；P₂ : Type u_17；M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂]
 P₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear equivalence constructing a semilinear map `M ⊗ N → P` given a bilinear 
map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → 
M ⊗ N` is
the given bilinear map `M → N → P`.
-/
def lift.equiv : (M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂) ≃ₗ[R₂] M ⊗[R] N →ₛₗ[σ₁₂] P₂ :=
  { uncurry σ₁₂ M N P₂ with
    invFun := fun f => (mk R M N).compr₂ₛₗ f }

@[simp]
/-
**TensorProduct.lift.equiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct.lift`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} [inst : CommSemiring R] [inst_1 : CommSem
iring R₂] (σ₁₂ : R →+* R₂) (M : Type u_7)   (N : Type u_8) (P₂ : Type u_17) [ins
t_2 : AddCommMonoid M] [inst_3 : AddCommMonoid N] [inst_4 : AddCommMonoid P₂]   
[inst_5 : _root_.Module R M] [inst_6 : _root_.Module R N] [inst_7 : _root_.Modul
e R₂ P₂]   (f : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂) (m : M) (n : N), ((TensorProduct.lift.
equiv σ₁₂ M N P₂) f) (m ⊗ₜ[R] n) = (f m) n
参数：σ₁₂ : R →+* R₂；M : Type u_7；N : Type u_8；P₂ : Type u_17；f : M →ₛₗ[σ₁₂] N →ₛₗ[
σ₁₂] P₂；m : M；n : N；(TensorProduct.lift.equiv σ₁₂ M N P₂) f；m ⊗ₜ[R] n；f m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.uncurry_apply`：uncurry_apply (f : M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] 
P₂) (m : M) (n : N) : uncurry σ₁₂ M N P₂ f (m otimesₜ n) = f m n
-/
theorem lift.equiv_apply (f : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂) (m : M) (n : N) :
    lift.equiv σ₁₂ M N P₂ f (m ⊗ₜ n) = f m n :=
  uncurry_apply f m n

@[simp]
/-
**TensorProduct.lift.equiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct.l
ift`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} [inst : CommSemiring R] [inst_1 : CommSem
iring R₂] (σ₁₂ : R →+* R₂) (M : Type u_7)   (N : Type u_8) (P₂ : Type u_17) [ins
t_2 : AddCommMonoid M] [inst_3 : AddCommMonoid N] [inst_4 : AddCommMonoid P₂]   
[inst_5 : _root_.Module R M] [inst_6 : _root_.Module R N] [inst_7 : _root_.Modul
e R₂ P₂]   (f : TensorProduct R M N →ₛₗ[σ₁₂] P₂) (m : M) (n : N),   (((TensorPro
duct.lift.equiv σ₁₂ M N P₂).symm f) m) n = f (m ⊗ₜ[R] n)
参数：σ₁₂ : R →+* R₂；M : Type u_7；N : Type u_8；P₂ : Type u_17；f : TensorProduct R M
 N →ₛₗ[σ₁₂] P₂；m : M；n : N；((TensorProduct.lift.equiv σ₁₂ M N P₂).symm f) m；m ⊗ₜ
[R] n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem lift.equiv_symm_apply (f : M ⊗[R] N →ₛₗ[σ₁₂] P₂) (m : M) (n : N) :
    (lift.equiv σ₁₂ M N P₂).symm f m n = f (m ⊗ₜ n) :=
  rfl

/-- Given a semilinear map `M ⊗ N → P`, compose it with the canonical bilinear map
`M → N → M ⊗ N` to form a bilinear map `M → N → P`. -/
/-
**TensorProduct.lcurry** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：lcurry : (M otimes[R] N ->ₛₗ[σ₁₂] P₂) ->ₗ[R₂] M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a semilinear map `M ⊗ N → P`, compose it with the canonical bilinear map
`M → N → M ⊗ N` to form a bilinear map `M → N → P`.
-/
def lcurry : (M ⊗[R] N →ₛₗ[σ₁₂] P₂) →ₗ[R₂] M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂ :=
  (lift.equiv σ₁₂ M N P₂).symm

variable {M N P₂ σ₁₂}

@[simp]
/-
**TensorProduct.lcurry_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：lcurry_apply (f : M otimes[R] N ->ₛₗ[σ₁₂] P₂) (m : M) (n : N) : lcurry σ₁₂
 M N P₂ f m n = f (m otimesₜ n)
参数：f : M otimes[R] N ->ₛₗ[σ₁₂] P₂；m : M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem lcurry_apply (f : M ⊗[R] N →ₛₗ[σ₁₂] P₂) (m : M) (n : N) :
    lcurry σ₁₂ M N P₂ f m n = f (m ⊗ₜ n) :=
  rfl

/-- Given a semilinear map `M ⊗ N → P`, compose it with the canonical bilinear map
`M → N → M ⊗ N` to form a bilinear map `M → N → P`. -/
/-
**TensorProduct.curry** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：curry (f : M otimes[R] N ->ₛₗ[σ₁₂] P₂) : M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂
参数：f : M otimes[R] N ->ₛₗ[σ₁₂] P₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a semilinear map `M ⊗ N → P`, compose it with the canonical bilinear map
`M → N → M ⊗ N` to form a bilinear map `M → N → P`.
-/
def curry (f : M ⊗[R] N →ₛₗ[σ₁₂] P₂) : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂ :=
  lcurry σ₁₂ M N P₂ f

@[simp]
/-
**TensorProduct.curry_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：curry_apply (f : M otimes[R] N ->ₛₗ[σ₁₂] P₂) (m : M) (n : N) : curry f m n
 = f (m otimesₜ n)
参数：f : M otimes[R] N ->ₛₗ[σ₁₂] P₂；m : M；n : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem curry_apply (f : M ⊗[R] N →ₛₗ[σ₁₂] P₂) (m : M) (n : N) : curry f m n = f (m ⊗ₜ n) :=
  rfl
/-
**TensorProduct.curry_injective** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：curry_injective : Function.Injective (curry : (M otimes[R] N ->ₛₗ[σ₁₂] P₂)
 -> M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
-/
theorem curry_injective :
    Function.Injective (curry : (M ⊗[R] N →ₛₗ[σ₁₂] P₂) → M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂) :=
  fun _ _ H => ext H
/-
**TensorProduct.ext_threefold** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：ext_threefold {g h : M otimes[R] N otimes[R] P ->ₛₗ[σ₁₂] P₂} (H : forall x
 y z, g (x otimesₜ y otimesₜ z) = h (x otimesₜ y otimesₜ z)) : g = h
参数：H : forall x y z, g (x otimesₜ y otimesₜ z) = h (x otimesₜ y otimesₜ z)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem ext_threefold {g h : M ⊗[R] N ⊗[R] P →ₛₗ[σ₁₂] P₂}
    (H : ∀ x y z, g (x ⊗ₜ y ⊗ₜ z) = h (x ⊗ₜ y ⊗ₜ z)) : g = h := by
  ext x y z
  exact H x y z
/-
**TensorProduct.ext_threefold'** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：ext_threefold' {g h : M otimes[R] (N otimes[R] P) ->ₛₗ[σ₁₂] P₂} (H : foral
l x y z, g (x otimesₜ (y otimesₜ z)) = h (x otimesₜ (y otimesₜ z))) : g = h
参数：N otimes[R] P；H : forall x y z, g (x otimesₜ (y otimesₜ z)) = h (x otimesₜ (y
 otimesₜ z))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem ext_threefold' {g h : M ⊗[R] (N ⊗[R] P) →ₛₗ[σ₁₂] P₂}
    (H : ∀ x y z, g (x ⊗ₜ (y ⊗ₜ z)) = h (x ⊗ₜ (y ⊗ₜ z))) : g = h := by
  ext x y z
  exact H x y z

-- We'll need this one for checking the pentagon identity!
/-
**TensorProduct.ext_fourfold** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：ext_fourfold {g h : M otimes[R] N otimes[R] P otimes[R] Q ->ₛₗ[σ₁₂] P₂} (H
 : forall w x y z, g (w otimesₜ x otimesₜ y otimesₜ z) = h (w otimesₜ x otimesₜ 
y otimesₜ z)) : g = h
参数：H : forall w x y z, g (w otimesₜ x otimesₜ y otimesₜ z) = h (w otimesₜ x otim
esₜ y otimesₜ z)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem ext_fourfold {g h : M ⊗[R] N ⊗[R] P ⊗[R] Q →ₛₗ[σ₁₂] P₂}
    (H : ∀ w x y z, g (w ⊗ₜ x ⊗ₜ y ⊗ₜ z) = h (w ⊗ₜ x ⊗ₜ y ⊗ₜ z)) : g = h := by
  ext w x y z
  exact H w x y z

/-- Two semilinear maps `(M ⊗ N) ⊗ (P ⊗ Q) → P₂` which agree on all elements of the
form `(m ⊗ₜ n) ⊗ₜ (p ⊗ₜ q)` are equal. -/
/-
**TensorProduct.ext_fourfold'** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：ext_fourfold' {φ ψ : M otimes[R] N otimes[R] (P otimes[R] Q) ->ₛₗ[σ₁₂] P₂}
 (H : forall w x y z, φ (w otimesₜ x otimesₜ (y otimesₜ z)) = ψ (w otimesₜ x oti
mesₜ (y otimesₜ z))) : φ = ψ
参数：P otimes[R] Q；H : forall w x y z, φ (w otimesₜ x otimesₜ (y otimesₜ z)) = ψ (
w otimesₜ x otimesₜ (y otimesₜ z))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g

--- 原说明 ---
Two semilinear maps `(M ⊗ N) ⊗ (P ⊗ Q) → P₂` which agree on all elements of the
form `(m ⊗ₜ n) ⊗ₜ (p ⊗ₜ q)` are equal.
-/
theorem ext_fourfold' {φ ψ : M ⊗[R] N ⊗[R] (P ⊗[R] Q) →ₛₗ[σ₁₂] P₂}
    (H : ∀ w x y z, φ (w ⊗ₜ x ⊗ₜ (y ⊗ₜ z)) = ψ (w ⊗ₜ x ⊗ₜ (y ⊗ₜ z))) : φ = ψ := by
  ext m n p q
  exact H m n p q

/-- Two semilinear maps `M ⊗ (N ⊗ P) ⊗ Q → P₂` which agree on all elements of the
form `m ⊗ₜ (n ⊗ₜ p) ⊗ₜ q` are equal. -/
/-
**TensorProduct.ext_fourfold''** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：ext_fourfold'' {φ ψ : M otimes[R] (N otimes[R] P) otimes[R] Q ->ₛₗ[σ₁₂] P₂
} (H : forall w x y z, φ (w otimesₜ (x otimesₜ y) otimesₜ z) = ψ (w otimesₜ (x o
timesₜ y) otimesₜ z)) : φ = ψ
参数：N otimes[R] P；H : forall w x y z, φ (w otimesₜ (x otimesₜ y) otimesₜ z) = ψ (
w otimesₜ (x otimesₜ y) otimesₜ z)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g

--- 原说明 ---
Two semilinear maps `M ⊗ (N ⊗ P) ⊗ Q → P₂` which agree on all elements of the
form `m ⊗ₜ (n ⊗ₜ p) ⊗ₜ q` are equal.
-/
theorem ext_fourfold'' {φ ψ : M ⊗[R] (N ⊗[R] P) ⊗[R] Q →ₛₗ[σ₁₂] P₂}
    (H : ∀ w x y z, φ (w ⊗ₜ (x ⊗ₜ y) ⊗ₜ z) = ψ (w ⊗ₜ (x ⊗ₜ y) ⊗ₜ z)) : φ = ψ := by
  ext m n p q
  exact H m n p q

end UniversalProperty

variable {M N}
section

variable (R M N)

/-- The tensor product of modules is commutative, up to linear equivalence. -/
/-
**TensorProduct.comm** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：(R : Type u_1) →   [inst : CommSemiring R] →     (M : Type u_7) →       (N
 : Type u_8) →         [inst_1 : AddCommMonoid M] →           [inst_2 : AddCommM
onoid N] →             [inst_3 : _root_.Module R M] → [inst_4 : _root_.Module R 
N] → TensorProduct R M N ≃ₗ[R] TensorProduct R N M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of modules is commutative, up to linear equivalence.
-/
protected def comm : M ⊗[R] N ≃ₗ[R] N ⊗[R] M :=
  LinearEquiv.ofLinearMap (lift (mk R N M).flip) (lift (mk R M N).flip) (ext' fun _ _ => rfl)
    (ext' fun _ _ => rfl)

@[simp]
/-
**TensorProduct.comm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：comm_tmul (m : M) (n : N) : (TensorProduct.comm R M N) (m otimesₜ n) = n o
timesₜ m
参数：m : M；n : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comm_tmul (m : M) (n : N) : (TensorProduct.comm R M N) (m ⊗ₜ n) = n ⊗ₜ m :=
  rfl

@[simp]
/-
**TensorProduct.comm_symm** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：comm_symm : (TensorProduct.comm R M N).symm = TensorProduct.comm R N M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comm_symm : (TensorProduct.comm R M N).symm = TensorProduct.comm R N M := rfl
/-
**TensorProduct.comm_symm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：comm_symm_tmul (m : M) (n : N) : (TensorProduct.comm R M N).symm (n otimes
ₜ m) = m otimesₜ n
参数：m : M；n : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comm_symm_tmul (m : M) (n : N) : (TensorProduct.comm R M N).symm (n ⊗ₜ m) = m ⊗ₜ n :=
  rfl

-- Why is the `toLinearMap` necessary ? And why is this slow ?
/-
**TensorProduct.lift_comp_comm_eq** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：lift_comp_comm_eq (f : M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂) : lift f ∘ₛₗ (TensorPro
duct.comm R N M).toLinearMap = lift f.flip
参数：f : M ->ₛₗ[σ₁₂] N ->ₛₗ[σ₁₂] P₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
-/
lemma lift_comp_comm_eq (f : M →ₛₗ[σ₁₂] N →ₛₗ[σ₁₂] P₂) :
    lift f ∘ₛₗ (TensorProduct.comm R N M).toLinearMap = lift f.flip :=
  ext rfl

attribute [local ext high] ext in
/-
**TensorProduct.comm_trans_comm** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ (R : Type u_1) [inst : CommSemiring R] (M : Type u_7) (N : Type u_8) [in
st_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M
] [inst_4 : _root_.Module R N],   TensorProduct.comm R N M ≪≫ₗ TensorProduct.com
m R M N = LinearEquiv.refl R (TensorProduct R N M)
参数：R : Type u_1；M : Type u_7；N : Type u_8；TensorProduct R N M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
@[simp] lemma comm_trans_comm :
    TensorProduct.comm R N M ≪≫ₗ TensorProduct.comm R M N = .refl _ _ := by
  apply LinearEquiv.toLinearMap_injective; ext; rfl
/-
**TensorProduct.comm_comp_comm** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：comm_comp_comm : (TensorProduct.comm R N M).toLinearMap ∘ₗ (TensorProduct.
comm R M N).toLinearMap = .id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.comm_trans_comm`：∀ (R : Type u_1) [inst : CommSemiring R] 
(M : Type u_7) (N : Type u_8) [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMono
id N] [inst_3 : _ro…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comm_comp_comm :
    (TensorProduct.comm R N M).toLinearMap ∘ₗ (TensorProduct.comm R M N).toLinearMap = .id := by
  simp

@[simp]
/-
**TensorProduct.comm_comp_comm_assoc** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：comm_comp_comm_assoc (f : P ->ₗ[R] M otimes[R] N) : (TensorProduct.comm R 
N M).toLinearMap ∘ₗ (TensorProduct.comm R M N).toLinearMap ∘ₗ f = f
参数：f : P ->ₗ[R] M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用引理 `TensorProduct.comm_comp_comm`：comm_comp_comm : (TensorProduct.comm R N M
).toLinearMap ∘ₗ (TensorProduct.comm R M N).toLinearMap = .id
· 使用定理 `LinearMap.id_comp`：id_comp : id.comp f = f
-/
lemma comm_comp_comm_assoc (f : P →ₗ[R] M ⊗[R] N) :
    (TensorProduct.comm R N M).toLinearMap ∘ₗ (TensorProduct.comm R M N).toLinearMap ∘ₗ f = f := by
  rw [← LinearMap.comp_assoc, comm_comp_comm, LinearMap.id_comp]
/-
**TensorProduct.comm_comm** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ (R : Type u_1) [inst : CommSemiring R] (M : Type u_7) (N : Type u_8) [in
st_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M
] [inst_4 : _root_.Module R N] (x : TensorProduct R N M),   (TensorProduct.comm 
R M N) ((TensorProduct.comm R N M) x) = x
参数：R : Type u_1；M : Type u_7；N : Type u_8；x : TensorProduct R N M；TensorProduct.
comm R M N；(TensorProduct.comm R N M) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.comm_trans_comm`：∀ (R : Type u_1) [inst : CommSemiring R] 
(M : Type u_7) (N : Type u_8) [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMono
id N] [inst_3 : _ro…
-/
@[simp] theorem comm_comm (x) :
    TensorProduct.comm R M N (TensorProduct.comm R N M x) = x :=
  congr($(comm_trans_comm _ _ _) x)

end

section CompatibleSMul

variable (R) (A S M N : Type*) [AddCommMonoid M] [AddCommMonoid N] [Module R M]
  [Module R N] [CommSemiring A] [Module A M] [Module A N] [SMulCommClass R A M]
  [CommSemiring S] [Module S M] [SMulCommClass R S M] [SMulCommClass A S M]
  [CompatibleSMul R A M N]

set_option backward.isDefEq.respectTransparency false in
/-- If M and N are both R- and A-modules and their actions on them commute,
and if the A-action on `M ⊗[R] N` can switch between the two factors, then there is a
canonical S-linear map from `M ⊗[A] N` to `M ⊗[R] N`,
where `S` is any other ring acting on `M` and whose action commutes with the `A` and `R`-actions. -/
/-
**TensorProduct.mapOfCompatibleSMul** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：mapOfCompatibleSMul : M otimes[A] N ->ₗ[S] M otimes[R] N where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If M and N are both R- and A-modules and their actions on them commute,
and if the A-action on `M ⊗[R] N` can switch between the two factors, then there
 is a
canonical S-linear map from `M ⊗[A] N` to `M ⊗[R] N`,
where `S` is any other ring acting on `M` and whose action commutes with the `A`
 and `R`-actions.
-/
def mapOfCompatibleSMul : M ⊗[A] N →ₗ[S] M ⊗[R] N where
  __ :=
    lift (σ₁₂ := RingHom.id A)
    { toFun := fun m ↦
      { __ := mk R M N m
        map_smul' := fun _ _ ↦ (smul_tmul _ _ _).symm }
      map_add' := fun _ _ ↦ LinearMap.ext <| by simp
      map_smul' := fun _ _ ↦ rfl }
  map_smul' s x := by
    induction x with
    | zero => simp
    | add x y _ _ => simp_all
    | tmul x y => simp [smul_tmul']
/-
**TensorProduct.mapOfCompatibleSMul_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduc
t`。
形式化陈述：∀ (R : Type u_1) [inst : CommSemiring R] (A : Type u_22) (S : Type u_23) (
M : Type u_24) (N : Type u_25)   [inst_1 : AddCommMonoid M] [inst_2 : AddCommMon
oid N] [inst_3 : _root_.Module R M] [inst_4 : _root_.Module R N]   [inst_5 : Com
mSemiring A] [inst_6 : _root_.Module A M] [inst_7 : _root_.Module A N] [inst_8 :
 SMulCommClass R A M]   [inst_9 : CommSemiring S] [inst_10 : _root_.Module S M] 
[inst_11 : SMulCommClass R S M]   [inst_12 : SMulCommClass A S M] [inst_13 : Ten
sorProduct.CompatibleSMul R A M N] (m : M) (n : N),   (TensorProduct.mapOfCompat
ibleSMul R A S M N) (m ⊗ₜ[A] n) = m ⊗ₜ[R] n
参数：R : Type u_1；A : Type u_22；S : Type u_23；M : Type u_24；N : Type u_25；m : M；n 
: N；TensorProduct.mapOfCompatibleSMul R A S M N；m ⊗ₜ[A] n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem mapOfCompatibleSMul_tmul (m n) : mapOfCompatibleSMul R A S M N (m ⊗ₜ n) = m ⊗ₜ n :=
  rfl

/- The map `mapOfCompatibleSMul` is surjective. Its kernel is characterized by the Lemma
`TensorProduct.ker_mapOfCompatibleSMul`. -/
/-
**TensorProduct.mapOfCompatibleSMul_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Tensor
Product`。
形式化陈述：mapOfCompatibleSMul_surjective : Function.Surjective (mapOfCompatibleSMul 
R A S M N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
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
· 使用定理 `TensorProduct.mapOfCompatibleSMul_tmul`：∀ (R : Type u_1) [inst : CommSem
iring R] (A : Type u_22) (S : Type u_23) (M : Type u_24) (N : Type u_25)   [inst
_1 : AddCommMonoid M] [inst_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
The map `mapOfCompatibleSMul` is surjective. Its kernel is characterized by the 
Lemma
`TensorProduct.ker_mapOfCompatibleSMul`.
-/
theorem mapOfCompatibleSMul_surjective : Function.Surjective (mapOfCompatibleSMul R A S M N) :=
  fun x ↦ x.induction_on (⟨0, map_zero _⟩) (fun m n ↦ ⟨_, mapOfCompatibleSMul_tmul ..⟩)
    fun _ _ ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x + y, by simpa using congr($hx + $hy)⟩

attribute [local instance] SMulCommClass.symm

@[deprecated "with (S := R)" (since := "2026-02-21")]
alias mapOfCompatibleSMul' := mapOfCompatibleSMul

/-- If the R- and A-actions on M and N satisfy `CompatibleSMul` both ways,
then `M ⊗[A] N` is canonically isomorphic to `M ⊗[R] N` as `S`-modules,
where `S` is any other ring acting on `M` and whose action commutes with the `A` and `R`-actions. -/
/-
**TensorProduct.equivOfCompatibleSMul** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：equivOfCompatibleSMul [CompatibleSMul A R M N] : M otimes[A] N ≃ₗ[S] M oti
mes[R] N where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the R- and A-actions on M and N satisfy `CompatibleSMul` both ways,
then `M ⊗[A] N` is canonically isomorphic to `M ⊗[R] N` as `S`-modules,
where `S` is any other ring acting on `M` and whose action commutes with the `A`
 and `R`-actions.
-/
def equivOfCompatibleSMul [CompatibleSMul A R M N] : M ⊗[A] N ≃ₗ[S] M ⊗[R] N where
  __ := mapOfCompatibleSMul R A S M N
  invFun := mapOfCompatibleSMul A R S M N
  left_inv x := x.induction_on (map_zero _) (fun _ _ ↦ rfl)
    fun _ _ h h' ↦ by simpa using congr($h + $h')
  right_inv x := x.induction_on (map_zero _) (fun _ _ ↦ rfl)
    fun _ _ h h' ↦ by simpa using congr($h + $h')

end CompatibleSMul

end TensorProduct

end Semiring

section Ring

variable {R : Type*} [CommSemiring R]
variable {M : Type*} {N : Type*} {P : Type*} {Q : Type*} {S : Type*}
variable [AddCommGroup M] [AddCommMonoid N] [AddCommGroup P] [AddCommMonoid Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]

namespace TensorProduct

open TensorProduct

open LinearMap

variable (R) in
/-- Auxiliary function to defining negation multiplication on tensor product. -/
/-
**TensorProduct.Neg.aux** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct.Neg`。
形式化陈述：(R : Type u_1) →   [inst : CommSemiring R] →     {M : Type u_2} →       {N
 : Type u_3} →         [inst_1 : AddCommGroup M] →           [inst_2 : AddCommMo
noid N] →             [inst_3 : _root_.Module R M] → [inst_4 : _root_.Module R N
] → TensorProduct R M N →ₗ[R] TensorProduct R M N
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary function to defining negation multiplication on tensor product.
-/
def Neg.aux : M ⊗[R] N →ₗ[R] M ⊗[R] N :=
  lift <| (mk R M N).comp (-LinearMap.id)
/-
**TensorProduct.neg** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
形式化陈述：neg : Neg (M otimes[R] N) where neg
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance neg : Neg (M ⊗[R] N) where
  neg := Neg.aux R
/-
**TensorProduct.neg_add_cancel** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Type u_2} {N : Type u_3} [in
st_1 : AddCommGroup M]   [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M]
 [inst_4 : _root_.Module R N] (x : TensorProduct R M N),   -x + x = 0
参数：x : TensorProduct R M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `TensorProduct.add_tmul`：add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) otimesₜ
 n = m₁ otimesₜ n + m₂ otimesₜ[R] n
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `_private.Mathlib.LinearAlgebra.TensorProduct.Basic.0.TensorProduct.neg_a
dd_cancel._abel_1_1`：∀ {R : Type u_3} [inst : CommSemiring R] {M : Type u_1} {N 
: Type u_2} [inst_1 : AddCommGroup M]   [inst_2 : AddCommMonoid N] [inst_3 : _ro
o…
-/
protected theorem neg_add_cancel (x : M ⊗[R] N) : -x + x = 0 :=
  x.induction_on
    (by rw [add_zero]; apply (Neg.aux R).map_zero)
    (fun x y => by convert! (add_tmul (R := R) (-x) x y).symm; rw [neg_add_cancel, zero_tmul])
    fun x y hx hy => by
    suffices -x + x + (-y + y) = 0 by
      rw [← this]
      unfold Neg.neg neg
      simp only
      rw [map_add]
      abel
    rw [hx, hy, add_zero]
/-
**TensorProduct.addCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
形式化陈述：addCommGroup : AddCommGroup (M otimes[R] N) where neg_add_cancel
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.neg_add_cancel`：∀ {R : Type u_1} [inst : CommSemiring R] {
M : Type u_2} {N : Type u_3} [inst_1 : AddCommGroup M]   [inst_2 : AddCommMonoid
 N] [inst_3 : _roo…
-/
instance addCommGroup : AddCommGroup (M ⊗[R] N) where
  neg_add_cancel := fun x => TensorProduct.neg_add_cancel x
  zsmul_zero' := by simp
  zsmul_succ' := by simp [add_comm, TensorProduct.add_smul]
  zsmul_neg' := fun n x => by
    change (-n.succ : ℤ) • x = -(((n : ℤ) + 1) • x)
    rw [← zero_add (_ • x), ← TensorProduct.neg_add_cancel ((n.succ : ℤ) • x), add_assoc,
      ← add_smul, ← sub_eq_add_neg, sub_self, zero_smul, add_zero]
    rfl
/-
**TensorProduct.neg_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：neg_tmul (m : M) (n : N) : (-m) otimesₜ n = -m otimesₜ[R] n
参数：m : M；n : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_tmul (m : M) (n : N) : (-m) ⊗ₜ n = -m ⊗ₜ[R] n :=
  rfl
/-
**TensorProduct.tmul_neg** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：tmul_neg (m : M) (p : P) : m otimesₜ (-p) = -m otimesₜ[R] p
参数：m : M；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_neg`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : 
Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M]
 [inst_…
-/
theorem tmul_neg (m : M) (p : P) : m ⊗ₜ (-p) = -m ⊗ₜ[R] p :=
  (mk R M P _).map_neg _
/-
**TensorProduct.tmul_sub** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：tmul_sub (m : M) (p₁ p₂ : P) : m otimesₜ (p₁ - p₂) = m otimesₜ[R] p₁ - m o
timesₜ[R] p₂
参数：m : M；p₁ p₂ : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_sub`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : 
Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M]
 [inst_…
-/
theorem tmul_sub (m : M) (p₁ p₂ : P) : m ⊗ₜ (p₁ - p₂) = m ⊗ₜ[R] p₁ - m ⊗ₜ[R] p₂ :=
  (mk R M P _).map_sub _ _
/-
**TensorProduct.sub_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：sub_tmul (m₁ m₂ : M) (n : N) : (m₁ - m₂) otimesₜ n = m₁ otimesₜ[R] n - m₂ 
otimesₜ[R] n
参数：m₁ m₂ : M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_sub₂`：map_sub₂ (f : M' ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P') (x y z) :
 f (x - y) z = f x z - f y z
-/
theorem sub_tmul (m₁ m₂ : M) (n : N) : (m₁ - m₂) ⊗ₜ n = m₁ ⊗ₜ[R] n - m₂ ⊗ₜ[R] n :=
  (mk R M N).map_sub₂ _ _ _

/-- While the tensor product will automatically inherit a ℤ-module structure from
`AddCommGroup.toIntModule`, that structure won't be compatible with lemmas like `tmul_smul` unless
we use a `ℤ-Module` instance provided by `TensorProduct.left_module`.

When `R` is a `Ring` we get the required `TensorProduct.compatible_smul` instance through
`IsScalarTower`, but when it is only a `Semiring` we need to build it from scratch.
The instance diamond in `compatible_smul` doesn't matter because it's in `Prop`.
-/
/-
**TensorProduct.CompatibleSMul.int** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct.Comp
atibleSMul`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Type u_2} {P : Type u_4} [in
st_1 : AddCommGroup M]   [inst_2 : AddCommGroup P] [inst_3 : _root_.Module R M] 
[inst_4 : _root_.Module R P],   TensorProduct.CompatibleSMul R ℤ M P
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.induction_on`：∀ {motive : ℤ → Prop} (i : ℤ),   motive 0 → (∀ (i : ℕ)
, motive ↑i → motive (↑i + 1)) → (∀ (i : ℕ), motive (-↑i) → motive (-↑i - 1)) → 
motive…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `TensorProduct.add_tmul`：add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) otimesₜ
 n = m₁ otimesₜ n + m₂ otimesₜ[R] n
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `TensorProduct.sub_tmul`：sub_tmul (m₁ m₂ : M) (n : N) : (m₁ - m₂) otimesₜ
 n = m₁ otimesₜ[R] n - m₂ otimesₜ[R] n
· 使用定理 `TensorProduct.tmul_sub`：tmul_sub (m : M) (p₁ p₂ : P) : m otimesₜ (p₁ - p
₂) = m otimesₜ[R] p₁ - m otimesₜ[R] p₂

--- 原说明 ---
While the tensor product will automatically inherit a ℤ-module structure from
`AddCommGroup.toIntModule`, that structure won't be compatible with lemmas like 
`tmul_smul` unless
we use a `ℤ-Module` instance provided by `TensorProduct.left_module`.

When `R` is a `Ring` we get the required `TensorProduct.compatible_smul` instanc
e through
`IsScalarTower`, but when it is only a `Semiring` we need to build it from scrat
ch.
The instance diamond in `compatible_smul` doesn't matter because it's in `Prop`.
-/
instance CompatibleSMul.int : CompatibleSMul R ℤ M P :=
  ⟨fun r m p =>
    Int.induction_on r (by simp) (fun r ih => by simpa [add_smul, tmul_add, add_tmul] using ih)
      fun r ih => by simpa [sub_smul, tmul_sub, sub_tmul] using ih⟩
/-
**TensorProduct.CompatibleSMul.unit** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct.Com
patibleSMul`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Type u_2} {N : Type u_3} [in
st_1 : AddCommGroup M]   [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M]
 [inst_4 : _root_.Module R N] {S : Type u_7}   [inst_5 : Monoid S] [inst_6 : Dis
tribMulAction S M] [inst_7 : DistribMulAction S N]   [TensorProduct.CompatibleSM
ul R S M N], TensorProduct.CompatibleSMul R Sˣ M N
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.CompatibleSMul.smul_tmul`：∀ {R : Type u_1} {R' : Type u_4}
 {inst : CommSemiring R} {inst_1 : Monoid R'} {M : Type u_7} {N : Type u_8}   {i
nst_2 : AddCommMonoid M} {in…
-/
instance CompatibleSMul.unit {S} [Monoid S] [DistribMulAction S M] [DistribMulAction S N]
    [CompatibleSMul R S M N] : CompatibleSMul R Sˣ M N :=
  ⟨fun s m n => CompatibleSMul.smul_tmul (s : S) m n⟩

end TensorProduct

end Ring

