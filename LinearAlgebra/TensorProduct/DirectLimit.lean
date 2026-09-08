/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.Algebra.Colimit.Module
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Tensor product and direct limits commute with each other.

Given a family of `R`-modules `Gᵢ` with a family of compatible `R`-linear maps `fᵢⱼ : Gᵢ → Gⱼ` for
every `i ≤ j` and another `R`-module `M`, we have `(limᵢ Gᵢ) ⊗ M` and `lim (Gᵢ ⊗ M)` are isomorphic
as `R`-modules.

## Main definitions:

* `TensorProduct.directLimitLeft : DirectLimit G f ⊗[R] M ≃ₗ[R] DirectLimit (G · ⊗[R] M) (f ▷ M)`
* `TensorProduct.directLimitRight : M ⊗[R] DirectLimit G f ≃ₗ[R] DirectLimit (M ⊗[R] G ·) (M ◁ f)`

-/

@[expose] public section

open TensorProduct Module Module.DirectLimit

variable {R : Type*} [CommSemiring R]
variable {ι : Type*}
variable [DecidableEq ι] [Preorder ι]
variable {G : ι → Type*}
variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)
variable (M : Type*) [AddCommMonoid M] [Module R M]

-- alluding to the notation in `CategoryTheory.Monoidal`
local notation M " ◁ " f => fun i j h ↦ LinearMap.lTensor M (f _ _ h)
local notation f " ▷ " N => fun i j h ↦ LinearMap.rTensor N (f _ _ h)

namespace TensorProduct

/--
the map `limᵢ (Gᵢ ⊗ M) → (limᵢ Gᵢ) ⊗ M` induced by the family of maps `Gᵢ ⊗ M → (limᵢ Gᵢ) ⊗ M`
given by `gᵢ ⊗ m ↦ [gᵢ] ⊗ m`.
-/
/-
**TensorProduct.fromDirectLimit** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：fromDirectLimit : DirectLimit (G · otimes[R] M) (f ▷ M) ->ₗ[R] DirectLimit
 G f otimes[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the map `limᵢ (Gᵢ ⊗ M) → (limᵢ Gᵢ) ⊗ M` induced by the family of maps `Gᵢ ⊗ M → 
(limᵢ Gᵢ) ⊗ M`
given by `gᵢ ⊗ m ↦ [gᵢ] ⊗ m`.
-/
noncomputable def fromDirectLimit :
    DirectLimit (G · ⊗[R] M) (f ▷ M) →ₗ[R] DirectLimit G f ⊗[R] M :=
  Module.DirectLimit.lift _ _ _ _ (fun _ ↦ (of _ _ _ _ _).rTensor M)
    fun _ _ _ x ↦ by refine x.induction_on ?_ ?_ ?_ <;> aesop

variable {M} in
/-
**TensorProduct.fromDirectLimit_of_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct
`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {ι : Type u_2} [inst_1 : Decidabl
eEq ι] [inst_2 : Preorder ι]   {G : ι → Type u_3} [inst_3 : (i : ι) → AddCommMon
oid (G i)] [inst_4 : (i : ι) → _root_.Module R (G i)]   (f : (i j : ι) → i ≤ j →
 G i →ₗ[R] G j) {M : Type u_4} [inst_5 : AddCommMonoid M] [inst_6 : _root_.Modul
e R M] {i : ι}   (g : G i) (m : M),   (TensorProduct.fromDirectLimit f M)       
((Module.DirectLimit.of R ι (fun x => TensorProduct R (G x) M) (fun i j h => Lin
earMap.rTensor M (f i j h)) i)         (g ⊗ₜ[R] m)) =     (Module.DirectLimit.of
 R ι G f i) g ⊗ₜ[R] m
参数：i : ι；G i；i : ι；G i；f : (i j : ι) → i ≤ j → G i →ₗ[R] G j；g : G i；m : M；Tenso
rProduct.fromDirectLimit f M；(Module.DirectLimit.of R ι (fun x => TensorProduct 
R (G x) M) (fun i j h => LinearMap.rTensor M (f i j h)) i)         (g ⊗ₜ[R] m)；M
odule.DirectLimit.of R ι G f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.DirectLimit.lift_of`：∀ {R : Type u_1} [inst : Semiring R] {ι : Ty
pe u_2} [inst_1 : Preorder ι] {G : ι → Type u_3}   [inst_2 : (i : ι) → AddCommMo
noid (G i)] [ins…
-/
@[simp] lemma fromDirectLimit_of_tmul {i : ι} (g : G i) (m : M) :
    fromDirectLimit f M (of _ _ _ _ i (g ⊗ₜ m)) = (of _ _ _ f i g) ⊗ₜ m :=
  lift_of (G := (G · ⊗[R] M)) _ _ (g ⊗ₜ m)

/--
the map `(limᵢ Gᵢ) ⊗ M → limᵢ (Gᵢ ⊗ M)` from the bilinear map `limᵢ Gᵢ → M → limᵢ (Gᵢ ⊗ M)` given
by the family of maps `Gᵢ → M → limᵢ (Gᵢ ⊗ M)` where `gᵢ ↦ m ↦ [gᵢ ⊗ m]`
-/
/-
**TensorProduct.toDirectLimit** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：toDirectLimit : DirectLimit G f otimes[R] M ->ₗ[R] DirectLimit (G · otimes
[R] M) (f ▷ M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the map `(limᵢ Gᵢ) ⊗ M → limᵢ (Gᵢ ⊗ M)` from the bilinear map `limᵢ Gᵢ → M → lim
ᵢ (Gᵢ ⊗ M)` given
by the family of maps `Gᵢ → M → limᵢ (Gᵢ ⊗ M)` where `gᵢ ↦ m ↦ [gᵢ ⊗ m]`
-/
noncomputable def toDirectLimit : DirectLimit G f ⊗[R] M →ₗ[R] DirectLimit (G · ⊗[R] M) (f ▷ M) :=
  TensorProduct.lift <| Module.DirectLimit.lift _ _ _ _
    (fun i ↦
      (TensorProduct.mk R _ _).compr₂ (of R ι _ (fun _i _j h ↦ (f _ _ h).rTensor M) i))
    fun _ _ _ g ↦ DFunLike.ext _ _ (of_f (G := (G · ⊗[R] M)) (x := g ⊗ₜ ·))

variable {M} in
/-
**TensorProduct.toDirectLimit_tmul_of** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {ι : Type u_2} [inst_1 : Decidabl
eEq ι] [inst_2 : Preorder ι]   {G : ι → Type u_3} [inst_3 : (i : ι) → AddCommMon
oid (G i)] [inst_4 : (i : ι) → _root_.Module R (G i)]   (f : (i j : ι) → i ≤ j →
 G i →ₗ[R] G j) {M : Type u_4} [inst_5 : AddCommMonoid M] [inst_6 : _root_.Modul
e R M] {i : ι}   (g : G i) (m : M),   (TensorProduct.toDirectLimit f M) ((Module
.DirectLimit.of R ι G f i) g ⊗ₜ[R] m) =     (Module.DirectLimit.of R ι (fun x =>
 TensorProduct R (G x) M) (fun i j h => LinearMap.rTensor M (f i j h)) i)       
(g ⊗ₜ[R] m)
参数：i : ι；G i；i : ι；G i；f : (i j : ι) → i ≤ j → G i →ₗ[R] G j；g : G i；m : M；Tenso
rProduct.toDirectLimit f M；(Module.DirectLimit.of R ι G f i) g ⊗ₜ[R] m；Module.Di
rectLimit.of R ι (fun x => TensorProduct R (G x) M) (fun i j h => LinearMap.rTen
sor M (f i j h)) i；g ⊗ₜ[R] m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.toDirectLimit.eq_1`：∀ {R : Type u_1} [inst : CommSemiring 
R] {ι : Type u_2} [inst_1 : DecidableEq ι] [inst_2 : Preorder ι]   {G : ι → Type
 u_3} [inst_3 : (i : ι…
· 使用定理 `TensorProduct.lift.tmul`：∀ {R : Type u_1} {R₂ : Type u_2} [inst : CommSe
miring R] [inst_1 : CommSemiring R₂] {σ₁₂ : R →+* R₂} {M : Type u_7}   {N : Type
 u_8} {P₂ : T…
· 使用定理 `Module.DirectLimit.lift_of`：∀ {R : Type u_1} [inst : Semiring R] {ι : Ty
pe u_2} [inst_1 : Preorder ι] {G : ι → Type u_3}   [inst_2 : (i : ι) → AddCommMo
noid (G i)] [ins…
-/
@[simp] lemma toDirectLimit_tmul_of
    {i : ι} (g : G i) (m : M) :
    (toDirectLimit f M <| (of _ _ G f i g) ⊗ₜ m) = (of _ _ _ _ i (g ⊗ₜ m)) := by
  rw [toDirectLimit, lift.tmul, lift_of]
  rfl

attribute [local ext] TensorProduct.ext in
/--
`limᵢ (Gᵢ ⊗ M)` and `(limᵢ Gᵢ) ⊗ M` are isomorphic as modules
-/
/-
**TensorProduct.directLimitLeft** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：directLimitLeft : DirectLimit G f otimes[R] M ≃ₗ[R] DirectLimit (G · otime
s[R] M) (f ▷ M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`limᵢ (Gᵢ ⊗ M)` and `(limᵢ Gᵢ) ⊗ M` are isomorphic as modules
-/
noncomputable def directLimitLeft :
    DirectLimit G f ⊗[R] M ≃ₗ[R] DirectLimit (G · ⊗[R] M) (f ▷ M) :=
  LinearEquiv.ofLinearMap (toDirectLimit f M) (fromDirectLimit f M) (by ext; simp) (by ext; simp)
/-
**TensorProduct.directLimitLeft_tmul_of** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct
`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {ι : Type u_2} [inst_1 : Decidabl
eEq ι] [inst_2 : Preorder ι]   {G : ι → Type u_3} [inst_3 : (i : ι) → AddCommMon
oid (G i)] [inst_4 : (i : ι) → _root_.Module R (G i)]   (f : (i j : ι) → i ≤ j →
 G i →ₗ[R] G j) (M : Type u_4) [inst_5 : AddCommMonoid M] [inst_6 : _root_.Modul
e R M] {i : ι}   (g : G i) (m : M),   (TensorProduct.directLimitLeft f M) ((Modu
le.DirectLimit.of R ι G f i) g ⊗ₜ[R] m) =     (Module.DirectLimit.of R ι (fun i 
=> TensorProduct R (G i) M) (fun i j h => LinearMap.rTensor M (f i j h)) i)     
  (g ⊗ₜ[R] m)
参数：i : ι；G i；i : ι；G i；f : (i j : ι) → i ≤ j → G i →ₗ[R] G j；M : Type u_4；g : G 
i；m : M；TensorProduct.directLimitLeft f M；(Module.DirectLimit.of R ι G f i) g ⊗ₜ
[R] m；Module.DirectLimit.of R ι (fun i => TensorProduct R (G i) M) (fun i j h =>
 LinearMap.rTensor M (f i j h)) i；g ⊗ₜ[R] m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.toDirectLimit_tmul_of`：∀ {R : Type u_1} [inst : CommSemiri
ng R] {ι : Type u_2} [inst_1 : DecidableEq ι] [inst_2 : Preorder ι]   {G : ι → T
ype u_3} [inst_3 : (i : ι…
-/
@[simp] lemma directLimitLeft_tmul_of {i : ι} (g : G i) (m : M) :
    directLimitLeft f M (of _ _ _ _ _ g ⊗ₜ m) = of _ _ _ (f ▷ M) _ (g ⊗ₜ m) :=
  toDirectLimit_tmul_of f g m
/-
**TensorProduct.directLimitLeft_symm_of_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorPr
oduct`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {ι : Type u_2} [inst_1 : Decidabl
eEq ι] [inst_2 : Preorder ι]   {G : ι → Type u_3} [inst_3 : (i : ι) → AddCommMon
oid (G i)] [inst_4 : (i : ι) → _root_.Module R (G i)]   (f : (i j : ι) → i ≤ j →
 G i →ₗ[R] G j) (M : Type u_4) [inst_5 : AddCommMonoid M] [inst_6 : _root_.Modul
e R M] {i : ι}   (g : G i) (m : M),   (TensorProduct.directLimitLeft f M).symm  
     ((Module.DirectLimit.of R ι (fun x => TensorProduct R (G x) M) (fun i j h =
> LinearMap.rTensor M (f i j h)) i)         (g ⊗ₜ[R] m)) =     (Module.DirectLim
it.of R ι G f i) g ⊗ₜ[R] m
参数：i : ι；G i；i : ι；G i；f : (i j : ι) → i ≤ j → G i →ₗ[R] G j；M : Type u_4；g : G 
i；m : M；TensorProduct.directLimitLeft f M；(Module.DirectLimit.of R ι (fun x => T
ensorProduct R (G x) M) (fun i j h => LinearMap.rTensor M (f i j h)) i)         
(g ⊗ₜ[R] m)；Module.DirectLimit.of R ι G f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.fromDirectLimit_of_tmul`：∀ {R : Type u_1} [inst : CommSemi
ring R] {ι : Type u_2} [inst_1 : DecidableEq ι] [inst_2 : Preorder ι]   {G : ι →
 Type u_3} [inst_3 : (i : ι…
-/
@[simp] lemma directLimitLeft_symm_of_tmul {i : ι} (g : G i) (m : M) :
    (directLimitLeft f M).symm (of _ _ _ _ _ (g ⊗ₜ m)) = of _ _ _ f _ g ⊗ₜ m :=
  fromDirectLimit_of_tmul f g m
/-
**TensorProduct.directLimitLeft_rTensor_of** 是 Mathlib 中的一个引理，位于命名空间 `TensorProd
uct`。
形式化陈述：directLimitLeft_rTensor_of {i : ι} (x : G i otimes[R] M) : directLimitLeft
 f M (LinearMap.rTensor M (of ..) x) = of _ _ _ (f ▷ M) _ x
参数：x : G i otimes[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.directLimitLeft_tmul_of`：∀ {R : Type u_1} [inst : CommSemi
ring R] {ι : Type u_2} [inst_1 : DecidableEq ι] [inst_2 : Preorder ι]   {G : ι →
 Type u_3} [inst_3 : (i : ι…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
lemma directLimitLeft_rTensor_of {i : ι} (x : G i ⊗[R] M) :
    directLimitLeft f M (LinearMap.rTensor M (of ..) x) = of _ _ _ (f ▷ M) _ x :=
  x.induction_on (by simp) (by simp +contextual) (by simp +contextual)

/--
`M ⊗ (limᵢ Gᵢ)` and `limᵢ (M ⊗ Gᵢ)` are isomorphic as modules
-/
/-
**TensorProduct.directLimitRight** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：directLimitRight : M otimes[R] DirectLimit G f ≃ₗ[R] DirectLimit (M otimes
[R] G ·) (M ◁ f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M ⊗ (limᵢ Gᵢ)` and `limᵢ (M ⊗ Gᵢ)` are isomorphic as modules
-/
noncomputable def directLimitRight :
    M ⊗[R] DirectLimit G f ≃ₗ[R] DirectLimit (M ⊗[R] G ·) (M ◁ f) :=
  TensorProduct.comm _ _ _ ≪≫ₗ directLimitLeft f M ≪≫ₗ
    Module.DirectLimit.congr (fun _ ↦ TensorProduct.comm _ _ _)
      (fun i j h ↦ TensorProduct.ext <| DFunLike.ext _ _ <| by aesop)
/-
**TensorProduct.directLimitRight_tmul_of** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduc
t`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {ι : Type u_2} [inst_1 : Decidabl
eEq ι] [inst_2 : Preorder ι]   {G : ι → Type u_3} [inst_3 : (i : ι) → AddCommMon
oid (G i)] [inst_4 : (i : ι) → _root_.Module R (G i)]   (f : (i j : ι) → i ≤ j →
 G i →ₗ[R] G j) (M : Type u_4) [inst_5 : AddCommMonoid M] [inst_6 : _root_.Modul
e R M] {i : ι}   (m : M) (g : G i),   (TensorProduct.directLimitRight f M) (m ⊗ₜ
[R] (Module.DirectLimit.of R ι G f i) g) =     (Module.DirectLimit.of R ι (fun x
 => TensorProduct R M (G x)) (fun i j h => LinearMap.lTensor M (f i j h)) i)    
   (m ⊗ₜ[R] g)
参数：i : ι；G i；i : ι；G i；f : (i j : ι) → i ≤ j → G i →ₗ[R] G j；M : Type u_4；m : M；
g : G i；TensorProduct.directLimitRight f M；m ⊗ₜ[R] (Module.DirectLimit.of R ι G 
f i) g；Module.DirectLimit.of R ι (fun x => TensorProduct R M (G x)) (fun i j h =
> LinearMap.lTensor M (f i j h)) i；m ⊗ₜ[R] g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.directLimitLeft_tmul_of`：∀ {R : Type u_1} [inst : CommSemi
ring R] {ι : Type u_2} [inst_1 : DecidableEq ι] [inst_2 : Preorder ι]   {G : ι →
 Type u_3} [inst_3 : (i : ι…
· 使用引理 `Module.DirectLimit.congr_apply_of`：congr_apply_of (e : (i : ι) -> G i ≃ₗ
[R] G' i) (he : forall i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ e i) {i : ι} (g : G i
) : congr e he (of _ _ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma directLimitRight_tmul_of {i : ι} (m : M) (g : G i) :
    directLimitRight f M (m ⊗ₜ of _ _ _ _ _ g) = of _ _ _ _ i (m ⊗ₜ g) := by
  simp [directLimitRight, congr_apply_of]
/-
**TensorProduct.directLimitRight_symm_of_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorP
roduct`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {ι : Type u_2} [inst_1 : Decidabl
eEq ι] [inst_2 : Preorder ι]   {G : ι → Type u_3} [inst_3 : (i : ι) → AddCommMon
oid (G i)] [inst_4 : (i : ι) → _root_.Module R (G i)]   (f : (i j : ι) → i ≤ j →
 G i →ₗ[R] G j) (M : Type u_4) [inst_5 : AddCommMonoid M] [inst_6 : _root_.Modul
e R M] {i : ι}   (m : M) (g : G i),   (TensorProduct.directLimitRight f M).symm 
      ((Module.DirectLimit.of R ι (fun x => TensorProduct R M (G x)) (fun i j h 
=> LinearMap.lTensor M (f i j h)) i)         (m ⊗ₜ[R] g)) =     m ⊗ₜ[R] (Module.
DirectLimit.of R ι G f i) g
参数：i : ι；G i；i : ι；G i；f : (i j : ι) → i ≤ j → G i →ₗ[R] G j；M : Type u_4；m : M；
g : G i；TensorProduct.directLimitRight f M；(Module.DirectLimit.of R ι (fun x => 
TensorProduct R M (G x)) (fun i j h => LinearMap.lTensor M (f i j h)) i)        
 (m ⊗ₜ[R] g)；Module.DirectLimit.of R ι G f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.DirectLimit.congr_symm_apply_of`：congr_symm_apply_of (e : (i : ι)
 -> G i ≃ₗ[R] G' i) (he : forall i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ e i) {i : ι
} (g : G' i) : (congr e he).…
· 使用定理 `TensorProduct.directLimitLeft_symm_of_tmul`：∀ {R : Type u_1} [inst : Com
mSemiring R] {ι : Type u_2} [inst_1 : DecidableEq ι] [inst_2 : Preorder ι]   {G 
: ι → Type u_3} [inst_3 : (i : ι…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma directLimitRight_symm_of_tmul {i : ι} (m : M) (g : G i) :
    (directLimitRight f M).symm (of _ _ _ _ _ (m ⊗ₜ g)) = m ⊗ₜ of _ _ _ f _ g := by
  simp [directLimitRight, congr_symm_apply_of]

variable [DirectedSystem G (f · · ·)]
/-
**TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DirectedSystem (G · ⊗[R] M) (f ▷ M) where
  map_self i x := by
    convert! LinearMap.rTensor_id_apply M (G i) x; ext; apply DirectedSystem.map_self'
  map_map _ _ _ _ _ x := by
    convert! ← (LinearMap.rTensor_comp_apply M _ _ x).symm; ext; apply DirectedSystem.map_map' f
/-
**TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DirectedSystem (M ⊗[R] G ·) (M ◁ f) where
  map_self i x := by
    convert! LinearMap.lTensor_id_apply M _ x; ext; apply DirectedSystem.map_self'
  map_map _ _ _ h₁ h₂ x := by
    convert! ← (LinearMap.lTensor_comp_apply M _ _ x).symm; ext; apply DirectedSystem.map_map' f

end TensorProduct

