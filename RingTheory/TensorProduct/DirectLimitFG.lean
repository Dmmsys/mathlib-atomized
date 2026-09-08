/-
Copyright (c) 2025 Antoine Chambert-Loir and María-Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María-Inés de Frutos Fernández
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Adjoin.FG

/-! # Tensor products and finitely generated submodules

Various results about how tensor products of arbitrary modules are direct limits of
tensor products of finitely-generated modules.

## Main definitions

* `Submodule.FG.directedSystem`, the directed system of finitely generated submodules of a module.

* `Submodule.FG.directLimit` proves that a module is the direct limit
  of its finitely generated submodules, with respect to the inclusion maps

* `DirectedSystem.rTensor`, the directed system deduced from a directed system of modules
  by applying `rTensor`.

* `Submodule.FG.rTensor.directSystem`, the directed system of
  modules `P ⊗[R] N`, for all finitely generated
  submodules `P`, with respect to the maps deduced from the inclusions

* `Submodule.FG.rTensor.directLimit` : a tensor product `M ⊗[R] N` is the direct limit
  of the modules `P ⊗[R] N`, where `P` ranges over all finitely generated submodules of `M`,
  as a linear equivalence.

* `DirectedSystem.lTensor`, the directed system deduced from a directed system of modules
  by applying `lTensor`.

* `Submodule.FG.lTensor.directSystem`, the directed system of
  modules `M ⊗[R] Q`, for all finitely generated
  submodules `Q`, with respect to the maps deduced from the inclusions

* `Submodule.FG.lTensor.directLimit` : a tensor product `M ⊗[R] N` is the direct limit
  of the modules `M ⊗[R] Q`, where `Q` ranges over all finitely generated submodules of `N`,
  as a linear equivalence.
-/

@[expose] public section

open Submodule LinearMap

section Semiring

universe u v
variable {R : Type u} [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The directed system of finitely generated submodules of `M` -/
/-
**Submodule.FG.directedSystem** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Submodule.FG.directedSystem : DirectedSystem (ι
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
The directed system of finitely generated submodules of `M`
-/
instance Submodule.FG.directedSystem :
    DirectedSystem (ι := {P : Submodule R M // P.FG}) (F := fun P ↦ P.val)
    (f := fun ⦃P Q⦄ (h : P ≤ Q) ↦ Submodule.inclusion h) where
  map_self := fun _ _ ↦ rfl
  map_map  := fun _ _ _ _ _ _ ↦ rfl

set_option backward.isDefEq.respectTransparency.types false in
variable (R M) in
/-- Any module is the direct limit of its finitely generated submodules -/
/-
**Submodule.FG.directLimit** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.FG.directLimit [DecidableEq {P : Submodule R M // P.FG}] : Modul
e.DirectLimit (ι
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any module is the direct limit of its finitely generated submodules
-/
noncomputable def Submodule.FG.directLimit [DecidableEq {P : Submodule R M // P.FG}] :
    Module.DirectLimit (ι := {P : Submodule R M // P.FG}) (G := fun P ↦ P.val)
      (fun ⦃P Q⦄ (h : P ≤ Q) ↦ Submodule.inclusion h) ≃ₗ[R] M :=
  LinearEquiv.ofBijective
    (Module.DirectLimit.lift _ _ _ _ (fun P ↦ P.val.subtype) (fun _ _ _ _ ↦ rfl))
    ⟨Module.DirectLimit.lift_injective _ _ (fun P ↦ Submodule.injective_subtype P.val),
      fun x ↦ ⟨Module.DirectLimit.of _ {P : Submodule R M // P.FG} _ _
          ⟨Submodule.span R {x}, Submodule.fg_span_singleton x⟩
          ⟨x, Submodule.mem_span_singleton_self x⟩,
         by simp⟩⟩

end Semiring

section TensorProducts

open TensorProduct

universe u v

variable (R : Type u) (M N : Type*)
  [CommSemiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- Given a directed system of `R`-modules, tensoring it on the right gives a directed system -/
/-
**DirectedSystem.rTensor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirectedSystem.rTensor {ι : Type*} [Preorder ι] {F : ι -> Type*} [forall i
, AddCommMonoid (F i)] [forall i, Module R (F i)] {f : ⦃i j : ι⦄ -> i <= j -> F 
i ->ₗ[R] F j} (D : DirectedSystem F (fun _ _ h => f h)) : DirectedSystem (fun i 
=> (F i) otimes[R] N) (fun _ _ h => rTensor N (f h)) where map_self i t
参数：F i；F i；D : DirectedSystem F (fun _ _ h => f h)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.id_apply`：id_apply (x : M) : @id R M _ _ _ x = x
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `DirectedSystem.map_self`：∀ {ι : Type u_1} {inst : Preorder ι} {F : ι → T
ype u_4} {f : ⦃i j : ι⦄ → i ≤ j → F i → F j} [self : DirectedSystem F f]   ⦃i : 
ι⦄ (x : F i),…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `LinearMap.rTensor_comp`：rTensor_comp : (g.comp f).rTensor M = (g.rTensor
 M).comp (f.rTensor M)
· 使用定理 `DirectedSystem.map_map`：∀ {ι : Type u_1} {inst : Preorder ι} {F : ι → Ty
pe u_4} {f : ⦃i j : ι⦄ → i ≤ j → F i → F j} [self : DirectedSystem F f]   ⦃k j i
 : ι⦄ (hij :…

--- 原说明 ---
Given a directed system of `R`-modules, tensoring it on the right gives a direct
ed system
-/
theorem DirectedSystem.rTensor {ι : Type*} [Preorder ι] {F : ι → Type*}
    [∀ i, AddCommMonoid (F i)] [∀ i, Module R (F i)] {f : ⦃i j : ι⦄ → i ≤ j → F i →ₗ[R] F j}
    (D : DirectedSystem F (fun _ _ h ↦ f h)) :
    DirectedSystem (fun i ↦ (F i) ⊗[R] N) (fun _ _ h ↦ rTensor N (f h)) where
  map_self i t := by
    rw [← id_apply (R := R) t]
    apply DFunLike.congr_fun
    ext m n
    simp [D.map_self]
  map_map {i j k} h h' t := by
    rw [← comp_apply, ← rTensor_comp]
    apply DFunLike.congr_fun
    ext p n
    simp [D.map_map]

/-- When `P` ranges over finitely generated submodules of `M`,
  the modules of the form `P ⊗[R] N` form a directed system. -/
/-
**Submodule.FG.rTensor.directedSystem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.FG.rTensor.directedSystem : DirectedSystem (ι
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectedSystem.rTensor`：DirectedSystem.rTensor {ι : Type*} [Preorder ι] 
{F : ι -> Type*} [forall i, AddCommMonoid (F i)] [forall i, Module R (F i)] {f :
 ⦃i j : ι⦄ -…

--- 原说明 ---
When `P` ranges over finitely generated submodules of `M`,
  the modules of the form `P ⊗[R] N` form a directed system.
-/
theorem Submodule.FG.rTensor.directedSystem :
    DirectedSystem (ι := {P : Submodule R M // P.FG}) (fun P ↦ P.val ⊗[R] N)
    (fun ⦃_ _⦄ h ↦ rTensor N (Submodule.inclusion h)) :=
  Submodule.FG.directedSystem.rTensor R N

/-- A tensor product `M ⊗[R] N` is the direct limit of the modules `P ⊗[R] N`,
where `P` ranges over all finitely generated submodules of `M`, as a linear equivalence. -/
/-
**Submodule.FG.rTensor.directLimit** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.FG.rTensor.directLimit [DecidableEq {P : Submodule R M // P.FG}]
 : Module.DirectLimit (R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A tensor product `M ⊗[R] N` is the direct limit of the modules `P ⊗[R] N`,
where `P` ranges over all finitely generated submodules of `M`, as a linear equi
valence.
-/
noncomputable def Submodule.FG.rTensor.directLimit [DecidableEq {P : Submodule R M // P.FG}] :
    Module.DirectLimit (R := R) (ι := {P : Submodule R M // P.FG}) (fun P ↦ P.val ⊗[R] N)
      (fun ⦃P Q⦄ (h : P ≤ Q) ↦ (Submodule.inclusion h).rTensor N) ≃ₗ[R] M ⊗[R] N :=
  (TensorProduct.directLimitLeft _ N).symm.trans ((Submodule.FG.directLimit R M).rTensor N)

set_option backward.isDefEq.respectTransparency.types false in
/-
**Submodule.FG.rTensor.directLimit_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.FG.rTensor.directLimit_apply [DecidableEq {P : Submodule R M // 
P.FG}] {P : {P : Submodule R M // P.FG}} (u : P otimes[R] N) : (Submodule.FG.rTe
nsor.directLimit R M N) ((Module.DirectLimit.of R {P : Submodule R M // P.FG} (f
un P => P.val otimes[R] N) (fun ⦃_ _⦄ h => (Submodule.inclusion h).rTensor N) P)
 u) = (rTensor N (Submodule.subtype P)) u
参数：u : P otimes[R] N。
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
· 使用定理 `TensorProduct.directLimitLeft_symm_of_tmul`：∀ {R : Type u_1} [inst : Com
mSemiring R] {ι : Type u_2} [inst_1 : DecidableEq ι] [inst_2 : Preorder ι]   {G 
: ι → Type u_3} [inst_3 : (i : ι…
· 使用定理 `Module.DirectLimit.lift_of`：∀ {R : Type u_1} [inst : Semiring R] {ι : Ty
pe u_2} [inst_1 : Preorder ι] {G : ι → Type u_3}   [inst_2 : (i : ι) → AddCommMo
noid (G i)] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem Submodule.FG.rTensor.directLimit_apply [DecidableEq {P : Submodule R M // P.FG}]
    {P : {P : Submodule R M // P.FG}} (u : P ⊗[R] N) :
    (Submodule.FG.rTensor.directLimit R M N)
      ((Module.DirectLimit.of R {P : Submodule R M // P.FG} (fun P ↦ P.val ⊗[R] N)
        (fun ⦃_ _⦄ h ↦ (Submodule.inclusion h).rTensor N) P) u)
      = (rTensor N (Submodule.subtype P)) u := by
  suffices (Submodule.FG.rTensor.directLimit R M N).toLinearMap.comp
      (Module.DirectLimit.of R {P : Submodule R M // P.FG} (fun P ↦ P.val ⊗[R] N)
        (fun _ _ hPQ ↦ rTensor N (Submodule.inclusion hPQ)) P)
      = rTensor N (Submodule.subtype P.val) by
    exact DFunLike.congr_fun this u
  ext p n
  simp [Submodule.FG.rTensor.directLimit, Submodule.FG.directLimit]

/-- An alternative version to `Submodule.FG.rTensor.directLimit_apply`. -/
/-
**Submodule.FG.rTensor.directLimit_apply'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.FG.rTensor.directLimit_apply' [DecidableEq {P : Submodule R M //
 P.FG}] {P : Submodule R M} (hP : Submodule.FG P) (u : P otimes[R] N) : (Submodu
le.FG.rTensor.directLimit R M N) ((Module.DirectLimit.of R {P : Submodule R M //
 P.FG} (fun P => P.val otimes[R] N) (fun ⦃_ _⦄ h => rTensor N (Submodule.inclusi
on h)) ⟨P, hP⟩) u) = (rTensor N (Submodule.subtype P)) u
参数：hP : Submodule.FG P；u : P otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.FG.rTensor.directLimit_apply`：Submodule.FG.rTensor.directLimit
_apply [DecidableEq {P : Submodule R M // P.FG}] {P : {P : Submodule R M // P.FG
}} (u : P otimes[R] N) : (Su…

--- 原说明 ---
An alternative version to `Submodule.FG.rTensor.directLimit_apply`.
-/
theorem Submodule.FG.rTensor.directLimit_apply' [DecidableEq {P : Submodule R M // P.FG}]
    {P : Submodule R M} (hP : Submodule.FG P) (u : P ⊗[R] N) :
    (Submodule.FG.rTensor.directLimit R M N)
      ((Module.DirectLimit.of R {P : Submodule R M // P.FG} (fun P ↦ P.val ⊗[R] N)
        (fun ⦃_ _⦄ h ↦ rTensor N (Submodule.inclusion h)) ⟨P, hP⟩) u)
      = (rTensor N (Submodule.subtype P)) u := by
  apply Submodule.FG.rTensor.directLimit_apply

/-- Given a directed system of `R`-modules, tensoring it on the left gives a directed system -/
/-
**DirectedSystem.lTensor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirectedSystem.lTensor {ι : Type*} [Preorder ι] {F : ι -> Type*} [forall i
, AddCommMonoid (F i)] [forall i, Module R (F i)] {f : ⦃i j : ι⦄ -> i <= j -> F 
i ->ₗ[R] F j} (D : DirectedSystem F (fun _ _ h => f h)) : DirectedSystem (fun i 
=> M otimes[R] (F i)) (fun _ _ h => lTensor M (f h)) where map_self i t
参数：F i；F i；D : DirectedSystem F (fun _ _ h => f h)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.id_apply`：id_apply (x : M) : @id R M _ _ _ x = x
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `DirectedSystem.map_self`：∀ {ι : Type u_1} {inst : Preorder ι} {F : ι → T
ype u_4} {f : ⦃i j : ι⦄ → i ≤ j → F i → F j} [self : DirectedSystem F f]   ⦃i : 
ι⦄ (x : F i),…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `LinearMap.lTensor_comp`：lTensor_comp : (g.comp f).lTensor M = (g.lTensor
 M).comp (f.lTensor M)
· 使用定理 `DirectedSystem.map_map`：∀ {ι : Type u_1} {inst : Preorder ι} {F : ι → Ty
pe u_4} {f : ⦃i j : ι⦄ → i ≤ j → F i → F j} [self : DirectedSystem F f]   ⦃k j i
 : ι⦄ (hij :…

--- 原说明 ---
Given a directed system of `R`-modules, tensoring it on the left gives a directe
d system
-/
theorem DirectedSystem.lTensor {ι : Type*} [Preorder ι] {F : ι → Type*}
    [∀ i, AddCommMonoid (F i)] [∀ i, Module R (F i)] {f : ⦃i j : ι⦄ → i ≤ j → F i →ₗ[R] F j}
    (D : DirectedSystem F (fun _ _ h ↦ f h)) :
    DirectedSystem (fun i ↦ M ⊗[R] (F i)) (fun _ _ h ↦ lTensor M (f h)) where
  map_self i t := by
    rw [← id_apply (R := R) t]
    apply DFunLike.congr_fun
    ext m n
    simp [D.map_self]
  map_map {i j k} h h' t := by
    rw [← comp_apply, ← lTensor_comp]
    apply DFunLike.congr_fun
    ext p n
    simp [D.map_map]

/-- When `Q` ranges over finitely generated submodules of `N`,
  the modules of the form `M ⊗[R] Q` form a directed system. -/
/-
**Submodule.FG.lTensor.directedSystem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.FG.lTensor.directedSystem : DirectedSystem (ι
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectedSystem.lTensor`：DirectedSystem.lTensor {ι : Type*} [Preorder ι] 
{F : ι -> Type*} [forall i, AddCommMonoid (F i)] [forall i, Module R (F i)] {f :
 ⦃i j : ι⦄ -…

--- 原说明 ---
When `Q` ranges over finitely generated submodules of `N`,
  the modules of the form `M ⊗[R] Q` form a directed system.
-/
theorem Submodule.FG.lTensor.directedSystem :
    DirectedSystem (ι := {Q : Submodule R N // Q.FG}) (fun Q ↦ M ⊗[R] Q.val)
      (fun _ _ hPQ ↦ lTensor M (Submodule.inclusion hPQ)) :=
  Submodule.FG.directedSystem.lTensor R M

/-- A tensor product `M ⊗[R] N` is the direct limit of the modules `M ⊗[R] Q`,
where `Q` ranges over all finitely generated submodules of `N`, as a linear equivalence. -/
/-
**Submodule.FG.lTensor.directLimit** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.FG.lTensor.directLimit [DecidableEq {Q : Submodule R N // Q.FG}]
 : Module.DirectLimit (R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A tensor product `M ⊗[R] N` is the direct limit of the modules `M ⊗[R] Q`,
where `Q` ranges over all finitely generated submodules of `N`, as a linear equi
valence.
-/
noncomputable def Submodule.FG.lTensor.directLimit [DecidableEq {Q : Submodule R N // Q.FG}] :
    Module.DirectLimit (R := R) (ι := {Q : Submodule R N // Q.FG}) (fun Q ↦ M ⊗[R] Q.val)
      (fun _ _ hPQ ↦ (inclusion hPQ).lTensor M) ≃ₗ[R] M ⊗[R] N :=
  (TensorProduct.directLimitRight _ M).symm.trans ((Submodule.FG.directLimit R N).lTensor M)

set_option backward.isDefEq.respectTransparency.types false in
/-
**Submodule.FG.lTensor.directLimit_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.FG.lTensor.directLimit_apply [DecidableEq {P : Submodule R N // 
P.FG}] (Q : {Q : Submodule R N // Q.FG}) (u : M otimes[R] Q.val) : (Submodule.FG
.lTensor.directLimit R M N) ((Module.DirectLimit.of R {Q : Submodule R N // Q.FG
} (fun Q => M otimes[R] Q.val) (fun _ _ hPQ => (inclusion hPQ).lTensor M) Q) u) 
= (lTensor M (Submodule.subtype Q.val)) u
参数：Q : {Q : Submodule R N // Q.FG}；u : M otimes[R] Q.val。
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
· 使用定理 `TensorProduct.directLimitRight_symm_of_tmul`：∀ {R : Type u_1} [inst : Co
mmSemiring R] {ι : Type u_2} [inst_1 : DecidableEq ι] [inst_2 : Preorder ι]   {G
 : ι → Type u_3} [inst_3 : (i : ι…
· 使用定理 `Module.DirectLimit.lift_of`：∀ {R : Type u_1} [inst : Semiring R] {ι : Ty
pe u_2} [inst_1 : Preorder ι] {G : ι → Type u_3}   [inst_2 : (i : ι) → AddCommMo
noid (G i)] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem Submodule.FG.lTensor.directLimit_apply [DecidableEq {P : Submodule R N // P.FG}]
    (Q : {Q : Submodule R N // Q.FG}) (u : M ⊗[R] Q.val) :
    (Submodule.FG.lTensor.directLimit R M N)
      ((Module.DirectLimit.of R {Q : Submodule R N // Q.FG} (fun Q ↦ M ⊗[R] Q.val)
        (fun _ _ hPQ ↦ (inclusion hPQ).lTensor M) Q) u)
      = (lTensor M (Submodule.subtype Q.val)) u := by
  suffices (Submodule.FG.lTensor.directLimit R M N).toLinearMap.comp
      (Module.DirectLimit.of R {Q : Submodule R N // Q.FG} (fun Q ↦ M ⊗[R] Q.val)
        (fun _ _ hPQ ↦ lTensor M (inclusion hPQ)) Q)
      = lTensor M (Submodule.subtype Q.val) by
    exact DFunLike.congr_fun this u
  ext p n
  simp [Submodule.FG.lTensor.directLimit, Submodule.FG.directLimit]
/-
**Submodule.FG.lTensor.directLimit_apply'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.FG.lTensor.directLimit_apply' [DecidableEq {Q : Submodule R N //
 Q.FG}] (Q : Submodule R N) (hQ : Q.FG) (u : M otimes[R] Q) : (Submodule.FG.lTen
sor.directLimit R M N) ((Module.DirectLimit.of R {Q : Submodule R N // Q.FG} (fu
n Q => M otimes[R] Q.val) (fun _ _ hPQ => lTensor M (inclusion hPQ)) ⟨Q, hQ⟩) u)
 = (lTensor M (Submodule.subtype Q)) u
参数：Q : Submodule R N；hQ : Q.FG；u : M otimes[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.FG.lTensor.directLimit_apply`：Submodule.FG.lTensor.directLimit
_apply [DecidableEq {P : Submodule R N // P.FG}] (Q : {Q : Submodule R N // Q.FG
}) (u : M otimes[R] Q.val) :…
-/
theorem Submodule.FG.lTensor.directLimit_apply' [DecidableEq {Q : Submodule R N // Q.FG}]
    (Q : Submodule R N) (hQ : Q.FG) (u : M ⊗[R] Q) :
    (Submodule.FG.lTensor.directLimit R M N)
      ((Module.DirectLimit.of R {Q : Submodule R N // Q.FG} (fun Q ↦ M ⊗[R] Q.val)
        (fun _ _ hPQ ↦ lTensor M (inclusion hPQ)) ⟨Q, hQ⟩) u)
      = (lTensor M (Submodule.subtype Q)) u :=
  Submodule.FG.lTensor.directLimit_apply R M N ⟨Q, hQ⟩ u

variable {R M N} (u : M ⊗[R] N)
    {P : Submodule R M} (hP : Submodule.FG P) {t : P ⊗[R] N}
    {P' : Submodule R M} (hP' : Submodule.FG P') {t' : P' ⊗[R] N}
/-
**TensorProduct.exists_of_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TensorProduct.exists_of_fg : exists (P : Submodule R M), P.FG ∧ u in range
 (rTensor N P.subtype)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.DirectLimit.exists_of`：exists_of [Nonempty ι] [IsDirectedOrder ι]
 (z : DirectLimit G f) : exists i x, of R ι G f i x = z
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.FG.rTensor.directLimit_apply`：Submodule.FG.rTensor.directLimit
_apply [DecidableEq {P : Submodule R M // P.FG}] {P : {P : Submodule R M // P.FG
}} (u : P otimes[R] N) : (Su…
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
theorem TensorProduct.exists_of_fg :
    ∃ (P : Submodule R M), P.FG ∧ u ∈ range (rTensor N P.subtype) := by
  let ⟨P, t, ht⟩ := Module.DirectLimit.exists_of ((Submodule.FG.rTensor.directLimit R M N).symm u)
  use P.val, P.property, t
  rw [← Submodule.FG.rTensor.directLimit_apply, ht, LinearEquiv.apply_symm_apply]

include hP in
/-
**TensorProduct.eq_of_fg_of_subtype_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TensorProduct.eq_of_fg_of_subtype_eq {t' : P otimes[R] N} (h : rTensor N P
.subtype t = rTensor N P.subtype t') : exists (Q : Submodule R M) (hPQ : P <= Q)
, Q.FG ∧ rTensor N (inclusion hPQ) t = rTensor N (inclusion hPQ) t'
参数：h : rTensor N P.subtype t = rTensor N P.subtype t'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.DirectLimit.exists_eq_of_of_eq`：exists_eq_of_of_eq {i x y} (h : o
f R ι G f i x = of R ι G f i y) : exists j hij, f i j hij x = f i j hij y
· 使用定理 `TensorProduct.instDirectedSystemCoeLinearMapIdRTensor`：∀ {R : Type u_1} 
[inst : CommSemiring R] {ι : Type u_2} [inst_1 : Preorder ι] {G : ι → Type u_3} 
  [inst_2 : (i : ι) → AddCommMonoid (G i)] …
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.FG.rTensor.directLimit_apply'`：Submodule.FG.rTensor.directLimi
t_apply' [DecidableEq {P : Submodule R M // P.FG}] {P : Submodule R M} (hP : Sub
module.FG P) (u : P otimes[R]…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem TensorProduct.eq_of_fg_of_subtype_eq {t' : P ⊗[R] N}
    (h : rTensor N P.subtype t = rTensor N P.subtype t') :
    ∃ (Q : Submodule R M) (hPQ : P ≤ Q), Q.FG ∧
      rTensor N (inclusion hPQ) t = rTensor N (inclusion hPQ) t' := by
  simp only [← Submodule.FG.rTensor.directLimit_apply' R M N hP, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨Q, hPQ, h⟩ := Module.DirectLimit.exists_eq_of_of_eq h
  use Q.val, Subtype.coe_le_coe.mpr hPQ, Q.property

include hP in
/-
**TensorProduct.eq_zero_of_fg_of_subtype_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TensorProduct.eq_zero_of_fg_of_subtype_eq_zero (h : rTensor N P.subtype t 
= 0) : exists (Q : Submodule R M) (hPQ : P <= Q), Q.FG ∧ rTensor N (inclusion hP
Q) t = 0
参数：h : rTensor N P.subtype t = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
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
· 使用定理 `TensorProduct.eq_of_fg_of_subtype_eq`：TensorProduct.eq_of_fg_of_subtype_
eq {t' : P otimes[R] N} (h : rTensor N P.subtype t = rTensor N P.subtype t') : e
xists (Q : Submodule R M) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
-/
theorem TensorProduct.eq_zero_of_fg_of_subtype_eq_zero (h : rTensor N P.subtype t = 0) :
    ∃ (Q : Submodule R M) (hPQ : P ≤ Q), Q.FG ∧ rTensor N (inclusion hPQ) t = 0 := by
  rw [← (rTensor N P.subtype).map_zero] at h
  simpa only [map_zero] using TensorProduct.eq_of_fg_of_subtype_eq hP h

include hP hP' in
/-
**TensorProduct.eq_of_fg_of_subtype_eq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TensorProduct.eq_of_fg_of_subtype_eq' (h : rTensor N P.subtype t = rTensor
 N P'.subtype t') : exists (Q : Submodule R M) (hPQ : P <= Q) (hP'Q : P' <= Q), 
Q.FG ∧ rTensor N (inclusion hPQ) t = rTensor N (inclusion hP'Q) t'
参数：h : rTensor N P.subtype t = rTensor N P'.subtype t'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `TensorProduct.eq_of_fg_of_subtype_eq`：TensorProduct.eq_of_fg_of_subtype_
eq {t' : P otimes[R] N} (h : rTensor N P.subtype t = rTensor N P.subtype t') : e
xists (Q : Submodule R M) …
· 使用定理 `Submodule.FG.sup`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N₁ N₂ : Submodule R M},
 N₁.FG…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.rTensor_comp`：rTensor_comp : (g.comp f).rTensor M = (g.rTensor
 M).comp (f.rTensor M)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem TensorProduct.eq_of_fg_of_subtype_eq'
    (h : rTensor N P.subtype t = rTensor N P'.subtype t') :
    ∃ (Q : Submodule R M) (hPQ : P ≤ Q) (hP'Q : P' ≤ Q), Q.FG ∧
      rTensor N (inclusion hPQ) t = rTensor N (inclusion hP'Q) t' := by
  simp only [← subtype_comp_inclusion _ _ (le_sup_left : _ ≤ P ⊔ P'),
    ← subtype_comp_inclusion _ _ (le_sup_right : _ ≤ P ⊔ P'),
    rTensor_comp, coe_comp, Function.comp_apply] at h
  let ⟨Q, hQ_le, hQ, h⟩ := TensorProduct.eq_of_fg_of_subtype_eq (hP.sup hP') h
  use Q, le_trans le_sup_left hQ_le, le_trans le_sup_right hQ_le, hQ
  simpa [← comp_apply, ← rTensor_comp] using! h

end TensorProducts

section Algebra

open TensorProduct

variable {R S M N : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  (u : S ⊗[R] N)
  {A : Subalgebra R S} (hA : A.FG) {t t' : A ⊗[R] N}
  {A' : Subalgebra R S} (hA' : A'.FG)

/-
**TensorProduct.Algebra.exists_of_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TensorProduct.Algebra.exists_of_fg : exists (A : Subalgebra R S), Subalgeb
ra.FG A ∧ u in range (rTensor N A.val.toLinearMap)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.exists_of_fg`：TensorProduct.exists_of_fg : exists (P : Sub
module R M), P.FG ∧ u in range (rTensor N P.subtype)
· 使用定理 `Subalgebra.fg_adjoin_finset`：fg_adjoin_finset (s : Finset A) : (Algebra.
adjoin R (↑s : Set A)).FG
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `LinearMap.range_comp_le_range`：range_comp_le_range [RingHomSurjective τ₂
₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : range (g
.comp f : M ->ₛₗ[τ₁…
· 使用定理 `LinearMap.rTensor_comp`：rTensor_comp : (g.comp f).rTensor M = (g.rTensor
 M).comp (f.rTensor M)
· 使用定理 `Submodule.subtype_comp_inclusion`：subtype_comp_inclusion (p q : Submodul
e R M) (h : p <= q) : q.subtype.comp (inclusion h) = p.subtype
-/
theorem TensorProduct.Algebra.exists_of_fg :
    ∃ (A : Subalgebra R S), Subalgebra.FG A ∧ u ∈ range (rTensor N A.val.toLinearMap) := by
  obtain ⟨P, ⟨s, hs⟩, hu⟩ := TensorProduct.exists_of_fg u
  use Algebra.adjoin R s, Subalgebra.fg_adjoin_finset _
  have : P ≤ (Algebra.adjoin R (s : Set S)).toSubmodule := by
    simp only [← hs, span_le, Subalgebra.coe_toSubmodule]
    exact Algebra.subset_adjoin
  rw [← subtype_comp_inclusion P _ this, rTensor_comp] at hu
  exact range_comp_le_range _ _ hu

include hA in
/-
**TensorProduct.Algebra.eq_of_fg_of_subtype_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TensorProduct.Algebra.eq_of_fg_of_subtype_eq (h : rTensor N A.val.toLinear
Map t = rTensor N A.val.toLinearMap t') : exists (B : Subalgebra R S) (hAB : A <
= B), Subalgebra.FG B ∧ rTensor N (Subalgebra.inclusion hAB).toLinearMap t = Lin
earMap.rTensor N (Subalgebra.inclusion hAB).toLinearMap t'
参数：h : rTensor N A.val.toLinearMap t = rTensor N A.val.toLinearMap t'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.exists_of_fg`：TensorProduct.exists_of_fg : exists (P : Sub
module R M), P.FG ∧ u in range (rTensor N P.subtype)
· 使用定理 `Submodule.FG.map`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {S : Type u_3} {P : Type
 u_4} …
· 使用定理 `Submodule.FG.sup`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N₁ N₂ : Submodule R M},
 N₁.FG…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_sup`：map_sup (f : M ->ₛₗ[σ₁₂] M₂) : map f (p ⊔ p') = map f
 p ⊔ map f p'
· 使用定理 `Submodule.mem_sup_left`：mem_sup_left {S T : Submodule R M} : forall {x :
 M}, x in S -> x in S ⊔ T
· 使用定理 `Submodule.mem_sup_right`：mem_sup_right {S T : Submodule R M} : forall {x
 : M}, x in T -> x in S ⊔ T
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearMap.rTensor_comp`：rTensor_comp : (g.comp f).rTensor M = (g.rTensor
 M).comp (f.rTensor M)
· 使用定理 `TensorProduct.eq_of_fg_of_subtype_eq`：TensorProduct.eq_of_fg_of_subtype_
eq {t' : P otimes[R] N} (h : rTensor N P.subtype t = rTensor N P.subtype t') : e
xists (Q : Submodule R M) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.adjoin_mono`：adjoin_mono (H : s subseteq t) : adjoin R s <= adjo
in R t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `Subalgebra.fg_adjoin_finset`：fg_adjoin_finset (s : Finset A) : (Algebra.
adjoin R (↑s : Set A)).FG
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
-/
theorem TensorProduct.Algebra.eq_of_fg_of_subtype_eq
    (h : rTensor N A.val.toLinearMap t = rTensor N A.val.toLinearMap t') :
    ∃ (B : Subalgebra R S) (hAB : A ≤ B), Subalgebra.FG B
      ∧ rTensor N (Subalgebra.inclusion hAB).toLinearMap t
        = LinearMap.rTensor N (Subalgebra.inclusion hAB).toLinearMap t' := by
  classical
  let ⟨P, hP, u, hu⟩ := TensorProduct.exists_of_fg t
  let ⟨P', hP', u', hu'⟩ := TensorProduct.exists_of_fg t'
  let P₁ := Submodule.map A.toSubmodule.subtype (P ⊔ P')
  have hP₁ : Submodule.FG P₁ := Submodule.FG.map _ (Submodule.FG.sup hP hP')
  -- the embeddings from P and P' to P₁
  let j : P →ₗ[R] P₁ := (Subalgebra.toSubmodule A).subtype.restrict
      (fun p hp ↦ by
        simp only [coe_subtype, Submodule.map_sup, P₁]
        exact Submodule.mem_sup_left ⟨p, hp, rfl⟩)
  let j' : P' →ₗ[R] P₁ := (Subalgebra.toSubmodule A).subtype.restrict
      (fun p hp ↦ by
        simp only [coe_subtype, Submodule.map_sup, P₁]
        exact Submodule.mem_sup_right ⟨p, hp, rfl⟩)
  -- we map u and u' to P₁ ⊗[R] N, getting u₁ and u'₁
  set u₁ := rTensor N j u with hu₁
  set u'₁ := rTensor N j' u' with hu'₁
  -- u₁ and u'₁ are equal in S ⊗[R] N
  have : rTensor N P₁.subtype u₁ = rTensor N P₁.subtype u'₁ := by
    rw [hu₁, hu'₁]
    simp only [← comp_apply, ← rTensor_comp]
    have hj₁ : P₁.subtype ∘ₗ j = A.val.toLinearMap ∘ₗ P.subtype := rfl
    have hj'₁ : P₁.subtype ∘ₗ j' = A.val.toLinearMap ∘ₗ P'.subtype := rfl
    rw [hj₁, hj'₁]
    simp only [rTensor_comp, comp_apply]
    rw [hu, hu', h]
  let ⟨P'₁, hP₁_le, hP'₁, h⟩ := TensorProduct.eq_of_fg_of_subtype_eq hP₁ this
  let ⟨s, hs⟩ := hP'₁
  let ⟨w, hw⟩ := hA
  let B := Algebra.adjoin R ((s ∪ w : Finset S) : Set S)
  have hBA : A ≤ B := by
    simp only [B, ← hw]
    apply Algebra.adjoin_mono
    simp only [Finset.coe_union, Set.subset_union_right]
  use B, hBA, Subalgebra.fg_adjoin_finset _
  rw [← hu, ← hu']
  simp only [← comp_apply, ← rTensor_comp]
  have hP'₁_le : P'₁ ≤ B.toSubmodule := by
    simp only [← hs, Finset.coe_union, Submodule.span_le, Subalgebra.coe_toSubmodule, B]
    exact subset_trans Set.subset_union_left Algebra.subset_adjoin
  have k : (Subalgebra.inclusion hBA).toLinearMap ∘ₗ P.subtype
    = inclusion hP'₁_le ∘ₗ inclusion hP₁_le ∘ₗ j := by ext; rfl
  have k' : (Subalgebra.inclusion hBA).toLinearMap ∘ₗ P'.subtype
    = inclusion hP'₁_le ∘ₗ inclusion hP₁_le ∘ₗ j' := by ext; rfl
  rw [k, k']
  simp only [rTensor_comp, comp_apply]
  rw [← hu₁, ← hu'₁, h]

include hA hA' in
/-
**TensorProduct.Algebra.eq_of_fg_of_subtype_eq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TensorProduct.Algebra.eq_of_fg_of_subtype_eq' {t' : A' otimes[R] N} (h : r
Tensor N A.val.toLinearMap t = rTensor N A'.val.toLinearMap t') : exists (B : Su
balgebra R S) (hAB : A <= B) (hA'B : A' <= B), Subalgebra.FG B ∧ rTensor N (Suba
lgebra.inclusion hAB).toLinearMap t = rTensor N (Subalgebra.inclusion hA'B).toLi
nearMap t'
参数：h : rTensor N A.val.toLinearMap t = rTensor N A'.val.toLinearMap t'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `TensorProduct.Algebra.eq_of_fg_of_subtype_eq`：TensorProduct.Algebra.eq_o
f_fg_of_subtype_eq (h : rTensor N A.val.toLinearMap t = rTensor N A.val.toLinear
Map t') : exists (B : Subalgebra R…
· 使用定理 `Subalgebra.FG.sup`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [
inst_1 : Semiring A] [inst_2 : Algebra R A]   {S S' : Subalgebra R A}, S.FG → S'
.FG → (…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.rTensor_comp`：rTensor_comp : (g.comp f).rTensor M = (g.rTensor
 M).comp (f.rTensor M)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem TensorProduct.Algebra.eq_of_fg_of_subtype_eq' {t' : A' ⊗[R] N}
    (h : rTensor N A.val.toLinearMap t = rTensor N A'.val.toLinearMap t') :
    ∃ (B : Subalgebra R S) (hAB : A ≤ B) (hA'B : A' ≤ B), Subalgebra.FG B
      ∧ rTensor N (Subalgebra.inclusion hAB).toLinearMap t
        = rTensor N (Subalgebra.inclusion hA'B).toLinearMap t' := by
  have hj : (A ⊔ A').val.comp (Subalgebra.inclusion le_sup_left) = A.val := by ext; rfl
  have hj' : (A ⊔ A').val.comp (Subalgebra.inclusion le_sup_right) = A'.val := by ext; rfl
  simp only [← hj, ← hj', AlgHom.comp_toLinearMap, rTensor_comp, comp_apply] at h
  let ⟨B, hB_le, hB, h⟩ := TensorProduct.Algebra.eq_of_fg_of_subtype_eq
    (Subalgebra.FG.sup hA hA') h
  use B, le_trans le_sup_left hB_le, le_trans le_sup_right hB_le, hB
  simpa only [← rTensor_comp, ← comp_apply] using! h

/-- Lift an element that maps to 0 -/
/-
**Submodule.exists_fg_of_baseChange_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.exists_fg_of_baseChange_eq_zero (f : M ->ₗ[R] N) {t : S otimes[R
] M} (ht : f.baseChange S t = 0) : exists (A : Subalgebra R S) (_ : A.FG) (u : A
 otimes[R] M), f.baseChange A u = 0 ∧ A.val.toLinearMap.rTensor M u = t
参数：f : M ->ₗ[R] N；ht : f.baseChange S t = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `TensorProduct.Algebra.exists_of_fg`：TensorProduct.Algebra.exists_of_fg :
 exists (A : Subalgebra R S), Subalgebra.FG A ∧ u in range (rTensor N A.val.toLi
nearMap)
· 使用定理 `TensorProduct.Algebra.eq_of_fg_of_subtype_eq`：TensorProduct.Algebra.eq_o
f_fg_of_subtype_eq (h : rTensor N A.val.toLinearMap t = rTensor N A.val.toLinear
Map t') : exists (B : Subalgebra R…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.rTensor_baseChange`：rTensor_baseChange (φ : A ->ₐ[R] B) (t : A
 otimes[R] M) (f : M ->ₗ[R] N) : (φ.toLinearMap.rTensor N) (f.baseChange A t) = 
(f.baseChange B) (…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `LinearMap.rTensor_comp`：rTensor_comp : (g.comp f).rTensor M = (g.rTensor
 M).comp (f.rTensor M)

--- 原说明 ---
Lift an element that maps to 0
-/
theorem Submodule.exists_fg_of_baseChange_eq_zero
    (f : M →ₗ[R] N) {t : S ⊗[R] M} (ht : f.baseChange S t = 0) :
    ∃ (A : Subalgebra R S) (_ : A.FG) (u : A ⊗[R] M),
      f.baseChange A u = 0 ∧ A.val.toLinearMap.rTensor M u = t := by
  obtain ⟨A, hA, ht_memA⟩ := TensorProduct.Algebra.exists_of_fg t
  obtain ⟨u, hu⟩ := _root_.id ht_memA
  have := TensorProduct.Algebra.eq_of_fg_of_subtype_eq hA (t := f.baseChange _ u) (t' := 0)
  simp only [map_zero, exists_and_left] at this
  have hu' : (A.val.toLinearMap.rTensor N) (f.baseChange (↥A) u) = 0 := by
    rw [← ht, ← hu, rTensor_baseChange]
  obtain ⟨B, hB, hAB, hu'⟩ := this hu'
  use B, hB, rTensor M (Subalgebra.inclusion hAB).toLinearMap u
  constructor
  · rw [← rTensor_baseChange, hu']
  · rw [← comp_apply, ← rTensor_comp, ← hu]
    congr

end Algebra

