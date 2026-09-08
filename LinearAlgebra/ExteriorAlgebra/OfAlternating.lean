/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Fold
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# Extending an alternating map to the exterior algebra

## Main definitions

* `ExteriorAlgebra.liftAlternating`: construct a linear map out of the exterior algebra
  given alternating maps (corresponding to maps out of the exterior powers).
* `ExteriorAlgebra.liftAlternatingEquiv`: the above as a linear equivalence

## Main results

* `ExteriorAlgebra.lhom_ext`: linear maps from the exterior algebra agree if they agree on the
  exterior powers.

-/

@[expose] public section


variable {R M N N' : Type*}
variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup N']
variable [Module R M] [Module R N] [Module R N']

-- This instance can't be found where it's needed if we don't remind lean that it exists.
/-
**AlternatingMap.instModuleAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AlternatingMap.instModuleAddCommGroup {ι : Type*} : Module R (M [⋀^ι]->ₗ[R
] N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance AlternatingMap.instModuleAddCommGroup {ι : Type*} :
    Module R (M [⋀^ι]→ₗ[R] N) := by
  infer_instance

namespace ExteriorAlgebra

open CliffordAlgebra hiding ι

/-- Build a map out of the exterior algebra given a collection of alternating maps acting on each
exterior power -/
/-
**ExteriorAlgebra.liftAlternating** 是 Mathlib 中的一个定义，位于命名空间 `ExteriorAlgebra`。
形式化陈述：liftAlternating : (forall i, M [⋀^Fin i]->ₗ[R] N) ->ₗ[R] ExteriorAlgebra R
 M ->ₗ[R] N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a map out of the exterior algebra given a collection of alternating maps a
cting on each
exterior power
-/
def liftAlternating : (∀ i, M [⋀^Fin i]→ₗ[R] N) →ₗ[R] ExteriorAlgebra R M →ₗ[R] N := by
  suffices
    (∀ i, M [⋀^Fin i]→ₗ[R] N) →ₗ[R]
      ExteriorAlgebra R M →ₗ[R] ∀ i, M [⋀^Fin i]→ₗ[R] N by
    refine LinearMap.compr₂ this ?_
    refine (LinearEquiv.toLinearMap ?_).comp (LinearMap.proj 0)
    exact AlternatingMap.constLinearEquivOfIsEmpty.symm
  refine CliffordAlgebra.foldl _ ?_ ?_
  · refine
      LinearMap.mk₂ R (fun m f i => (f i.succ).curryLeft m) (fun m₁ m₂ f => ?_) (fun c m f => ?_)
        (fun m f₁ f₂ => ?_) fun c m f => ?_
    all_goals
      ext i : 1
      simp only [map_smul, map_add, Pi.add_apply, Pi.smul_apply, AlternatingMap.curryLeft_add,
        AlternatingMap.curryLeft_smul, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  · -- when applied twice with the same `m`, this recursive step produces 0
    intro m x
    ext
    simp

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**ExteriorAlgebra.liftAlternating_** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftAlternating_ι (f : ∀ i, M [⋀^Fin i]→ₗ[R] N) (m : M) :
    liftAlternating (R := R) (M := M) (N := N) f (ι R m) = f 1 ![m] := by
  dsimp [liftAlternating]
  rw [foldl_ι, LinearMap.mk₂_apply, AlternatingMap.curryLeft_apply_apply]
  congr!
/-
**ExteriorAlgebra.liftAlternating_** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftAlternating_ι_mul (f : ∀ i, M [⋀^Fin i]→ₗ[R] N) (m : M)
    (x : ExteriorAlgebra R M) :
    liftAlternating (R := R) (M := M) (N := N) f (ι R m * x) =
    liftAlternating (R := R) (M := M) (N := N) (fun i => (f i.succ).curryLeft m) x := by
  dsimp [liftAlternating]
  rw [foldl_mul, foldl_ι]
  rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**ExteriorAlgebra.liftAlternating_one** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra
`。
形式化陈述：liftAlternating_one (f : forall i, M [⋀^Fin i]->ₗ[R] N) : liftAlternating 
(R
参数：f : forall i, M [⋀^Fin i]->ₗ[R] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.foldl_one`：foldl_one (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n :
 N) : foldl Q f hf n 1 = n
-/
theorem liftAlternating_one (f : ∀ i, M [⋀^Fin i]→ₗ[R] N) :
    liftAlternating (R := R) (M := M) (N := N) f (1 : ExteriorAlgebra R M) = f 0 0 := by
  dsimp [liftAlternating]
  rw [foldl_one]

@[simp]
/-
**ExteriorAlgebra.liftAlternating_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Exterior
Algebra`。
形式化陈述：liftAlternating_algebraMap (f : forall i, M [⋀^Fin i]->ₗ[R] N) (r : R) : l
iftAlternating (R
参数：f : forall i, M [⋀^Fin i]->ₗ[R] N；r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ExteriorAlgebra.liftAlternating_one`：liftAlternating_one (f : forall i, 
M [⋀^Fin i]->ₗ[R] N) : liftAlternating (R
-/
theorem liftAlternating_algebraMap (f : ∀ i, M [⋀^Fin i]→ₗ[R] N) (r : R) :
    liftAlternating (R := R) (M := M) (N := N) f (algebraMap _ (ExteriorAlgebra R M) r) =
    r • f 0 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, liftAlternating_one]

@[simp]
/-
**ExteriorAlgebra.liftAlternating_apply_** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlge
bra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftAlternating_apply_ιMulti {n : ℕ} (f : ∀ i, M [⋀^Fin i]→ₗ[R] N)
    (v : Fin n → M) : liftAlternating (R := R) (M := M) (N := N) f (ιMulti R n v) = f n v := by
  rw [ιMulti_apply]
  induction n generalizing f with
  | zero => rw [List.ofFn_zero, List.prod_nil, liftAlternating_one, Subsingleton.elim 0 v]
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, liftAlternating_ι_mul, ih,
      AlternatingMap.curryLeft_apply_apply]
    congr
    exact Matrix.cons_head_tail _

@[simp]
/-
**ExteriorAlgebra.liftAlternating_comp_** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgeb
ra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftAlternating_comp_ιMulti {n : ℕ} (f : ∀ i, M [⋀^Fin i]→ₗ[R] N) :
    (liftAlternating (R := R) (M := M) (N := N) f).compAlternatingMap (ιMulti R n) = f n :=
  AlternatingMap.ext <| liftAlternating_apply_ιMulti f

@[simp]
/-
**ExteriorAlgebra.liftAlternating_comp** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebr
a`。
形式化陈述：liftAlternating_comp (g : N ->ₗ[R] N') (f : forall i, M [⋀^Fin i]->ₗ[R] N)
 : (liftAlternating (R
参数：g : N ->ₗ[R] N'；f : forall i, M [⋀^Fin i]->ₗ[R] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `CliffordAlgebra.left_induction`：left_induction {P : CliffordAlgebra Q ->
 Prop} (algebraMap : forall r : R, P (algebraMap _ _ r)) (add : forall x y, P x 
-> P y -> P (x + y))…
· 使用定理 `ExteriorAlgebra.liftAlternating_algebraMap`：liftAlternating_algebraMap (
f : forall i, M [⋀^Fin i]->ₗ[R] N) (r : R) : liftAlternating (R
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `LinearMap.compAlternatingMap_apply`：compAlternatingMap_apply (g : N ->ₗ[
R] N₂) (f : M [⋀^ι]->ₗ[R] N) (m : ι -> M) : g.compAlternatingMap f m = g (f m)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ExteriorAlgebra.liftAlternating_ι_mul`：liftAlternating_ι_mul (f : forall
 i, M [⋀^Fin i]->ₗ[R] N) (m : M) (x : ExteriorAlgebra R M) : liftAlternating (R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftAlternating_comp (g : N →ₗ[R] N') (f : ∀ i, M [⋀^Fin i]→ₗ[R] N) :
    (liftAlternating (R := R) (M := M) (N := N') fun i => g.compAlternatingMap (f i)) =
    g ∘ₗ liftAlternating (R := R) (M := M) (N := N) f := by
  ext v
  rw [LinearMap.comp_apply]
  induction v using CliffordAlgebra.left_induction generalizing f with
  | algebraMap =>
    rw [liftAlternating_algebraMap, liftAlternating_algebraMap, map_smul,
      LinearMap.compAlternatingMap_apply]
  | add _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
  | ι_mul _ _ hx =>
    rw [liftAlternating_ι_mul, liftAlternating_ι_mul, ← hx]
    simp_rw [AlternatingMap.curryLeft_compAlternatingMap]

@[simp]
/-
**ExteriorAlgebra.liftAlternating_** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftAlternating_ιMulti :
    liftAlternating (R := R) (M := M) (N := ExteriorAlgebra R M) (ιMulti R) =
    (LinearMap.id : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M) := by
  ext v
  dsimp
  induction v using CliffordAlgebra.left_induction with
  | algebraMap => rw [liftAlternating_algebraMap, ιMulti_zero_apply, Algebra.algebraMap_eq_smul_one]
  | add _ _ hx hy => rw [map_add, hx, hy]
  | ι_mul _ _ hx => simp_rw [liftAlternating_ι_mul, ιMulti_succ_curryLeft, liftAlternating_comp,
      LinearMap.comp_apply, LinearMap.mulLeft_apply, hx]

/-- `ExteriorAlgebra.liftAlternating` is an equivalence. -/
@[simps apply symm_apply]
/-
**ExteriorAlgebra.liftAlternatingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ExteriorAlgebr
a`。
形式化陈述：liftAlternatingEquiv : (forall i, M [⋀^Fin i]->ₗ[R] N) ≃ₗ[R] ExteriorAlgeb
ra R M ->ₗ[R] N where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ExteriorAlgebra.liftAlternating` is an equivalence.
-/
def liftAlternatingEquiv : (∀ i, M [⋀^Fin i]→ₗ[R] N) ≃ₗ[R] ExteriorAlgebra R M →ₗ[R] N where
  toFun := liftAlternating (R := R)
  map_add' := map_add _
  map_smul' := map_smul _
  invFun F i := F.compAlternatingMap (ιMulti R i)
  left_inv _ := funext fun _ => liftAlternating_comp_ιMulti _
  right_inv F :=
    (liftAlternating_comp _ _).trans <| by rw [liftAlternating_ιMulti, LinearMap.comp_id]

/-- To show that two linear maps from the exterior algebra agree, it suffices to show they agree on
the exterior powers.

See note [partially-applied ext lemmas] -/
@[ext]
/-
**ExteriorAlgebra.lhom_ext** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
形式化陈述：lhom_ext ⦃f g : ExteriorAlgebra R M ->ₗ[R] N⦄ (h : forall i, f.compAlterna
tingMap (ιMulti R i) = g.compAlternatingMap (ιMulti R i)) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
To show that two linear maps from the exterior algebra agree, it suffices to sho
w they agree on
the exterior powers.

See note [partially-applied ext lemmas]
-/
theorem lhom_ext ⦃f g : ExteriorAlgebra R M →ₗ[R] N⦄
    (h : ∀ i, f.compAlternatingMap (ιMulti R i) = g.compAlternatingMap (ιMulti R i)) : f = g :=
  liftAlternatingEquiv.symm.injective <| funext h

end ExteriorAlgebra

