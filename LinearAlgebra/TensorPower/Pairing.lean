/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.TensorPower.Basic

/-!
# The pairing between the tensor power of the dual and the tensor power

We construct the pairing
`TensorPower.pairingDual : ⨂[R]^n (Module.Dual R M) →ₗ[R] (Module.Dual R (⨂[R]^n M))`.

-/

@[expose] public section

open TensorProduct PiTensorProduct

namespace TensorPower

variable (R : Type*) (M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]
  (n : ℕ)


/-- The canonical multilinear map from `n` copies of the dual of the module `M`
to the dual of `⨂[R]^n M`. -/
/-
**TensorPower.multilinearMapToDual** 是 Mathlib 中的一个定义，位于命名空间 `TensorPower`。
形式化陈述：multilinearMapToDual : MultilinearMap R (fun (_ : Fin n) => Module.Dual R 
M) (Module.Dual R (⨂[R]^n M))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical multilinear map from `n` copies of the dual of the module `M`
to the dual of `⨂[R]^n M`.
-/
noncomputable def multilinearMapToDual :
    MultilinearMap R (fun (_ : Fin n) ↦ Module.Dual R M)
      (Module.Dual R (⨂[R]^n M)) :=
  have : ∀ (_ : DecidableEq (Fin n)) (f : Fin n → Module.Dual R M)
      (φ : Module.Dual R M) (i j : Fin n) (v : Fin n → M),
      (Function.update f i φ) j (v j) =
      Function.update (fun j ↦ f j (v j)) i (φ (v i)) j := fun _ f φ i j v ↦ by
    by_cases h : j = i
    · subst h
      simp only [Function.update_self]
    · simp only [Function.update_of_ne h]
  { toFun := fun f ↦ PiTensorProduct.lift
      (MultilinearMap.compLinearMap (MultilinearMap.mkPiRing R (Fin n) 1) f)
    map_update_add' := fun f i φ₁ φ₂ ↦ by
      ext v
      simp [this]
    map_update_smul' := fun f i a φ ↦ by
      ext v
      simp [this, Finset.prod_update_of_mem, Semigroup.mul_assoc] }

variable {R M n} in
@[simp]
/-
**TensorPower.multilinearMapToDual_apply_tprod** 是 Mathlib 中的一个定理，位于命名空间 `Tensor
Power`。
形式化陈述：multilinearMapToDual_apply_tprod (f : (_ : Fin n) -> Module.Dual R M) (v :
 Fin n -> M) : multilinearMapToDual R M n f (tprod _ v) = ∏ i, (f i (v i))
参数：f : (_ : Fin n) -> Module.Dual R M；v : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.lift.tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : Comm
Semiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_
2 : (i : ι) → _r…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem multilinearMapToDual_apply_tprod (f : (_ : Fin n) → Module.Dual R M) (v : Fin n → M) :
    multilinearMapToDual R M n f (tprod _ v) = ∏ i, (f i (v i)) := by
  simp [multilinearMapToDual]

/-- The linear map from the tensor power of the dual to the dual of the tensor power. -/
/-
**TensorPower.pairingDual** 是 Mathlib 中的一个定义，位于命名空间 `TensorPower`。
形式化陈述：pairingDual : ⨂[R]^n (Module.Dual R M) ->ₗ[R] (Module.Dual R (⨂[R]^n M))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map from the tensor power of the dual to the dual of the tensor power
.
-/
noncomputable def pairingDual :
    ⨂[R]^n (Module.Dual R M) →ₗ[R] (Module.Dual R (⨂[R]^n M)) :=
  PiTensorProduct.lift (multilinearMapToDual R M n)

variable {R M n} in
@[simp]
/-
**TensorPower.pairingDual_tprod_tprod** 是 Mathlib 中的一个引理，位于命名空间 `TensorPower`。
形式化陈述：pairingDual_tprod_tprod (f : (_ : Fin n) -> Module.Dual R M) (v : Fin n ->
 M) : pairingDual R M n (tprod _ f) (tprod _ v) = ∏ i, (f i (v i))
参数：f : (_ : Fin n) -> Module.Dual R M；v : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.lift.tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : Comm
Semiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_
2 : (i : ι) → _r…
· 使用定理 `TensorPower.multilinearMapToDual_apply_tprod`：multilinearMapToDual_apply
_tprod (f : (_ : Fin n) -> Module.Dual R M) (v : Fin n -> M) : multilinearMapToD
ual R M n f (tprod _ v) = ∏ i, (f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pairingDual_tprod_tprod (f : (_ : Fin n) → Module.Dual R M) (v : Fin n → M) :
    pairingDual R M n (tprod _ f) (tprod _ v) = ∏ i, (f i (v i)) := by
  simp [pairingDual]

end TensorPower

