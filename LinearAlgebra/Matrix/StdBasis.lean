/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Standard basis on matrices

## Main results

* `Basis.matrix`: extend a basis on `M` to the standard basis on `Matrix n m M`
-/

@[expose] public section

open Module

namespace Module.Basis
variable {ι R M : Type*} (m n : Type*)
variable [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid M] [Module R M]

/-- The standard basis of `Matrix m n M` given a basis on `M`. -/
/-
**Module.Basis.matrix** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       (m : Type u
_4) →         (n : Type u_5) →           [Fintype m] →             [Fintype n] →
               [inst : Semiring R] →                 [inst_1 : AddCommMonoid M] 
→                   [inst_2 : _root_.Module R M] → Module.Basis ι R M → Module.B
asis (m × n × ι) R (Matrix m n M)
参数：m : Type u_4；n : Type u_5；m × n × ι；Matrix m n M。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The standard basis of `Matrix m n M` given a basis on `M`.
-/
protected noncomputable def matrix (b : Basis ι R M) :
    Basis (m × n × ι) R (Matrix m n M) :=
  Basis.reindex (Pi.basis fun _ : m => Pi.basis fun _ : n => b)
    ((Equiv.sigmaEquivProd _ _).trans <| .prodCongr (.refl _) (Equiv.sigmaEquivProd _ _))
    |>.map (Matrix.ofLinearEquiv R)

variable {n m}

@[simp]
/-
**Module.Basis.matrix_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：matrix_apply (b : Basis ι R M) (i : m) (j : n) (k : ι) [DecidableEq m] [De
cidableEq n] : b.matrix m n (i, j, k) = Matrix.single i j (b k)
参数：b : Basis ι R M；i : m；j : n；k : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_reindex`：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.
symm
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.prodCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_1
1} {β₂ : Type u_12} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂),   ⇑(e₁.prodCongr e₂) = Prod.m
ap ⇑e₁ ⇑e₂
· 使用定理 `Equiv.sigmaEquivProd_symm_apply`：∀ (α : Type u_1) (β : Type u_2) (a : α 
× β), (Equiv.sigmaEquivProd α β).symm a = ⟨a.1, a.2⟩
· 使用定理 `Pi.basis_apply`：basis_apply [DecidableEq η] (s : forall j, Basis (ιs j) 
R (Ms j)) (ji) : Pi.basis s ji = Pi.single ji.1 (s ji.1 ji.2)
· 使用定理 `Matrix.single_eq_of_single_single`：single_eq_of_single_single (i : m) (j
 : n) (a : α) : single i j a = Matrix.of (Pi.single i (Pi.single j a))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem matrix_apply (b : Basis ι R M) (i : m) (j : n) (k : ι) [DecidableEq m] [DecidableEq n] :
    b.matrix m n (i, j, k) = Matrix.single i j (b k) := by
  simp [Basis.matrix, Matrix.single_eq_of_single_single]

end Module.Basis

namespace Matrix

variable (R : Type*) (m n : Type*) [Fintype m] [Finite n] [Semiring R]

/-- The standard basis of `Matrix m n R`. -/
/-
**Matrix.stdBasis** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：stdBasis : Basis (m × n) R (Matrix m n R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The standard basis of `Matrix m n R`.
-/
noncomputable def stdBasis : Basis (m × n) R (Matrix m n R) :=
  Basis.reindex (Pi.basis fun _ : m => Pi.basisFun R n) (Equiv.sigmaEquivProd _ _)
    |>.map (ofLinearEquiv R)

variable {n m}
/-
**Matrix.stdBasis_eq_single** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：stdBasis_eq_single (i : m) (j : n) [DecidableEq m] [DecidableEq n] : stdBa
sis R m n (i, j) = single i j (1 : R)
参数：i : m；j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_reindex`：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.
symm
· 使用定理 `Equiv.sigmaEquivProd_symm_apply`：∀ (α : Type u_1) (β : Type u_2) (a : α 
× β), (Equiv.sigmaEquivProd α β).symm a = ⟨a.1, a.2⟩
· 使用定理 `Pi.basis_apply`：basis_apply [DecidableEq η] (s : forall j, Basis (ιs j) 
R (Ms j)) (ji) : Pi.basis s ji = Pi.single ji.1 (s ji.1 ji.2)
· 使用定理 `Pi.basisFun_apply`：basisFun_apply [DecidableEq η] (i) : basisFun R η i =
 Pi.single i 1
· 使用定理 `Matrix.single_eq_of_single_single`：single_eq_of_single_single (i : m) (j
 : n) (a : α) : single i j a = Matrix.of (Pi.single i (Pi.single j a))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stdBasis_eq_single (i : m) (j : n) [DecidableEq m] [DecidableEq n] :
    stdBasis R m n (i, j) = single i j (1 : R) := by
  simp [stdBasis, single_eq_of_single_single]

end Matrix

namespace Module.Free

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] [Module.Free R M]

/-- The module of finite matrices is free. -/
/-
**Module.Free.matrix** 是 Mathlib 中的一个实例，位于命名空间 `Module.Free`。
形式化陈述：matrix {m n : Type*} [Finite m] [Finite n] : Module.Free R (Matrix m n M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.pi`：∀ {ι : Type u_1} (R : Type u_2) [inst : Semiring R] (M :
 ι → Type u_4) [Finite ι]   [inst_2 : (i : ι) → AddCommMonoid (M i)] [inst_3 : (
i : …
· 使用定理 `Module.Free.function`：∀ (ι : Type u_1) (R : Type u_2) (M : Type u_3) [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Fini
te ι] [Mod…

--- 原说明 ---
The module of finite matrices is free.
-/
instance matrix {m n : Type*} [Finite m] [Finite n] : Module.Free R (Matrix m n M) :=
  Module.Free.pi R _

end Module.Free

