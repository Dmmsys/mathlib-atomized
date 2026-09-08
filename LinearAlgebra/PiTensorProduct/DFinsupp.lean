/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Multilinear.DFinsupp

/-!
# Tensor products of finitely supported functions

This file shows that taking `PiTensorProduct`s commutes with taking `DFinsupp`s in all arguments.

## Main results

* `ofDFinsuppEquiv`: the linear equivalence between a `PiTensorProduct` of `DFinsupp`s
  and the `DFinsupp` of the `PiTensorProduct`s.
-/

@[expose] public section

namespace PiTensorProduct

open LinearMap TensorProduct

variable {R ι : Type*} {κ : ι → Type*} {M : (i : ι) → κ i → Type*}
  [CommSemiring R] [Π i (j : κ i), AddCommMonoid (M i j)] [Π i (j : κ i), Module R (M i j)]
  [Fintype ι] [DecidableEq ι] [(i : ι) → DecidableEq (κ i)]

/-- The `ι`-ary tensor product distributes over `κ i`-ary finitely supported functions. -/
/-
**PiTensorProduct.ofDFinsuppEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PiTensorProduct`。
形式化陈述：ofDFinsuppEquiv : (⨂[R] i, (Π₀ j : κ i, M i j)) ≃ₗ[R] Π₀ p : Π i, κ i, ⨂[R
] i, M i (p i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ι`-ary tensor product distributes over `κ i`-ary finitely supported functio
ns.
-/
def ofDFinsuppEquiv :
    (⨂[R] i, (Π₀ j : κ i, M i j)) ≃ₗ[R] Π₀ p : Π i, κ i, ⨂[R] i, M i (p i) :=
  LinearEquiv.ofLinearMap
    (lift <| MultilinearMap.fromDFinsuppEquiv κ R
      fun p ↦ (DFinsupp.lsingle p).compMultilinearMap (tprod R))
    (DFinsupp.lsum R fun p ↦ lift <|
      (PiTensorProduct.map fun i ↦ DFinsupp.lsingle (p i)).compMultilinearMap (tprod R))
    (by ext p x; simp)
    (by ext x; simp)

@[simp]
/-
**PiTensorProduct.ofDFinsuppEquiv_tprod_single** 是 Mathlib 中的一个定理，位于命名空间 `PiTens
orProduct`。
形式化陈述：ofDFinsuppEquiv_tprod_single (p : Π i, κ i) (x : Π i, M i (p i)) : ofDFins
uppEquiv (⨂ₜ[R] i, DFinsupp.single (p i) (x i)) = DFinsupp.single p (⨂ₜ[R] i, x 
i)
参数：p : Π i, κ i；x : Π i, M i (p i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiTensorProduct.lift.tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : Comm
Semiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_
2 : (i : ι) → _r…
· 使用定理 `MultilinearMap.fromDFinsuppEquiv_single`：fromDFinsuppEquiv_single (f : Π
 (p : Π i, κ i), MultilinearMap R (fun i => M i (p i)) N) (p : Π i, κ i) (x : Π 
i, M i (p i)) : fromDFinsuppE…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofDFinsuppEquiv_tprod_single (p : Π i, κ i) (x : Π i, M i (p i)) :
    ofDFinsuppEquiv (⨂ₜ[R] i, DFinsupp.single (p i) (x i)) =
      DFinsupp.single p (⨂ₜ[R] i, x i) := by
  simp [ofDFinsuppEquiv]

@[simp]
/-
**PiTensorProduct.ofDFinsuppEquiv_symm_single_tprod** 是 Mathlib 中的一个定理，位于命名空间 `P
iTensorProduct`。
形式化陈述：ofDFinsuppEquiv_symm_single_tprod (p : Π i, κ i) (x : Π i, M i (p i)) : of
DFinsuppEquiv.symm (DFinsupp.single p (tprod R x)) = (⨂ₜ[R] i, DFinsupp.single (
p i) (x i))
参数：p : Π i, κ i；x : Π i, M i (p i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.lsum_apply_apply`：∀ {ι : Type u_1} {R : Type u_3} (S : Type u_4
) {M : ι → Type u_5} {N : Type u_6} [inst : Semiring R]   [inst_1 : (i : ι) → Ad
dCommMonoid (M …
· 使用定理 `DFinsupp.sumAddHom_single`：sumAddHom_single [forall i, AddZeroClass (β i
)] [AddCommMonoid γ] (φ : forall i, β i ->+ γ) (i) (x : β i) : sumAddHom φ (sing
le i x) = φ i x
· 使用定理 `PiTensorProduct.lift.tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : Comm
Semiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_
2 : (i : ι) → _r…
· 使用定理 `PiTensorProduct.map_tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : CommS
emiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_2
 : (i : ι) → _r…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofDFinsuppEquiv_symm_single_tprod (p : Π i, κ i) (x : Π i, M i (p i)) :
    ofDFinsuppEquiv.symm (DFinsupp.single p (tprod R x)) =
      (⨂ₜ[R] i, DFinsupp.single (p i) (x i)) := by
  simp [ofDFinsuppEquiv]

@[simp]
/-
**PiTensorProduct.ofDFinsuppEquiv_tprod_apply** 是 Mathlib 中的一个定理，位于命名空间 `PiTenso
rProduct`。
形式化陈述：ofDFinsuppEquiv_tprod_apply (x : Π i, Π₀ j, M i j) (p : Π i, κ i) : ofDFin
suppEquiv (tprod R x) p = ⨂ₜ[R] i, x i (p i)
参数：x : Π i, Π₀ j, M i j；p : Π i, κ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PiTensorProduct.lift.tprod`：∀ {ι : Type u_1} {R : Type u_4} [inst : Comm
Semiring R] {s : ι → Type u_7} [inst_1 : (i : ι) → AddCommMonoid (s i)]   [inst_
2 : (i : ι) → _r…
· 使用定理 `MultilinearMap.fromDFinsuppEquiv_apply`：fromDFinsuppEquiv_apply [Π i (j 
: κ i) (x : M i j), Decidable (x != 0)] (f : Π (p : Π i, κ i), MultilinearMap R 
(fun i => M i (p i)) N) (x :…
· 使用定理 `DFinsupp.finsetSum_apply`：finsetSum_apply {α} [forall i, AddCommMonoid (
β i)] (s : Finset α) (g : α -> Π₀ i, β i) (i : ι) : (∑ a in s, g a) i = ∑ a in s
, g a i
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Finset.sum_dite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMono
id M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι)   (b : (x : ι) → x = a → M
), (∑ x ∈…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MultilinearMap.map_coord_zero`：map_coord_zero {m : forall i, M₁ i} (i : 
ι) (h : m i = 0) : f m = 0
-/
theorem ofDFinsuppEquiv_tprod_apply (x : Π i, Π₀ j, M i j) (p : Π i, κ i) :
    ofDFinsuppEquiv (tprod R x) p = ⨂ₜ[R] i, x i (p i) := by
  classical
  simpa [ofDFinsuppEquiv, MultilinearMap.fromDFinsuppEquiv_apply] using fun i hi ↦
    ((tprod R).map_coord_zero (m := fun i ↦ x i (p i)) i hi).symm

end PiTensorProduct

