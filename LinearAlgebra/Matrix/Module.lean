/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Data.Matrix.Basis

/-!
# Mₙ(R)-module structure on `Mⁿ`

## Main Results

- `Matrix.Module.matrixModule`: This instance shows `ι → M` is a module over `Matrix ι ι R`, and
  the action of it is a generalization of `Matrix.mulVec`, this is only available in the
  `Matrix.Module` namespace.
- `LinearMap.mapMatrixModule`: This defines a linear map from `ι → M` to `ι → N` over
  `Matrix ι ι R` induced by a linear map from `M` to `N` and together with `Matrix.matrixModule`
  it gives a functor from the category of `R`-modules to the category of `Matrix ι ι R`-modules.

## Tags
matrix, module
-/

@[expose] public section

variable {ι R M N P : Type*} [Ring R] [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

namespace Matrix.Module

/-- `Mⁿ` is a `Mₙ(R)` module, note that this creates a diamond when `M` is `Matrix ι ι R` or when
  `M` is `R`. -/
/-
**Matrix.Module.matrixModule** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.Module`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       [inst : Rin
g R] →         [inst_1 : Fintype ι] →           [inst_2 : DecidableEq ι] →      
       [inst_3 : AddCommGroup M] → [_root_.Module R M] → _root_.Module (Matrix ι
 ι R) (ι → M)
参数：Matrix ι ι R；ι → M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Mⁿ` is a `Mₙ(R)` module, note that this creates a diamond when `M` is `Matrix ι
 ι R` or when
  `M` is `R`.
-/
scoped instance matrixModule : Module (Matrix ι ι R) (ι → M) where
  smul N v i := ∑ j : ι, N i j • v j
  one_smul v := funext fun i ↦ show ∑ _, _ = _ by simp [one_apply]
  mul_smul N₁ N₂ v := funext fun i ↦ show ∑ _, _ = ∑ _, _ • (∑ _, _) by
    simp_rw [mul_apply, Finset.smul_sum, Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
  smul_zero v := funext fun i ↦ show ∑ _, _ = _ by simp
  smul_add N v₁ v₂ := funext fun i ↦ show ∑ j : ι, N i j • (v₁ + v₂) j = (∑ _, _) + (∑ _, _) by
    simp [smul_add, Finset.sum_add_distrib]
  add_smul N₁ N₂ v := funext fun i ↦ show ∑ j : ι, (N₁ + N₂) i j • v j = (∑ _, _) + (∑ _, _) by
    simp [add_smul, Finset.sum_add_distrib]
  zero_smul v := funext fun i ↦ show ∑ _, _ = _ by simp
/-
**Matrix.Module.smul_def** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Module`。
形式化陈述：smul_def (N : Matrix ι ι R) (v : ι -> M) : N • v = fun i => ∑ j : ι, N i j
 • v j
参数：N : Matrix ι ι R；v : ι -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_def (N : Matrix ι ι R) (v : ι → M) :
    N • v = fun i ↦ ∑ j : ι, N i j • v j := rfl
/-
**Matrix.Module.smul_def'** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Module`。
形式化陈述：smul_def' (N : Matrix ι ι R) (v : ι -> M) : N • v = ∑ j : ι, fun i => N i 
j • v j
参数：N : Matrix ι ι R；v : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_def' (N : Matrix ι ι R) (v : ι → M) : N • v = ∑ j : ι, fun i ↦ N i j • v j := by
  ext; simp [smul_def]

@[simp]
/-
**Matrix.Module.smul_apply** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Module`。
形式化陈述：smul_apply (N : Matrix ι ι R) (v : ι -> M) (i : ι) : (N • v) i = ∑ j : ι, 
N i j • v j
参数：N : Matrix ι ι R；v : ι -> M；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_apply (N : Matrix ι ι R) (v : ι → M) (i : ι) :
    (N • v) i = ∑ j : ι, N i j • v j := rfl

@[simp]
/-
**Matrix.Module.single_smul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Module`。
形式化陈述：single_smul (i j : ι) (r : R) (v : ι -> M) : Matrix.single i j r • v = Pi.
single i (r • v j)
参数：i j : ι；r : R；v : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.sum_eq_single`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α
] [inst_1 : AddCommMonoid M] {f : α → M} (a : α),   (∀ (x : α), x ≠ a → f x = 0)
 → ∑ x, f x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.single_apply_of_ne`：single_apply_of_ne (h : ¬(i = i' ∧ j = j')) :
 single i j c i' j' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.single_apply_same`：single_apply_same : single i j c i j = c
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
-/
theorem single_smul (i j : ι) (r : R) (v : ι → M) :
    Matrix.single i j r • v = Pi.single i (r • v j) := by
  ext i'
  dsimp
  rw [Fintype.sum_eq_single j fun j' hj => ?_]
  · obtain rfl | hi := eq_or_ne i i' <;> simp [*]
  · simp [hj.symm]

@[simp]
/-
**Matrix.Module.diagonal_const_smul** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Module`。
形式化陈述：diagonal_const_smul (r : R) (v : ι -> M) : diagonal (fun _ : ι => r) • v =
 r • v
参数：r : R；v : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma diagonal_const_smul (r : R) (v : ι → M) :
    diagonal (fun _ : ι ↦ r) • v = r • v := by
  ext i
  simp [Matrix.diagonal_apply]
/-
**Matrix.Module.scalar_smul** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Module`。
形式化陈述：scalar_smul (r : R) (v : ι -> M) : Matrix.scalar ι r • v = r • v
参数：r : R；v : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.Module.diagonal_const_smul`：diagonal_const_smul (r : R) (v : ι ->
 M) : diagonal (fun _ : ι => r) • v = r • v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma scalar_smul (r : R) (v : ι → M) :
    Matrix.scalar ι r • v = r • v := by
  simp
/-
**Matrix.Module.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix.Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance (S : Type*) [Ring S] [SMul R S] [Module S M] [IsScalarTower R S M] :
    IsScalarTower R (Matrix ι ι S) (ι → M) where
  smul_assoc _ _ _ := by ext; simp [Finset.smul_sum]

end Matrix.Module

namespace LinearMap

open Matrix.Module

variable (ι) in
/-- The induced linear map from `Mⁿ` to `Nⁿ` by a linear map `f : M → N`, this is the matrix linear
  version of `LinearMap.compLeft`. -/
@[simps]
/-
**LinearMap.mapMatrixModule** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：mapMatrixModule (f : M ->ₗ[R] N) : (ι -> M) ->ₗ[Matrix ι ι R] (ι -> N) whe
re toFun
参数：f : M ->ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced linear map from `Mⁿ` to `Nⁿ` by a linear map `f : M → N`, this is th
e matrix linear
  version of `LinearMap.compLeft`.
-/
def mapMatrixModule (f : M →ₗ[R] N) : (ι → M) →ₗ[Matrix ι ι R] (ι → N) where
  toFun := LinearMap.compLeft f ι
  map_add' := map_add _
  map_smul' _ _ := by ext; simp

@[simp]
/-
**LinearMap.mapMatrixModule_id** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：mapMatrixModule_id : LinearMap.id.mapMatrixModule ι = .id (R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mapMatrixModule_apply`：∀ (ι : Type u_1) {R : Type u_2} {M : Ty
pe u_3} {N : Type u_4} [inst : Ring R] [inst_1 : Fintype ι]   [inst_2 : Decidabl
eEq ι] [inst_3 : AddC…
· 使用定理 `LinearMap.compLeft_apply`：∀ {R : Type u} {M₂ : Type w} {M₃ : Type y} [in
st : Semiring R] [inst_1 : AddCommMonoid M₂] [inst_2 : _root_.Module R M₂]   [in
st_3 : AddComm…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapMatrixModule_id :
    LinearMap.id.mapMatrixModule ι = .id (R := Matrix ι ι R) (M := ι → M) := by
  ext; simp
/-
**LinearMap.mapMatrixModule_id_apply** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：mapMatrixModule_id_apply (v : ι -> M) : LinearMap.id.mapMatrixModule ι (R
参数：v : ι -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.mapMatrixModule_id`：mapMatrixModule_id : LinearMap.id.mapMatri
xModule ι = .id (R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapMatrixModule_id_apply (v : ι → M) :
    LinearMap.id.mapMatrixModule ι (R := R) v = v := by
  simp
/-
**LinearMap.mapMatrixModule_comp** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：mapMatrixModule_comp (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) : (g ∘ₗ f).mapMatri
xModule ι = g.mapMatrixModule ι ∘ₗ f.mapMatrixModule ι
参数：f : M ->ₗ[R] N；g : N ->ₗ[R] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mapMatrixModule_apply`：∀ (ι : Type u_1) {R : Type u_2} {M : Ty
pe u_3} {N : Type u_4} [inst : Ring R] [inst_1 : Fintype ι]   [inst_2 : Decidabl
eEq ι] [inst_3 : AddC…
· 使用定理 `LinearMap.compLeft_apply`：∀ {R : Type u} {M₂ : Type w} {M₃ : Type y} [in
st : Semiring R] [inst_1 : AddCommMonoid M₂] [inst_2 : _root_.Module R M₂]   [in
st_3 : AddComm…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapMatrixModule_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    (g ∘ₗ f).mapMatrixModule ι = g.mapMatrixModule ι ∘ₗ f.mapMatrixModule ι := by
  ext; simp

@[simp]
/-
**LinearMap.mapMatrixModule_comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：mapMatrixModule_comp_apply (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (v : ι -> M) 
: (g ∘ₗ f).mapMatrixModule ι v = g.mapMatrixModule ι (f.mapMatrixModule ι v)
参数：f : M ->ₗ[R] N；g : N ->ₗ[R] P；v : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.mapMatrixModule_comp`：mapMatrixModule_comp (f : M ->ₗ[R] N) (g
 : N ->ₗ[R] P) : (g ∘ₗ f).mapMatrixModule ι = g.mapMatrixModule ι ∘ₗ f.mapMatrix
Module ι
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapMatrixModule_comp_apply (f : M →ₗ[R] N) (g : N →ₗ[R] P) (v : ι → M) :
    (g ∘ₗ f).mapMatrixModule ι v =
      g.mapMatrixModule ι (f.mapMatrixModule ι v) := by
  simp [mapMatrixModule_comp]

end LinearMap

