/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Tensor products and linear maps

This file defines `TensorProduct.map`, the `R`-linear map from `M ⊗ N` to `M₂ ⊗ N₂` defined by
a pair of linear (or more generally semilinear) maps `f : M → M₂` and `g : N → N₂`.

The notation `f ⊗ₘ g` is available for this map.

We also define one-sided versions `lTensor` and `rTensor`.

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

variable [Module R P] [Module R Q]

variable {M N}

open LinearMap

/-- The tensor product of a pair of linear maps between modules. -/
/-
**TensorProduct.map** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：map (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) : M otimes[R] N ->ₛₗ[σ₁₂] M₂
 otimes[R₂] N₂
参数：f : M ->ₛₗ[σ₁₂] M₂；g : N ->ₛₗ[σ₁₂] N₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of a pair of linear maps between modules.
-/
def map (f : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) : M ⊗[R] N →ₛₗ[σ₁₂] M₂ ⊗[R₂] N₂ :=
  lift <| comp (compl₂ (mk _ _ _) g) f

@[inherit_doc] scoped[RingTheory.LinearMap] infix:70 " ⊗ₘ " => TensorProduct.map

@[simp]
/-
**TensorProduct.map_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：map_tmul (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) (m : M) (n : N) : map f
 g (m otimesₜ n) = f m otimesₜ g n
参数：f : M ->ₛₗ[σ₁₂] M₂；g : N ->ₛₗ[σ₁₂] N₂；m : M；n : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_tmul (f : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) (m : M) (n : N) :
    map f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
  rfl

/-- Given semilinear maps `f : M → P`, `g : N → Q`, if we identify `M ⊗ N` with `N ⊗ M` and `P ⊗ Q`
with `Q ⊗ P`, then this lemma states that `f ⊗ g = g ⊗ f`. -/
/-
**TensorProduct.map_comp_comm_eq** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：map_comp_comm_eq (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) : map f g ∘ₛₗ (
TensorProduct.comm R N M).toLinearMap = (TensorProduct.comm R₂ N₂ M₂).toLinearMa
p ∘ₛₗ map g f
参数：f : M ->ₛₗ[σ₁₂] M₂；g : N ->ₛₗ[σ₁₂] N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h

--- 原说明 ---
Given semilinear maps `f : M → P`, `g : N → Q`, if we identify `M ⊗ N` with `N ⊗
 M` and `P ⊗ Q`
with `Q ⊗ P`, then this lemma states that `f ⊗ g = g ⊗ f`.
-/
lemma map_comp_comm_eq (f : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) :
    map f g ∘ₛₗ (TensorProduct.comm R N M).toLinearMap =
      (TensorProduct.comm R₂ N₂ M₂).toLinearMap ∘ₛₗ map g f :=
  ext rfl
/-
**TensorProduct.map_comm** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：map_comm (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) (x : N otimes[R] M) : m
ap f g (TensorProduct.comm R N M x) = TensorProduct.comm R₂ N₂ M₂ (map g f x)
参数：f : M ->ₛₗ[σ₁₂] M₂；g : N ->ₛₗ[σ₁₂] N₂；x : N otimes[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用引理 `TensorProduct.map_comp_comm_eq`：map_comp_comm_eq (f : M ->ₛₗ[σ₁₂] M₂) (g
 : N ->ₛₗ[σ₁₂] N₂) : map f g ∘ₛₗ (TensorProduct.comm R N M).toLinearMap = (Tenso
rProduct.comm R₂ N₂ …
-/
lemma map_comm (f : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) (x : N ⊗[R] M) :
    map f g (TensorProduct.comm R N M x) = TensorProduct.comm R₂ N₂ M₂ (map g f x) :=
  DFunLike.congr_fun (map_comp_comm_eq _ _) _
/-
**TensorProduct.range_map** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：range_map (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) : range (map f g) = .map₂ (mk 
R _ _) (range f) (range g)
参数：f : M ->ₗ[R] P；g : N ->ₗ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map₂_map_map`：map₂_map_map (f : M₂ ->ₗ[R] N₂ ->ₗ[R] P) (g : M 
->ₗ[R] M₂) (h : N ->ₗ[R] N₂) (p : Submodule R M) (q : Submodule R N) : map₂ f (m
ap g p) (map…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Submodule.map_map₂`：map_map₂ (f : P ->ₗ[R] P₂) (g : M ->ₗ[R] N ->ₗ[R] P)
 (p : Submodule R M) (q : Submodule R N) : map f (map₂ g p q) = map₂ (g.compr₂ f
) p q
-/
theorem range_map (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    range (map f g) = .map₂ (mk R _ _) (range f) (range g) := by
  simp_rw [← Submodule.map_top, Submodule.map₂_map_map, ← map₂_mk_top_top_eq_top,
    Submodule.map_map₂]
  rfl
/-
**TensorProduct.range_map_eq_span_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`
。
形式化陈述：range_map_eq_span_tmul (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) : range (map f g)
 = Submodule.span R { t | exists m n, f m otimesₜ g n = t }
参数：f : M ->ₗ[R] P；g : N ->ₗ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem range_map_eq_span_tmul (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    range (map f g) = Submodule.span R { t | ∃ m n, f m ⊗ₜ g n = t } := by
  simp only [← Submodule.map_top, ← span_tmul_eq_top, Submodule.map_span]
  congr; ext t
  simp

/-- Given submodules `p ⊆ P` and `q ⊆ Q`, this is the natural map: `p ⊗ q → P ⊗ Q`. -/
/-
**TensorProduct.mapIncl** 是 Mathlib 中的一个缩写定义，位于命名空间 `TensorProduct`。
形式化陈述：mapIncl (p : Submodule R P) (q : Submodule R Q) : p otimes[R] q ->ₗ[R] P o
times[R] Q
参数：p : Submodule R P；q : Submodule R Q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given submodules `p ⊆ P` and `q ⊆ Q`, this is the natural map: `p ⊗ q → P ⊗ Q`.
-/
abbrev mapIncl (p : Submodule R P) (q : Submodule R Q) : p ⊗[R] q →ₗ[R] P ⊗[R] Q :=
  map p.subtype q.subtype
/-
**TensorProduct.range_mapIncl** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：range_mapIncl (p : Submodule R P) (q : Submodule R Q) : LinearMap.range (m
apIncl p q) = .map₂ (mk R _ _) p q
参数：p : Submodule R P；q : Submodule R Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.range_map`：range_map (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) : r
ange (map f g) = .map₂ (mk R _ _) (range f) (range g)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma range_mapIncl (p : Submodule R P) (q : Submodule R Q) :
    LinearMap.range (mapIncl p q) = .map₂ (mk R _ _) p q := by
  simp_rw [mapIncl, range_map, Submodule.range_subtype]
/-
**TensorProduct.map** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：map (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) : M otimes[R] N ->ₛₗ[σ₁₂] M₂
 otimes[R₂] N₂
参数：f : M ->ₛₗ[σ₁₂] M₂；g : N ->ₛₗ[σ₁₂] N₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂_eq_range_lift_comp_mapIncl (f : P →ₗ[R] Q →ₗ[R] M)
    (p : Submodule R P) (q : Submodule R Q) :
    Submodule.map₂ f p q = LinearMap.range (lift f ∘ₗ mapIncl p q) := by
  simp_rw [LinearMap.range_comp, range_mapIncl, Submodule.map_map₂]
  rfl

section

variable {P' Q' : Type*}
variable [AddCommMonoid P'] [Module R P']
variable [AddCommMonoid Q'] [Module R Q']
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

/-
**TensorProduct.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：map_comp (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂₃] N₃) (f₁ : M ->ₛₗ[σ₁₂] M
₂) (g₁ : N ->ₛₗ[σ₁₂] N₂) : map (f₂ ∘ₛₗ f₁) (g₂ ∘ₛₗ g₁) = (map f₂ g₂) ∘ₛₗ (map f₁
 g₁)
参数：f₂ : M₂ ->ₛₗ[σ₂₃] M₃；g₂ : N₂ ->ₛₗ[σ₂₃] N₃；f₁ : M ->ₛₗ[σ₁₂] M₂；g₁ : N ->ₛₗ[σ₁₂
] N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
-/
theorem map_comp (f₂ : M₂ →ₛₗ[σ₂₃] M₃) (g₂ : N₂ →ₛₗ[σ₂₃] N₃)
    (f₁ : M →ₛₗ[σ₁₂] M₂) (g₁ : N →ₛₗ[σ₁₂] N₂) :
    map (f₂ ∘ₛₗ f₁) (g₂ ∘ₛₗ g₁) = (map f₂ g₂) ∘ₛₗ (map f₁ g₁) := ext' fun _ _ => rfl
/-
**TensorProduct.map_map** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：map_map (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂₃] N₃) (f₁ : M ->ₛₗ[σ₁₂] M₂
) (g₁ : N ->ₛₗ[σ₁₂] N₂) (x : M otimes[R] N) : map f₂ g₂ (map f₁ g₁ x) = map (f₂ 
∘ₛₗ f₁) (g₂ ∘ₛₗ g₁) x
参数：f₂ : M₂ ->ₛₗ[σ₂₃] M₃；g₂ : N₂ ->ₛₗ[σ₂₃] N₃；f₁ : M ->ₛₗ[σ₁₂] M₂；g₁ : N ->ₛₗ[σ₁₂
] N₂；x : M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TensorProduct.map_comp`：map_comp (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂
₃] N₃) (f₁ : M ->ₛₗ[σ₁₂] M₂) (g₁ : N ->ₛₗ[σ₁₂] N₂) : map (f₂ ∘ₛₗ f₁) (g₂ ∘ₛₗ g₁)
 = (map f₂ g…
-/
theorem map_map (f₂ : M₂ →ₛₗ[σ₂₃] M₃) (g₂ : N₂ →ₛₗ[σ₂₃] N₃)
    (f₁ : M →ₛₗ[σ₁₂] M₂) (g₁ : N →ₛₗ[σ₁₂] N₂) (x : M ⊗[R] N) :
    map f₂ g₂ (map f₁ g₁ x) = map (f₂ ∘ₛₗ f₁) (g₂ ∘ₛₗ g₁) x :=
  DFunLike.congr_fun (map_comp ..).symm x
/-
**TensorProduct.range_map_mono** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：range_map_mono [Module R M₂] [Module R M₃] [Module R N₂] [Module R N₃] {a 
: M ->ₗ[R] M₂} {b : M₃ ->ₗ[R] M₂} {c : N ->ₗ[R] N₂} {d : N₃ ->ₗ[R] N₂} (hab : ra
nge a <= range b) (hcd : range c <= range d) : range (map a c) <= range (map b d
)
参数：hab : range a <= range b；hcd : range c <= range d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.range_map`：range_map (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) : r
ange (map f g) = .map₂ (mk R _ _) (range f) (range g)
· 使用定理 `Submodule.map₂_le_map₂`：map₂_le_map₂ {f : M ->ₗ[R] N ->ₗ[R] P} {p₁ p₂ : 
Submodule R M} {q₁ q₂ : Submodule R N} (hp : p₁ <= p₂) (hq : q₁ <= q₂) : map₂ f 
p₁ q₁ <= map…
-/
lemma range_map_mono [Module R M₂] [Module R M₃] [Module R N₂] [Module R N₃]
    {a : M →ₗ[R] M₂} {b : M₃ →ₗ[R] M₂} {c : N →ₗ[R] N₂} {d : N₃ →ₗ[R] N₂}
    (hab : range a ≤ range b) (hcd : range c ≤ range d) : range (map a c) ≤ range (map b d) := by
  simp_rw [range_map]
  exact Submodule.map₂_le_map₂ hab hcd
/-
**TensorProduct.range_mapIncl_mono** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：range_mapIncl_mono {p p' : Submodule R P} {q q' : Submodule R Q} (hp : p <
= p') (hq : q <= q') : LinearMap.range (mapIncl p q) <= LinearMap.range (mapIncl
 p' q')
参数：hp : p <= p'；hq : q <= q'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TensorProduct.range_map_mono`：range_map_mono [Module R M₂] [Module R M₃]
 [Module R N₂] [Module R N₃] {a : M ->ₗ[R] M₂} {b : M₃ ->ₗ[R] M₂} {c : N ->ₗ[R] 
N₂} {d : N₃ ->ₗ[R]…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
-/
lemma range_mapIncl_mono {p p' : Submodule R P} {q q' : Submodule R Q} (hp : p ≤ p') (hq : q ≤ q') :
    LinearMap.range (mapIncl p q) ≤ LinearMap.range (mapIncl p' q') :=
  range_map_mono (by simpa) (by simpa)
/-
**TensorProduct.lift_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：lift_comp_map (i : M₂ ->ₛₗ[σ₂₃] N₂ ->ₛₗ[σ₂₃] P₃) (f : M ->ₛₗ[σ₁₂] M₂) (g :
 N ->ₛₗ[σ₁₂] N₂) : (lift i).comp (map f g) = lift ((i.comp f).compl₂ g)
参数：i : M₂ ->ₛₗ[σ₂₃] N₂ ->ₛₗ[σ₂₃] P₃；f : M ->ₛₗ[σ₁₂] M₂；g : N ->ₛₗ[σ₁₂] N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
-/
theorem lift_comp_map (i : M₂ →ₛₗ[σ₂₃] N₂ →ₛₗ[σ₂₃] P₃) (f : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) :
    (lift i).comp (map f g) = lift ((i.comp f).compl₂ g) :=
  ext' fun _ _ => rfl

attribute [local ext high] ext

@[simp]
/-
**TensorProduct.map_id** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：map_id : map (id : M ->ₗ[R] M) (id : N ->ₗ[R] N) = .id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_id : map (id : M →ₗ[R] M) (id : N →ₗ[R] N) = .id := by
  ext
  simp only [mk_apply, id_coe, compr₂ₛₗ_apply, _root_.id, map_tmul]

@[simp]
/-
**TensorProduct.map_one** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Type u_7} {N : Type u_8} [in
st_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M
] [inst_4 : _root_.Module R N], TensorProduct.map 1 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.map_id`：map_id : map (id : M ->ₗ[R] M) (id : N ->ₗ[R] N) =
 .id
-/
protected theorem map_one : map (1 : M →ₗ[R] M) (1 : N →ₗ[R] N) = 1 :=
  map_id
/-
**TensorProduct.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Type u_7} {N : Type u_8} [in
st_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M
] [inst_4 : _root_.Module R N] (f₁ f₂ : M →ₗ[R] M)   (g₁ g₂ : N →ₗ[R] N), Tensor
Product.map (f₁ * f₂) (g₁ * g₂) = TensorProduct.map f₁ g₁ * TensorProduct.map f₂
 g₂
参数：f₁ f₂ : M →ₗ[R] M；g₁ g₂ : N →ₗ[R] N；f₁ * f₂；g₁ * g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.map_comp`：map_comp (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂
₃] N₃) (f₁ : M ->ₛₗ[σ₁₂] M₂) (g₁ : N ->ₛₗ[σ₁₂] N₂) : map (f₂ ∘ₛₗ f₁) (g₂ ∘ₛₗ g₁)
 = (map f₂ g…
-/
protected theorem map_mul (f₁ f₂ : M →ₗ[R] M) (g₁ g₂ : N →ₗ[R] N) :
    map (f₁ * f₂) (g₁ * g₂) = map f₁ g₁ * map f₂ g₂ :=
  map_comp ..

@[simp]
/-
**TensorProduct.map_pow** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Type u_7} {N : Type u_8} [in
st_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M
] [inst_4 : _root_.Module R N] (f : M →ₗ[R] M) (g : N →ₗ[R] N)   (n : ℕ), Tensor
Product.map f g ^ n = TensorProduct.map (f ^ n) (g ^ n)
参数：f : M →ₗ[R] M；g : N →ₗ[R] N；n : ℕ；f ^ n；g ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `TensorProduct.map_one`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Typ
e u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [i
nst_3 : _ro…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `TensorProduct.map_mul`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Typ
e u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [i
nst_3 : _ro…
-/
protected theorem map_pow (f : M →ₗ[R] M) (g : N →ₗ[R] N) (n : ℕ) :
    map f g ^ n = map (f ^ n) (g ^ n) := by
  induction n with
  | zero => simp only [pow_zero, TensorProduct.map_one]
  | succ n ih => simp only [pow_succ', ih, TensorProduct.map_mul]
/-
**TensorProduct.map_add_left** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：map_add_left (f₁ f₂ : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) : map (f₁ + f₂)
 g = map f₁ g + map f₂ g
参数：f₁ f₂ : M ->ₛₗ[σ₁₂] M₂；g : N ->ₛₗ[σ₁₂] N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.add_tmul`：add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) otimesₜ
 n = m₁ otimesₜ n + m₂ otimesₜ[R] n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_add_left (f₁ f₂ : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) :
    map (f₁ + f₂) g = map f₁ g + map f₂ g := by
  ext
  simp only [add_tmul, compr₂ₛₗ_apply, mk_apply, map_tmul, add_apply]
/-
**TensorProduct.map_add_right** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：map_add_right (f : M ->ₛₗ[σ₁₂] M₂) (g₁ g₂ : N ->ₛₗ[σ₁₂] N₂) : map f (g₁ + 
g₂) = map f g₁ + map f g₂
参数：f : M ->ₛₗ[σ₁₂] M₂；g₁ g₂ : N ->ₛₗ[σ₁₂] N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_add_right (f : M →ₛₗ[σ₁₂] M₂) (g₁ g₂ : N →ₛₗ[σ₁₂] N₂) :
    map f (g₁ + g₂) = map f g₁ + map f g₂ := by
  ext
  simp only [tmul_add, compr₂ₛₗ_apply, mk_apply, map_tmul, add_apply]
/-
**TensorProduct.map_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：map_smul_left (r : R₂) (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) : map (r 
• f) g = r • map f g
参数：r : R₂；f : M ->ₛₗ[σ₁₂] M₂；g : N ->ₛₗ[σ₁₂] N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_smul_left (r : R₂) (f : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) :
    map (r • f) g = r • map f g := by
  ext
  simp only [smul_tmul, compr₂ₛₗ_apply, mk_apply, map_tmul, smul_apply, tmul_smul]
/-
**TensorProduct.map_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：map_smul_right (r : R₂) (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) : map f 
(r • g) = r • map f g
参数：r : R₂；f : M ->ₛₗ[σ₁₂] M₂；g : N ->ₛₗ[σ₁₂] N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_smul_right (r : R₂) (f : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) :
    map f (r • g) = r • map f g := by
  ext
  simp only [compr₂ₛₗ_apply, mk_apply, map_tmul, smul_apply, tmul_smul]

variable (M N P M₂ N₂ σ₁₂)

/-- The tensor product of a pair of semilinear maps between modules, bilinear in both maps. -/
/-
**TensorProduct.mapBilinear** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：mapBilinear : (M ->ₛₗ[σ₁₂] M₂) ->ₗ[R₂] (N ->ₛₗ[σ₁₂] N₂) ->ₗ[R₂] M otimes[R
] N ->ₛₗ[σ₁₂] M₂ otimes[R₂] N₂
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.map_add_left`：map_add_left (f₁ f₂ : M ->ₛₗ[σ₁₂] M₂) (g : N
 ->ₛₗ[σ₁₂] N₂) : map (f₁ + f₂) g = map f₁ g + map f₂ g
· 使用定理 `TensorProduct.map_smul_left`：map_smul_left (r : R₂) (f : M ->ₛₗ[σ₁₂] M₂)
 (g : N ->ₛₗ[σ₁₂] N₂) : map (r • f) g = r • map f g
· 使用定理 `TensorProduct.map_add_right`：map_add_right (f : M ->ₛₗ[σ₁₂] M₂) (g₁ g₂ :
 N ->ₛₗ[σ₁₂] N₂) : map f (g₁ + g₂) = map f g₁ + map f g₂
· 使用定理 `TensorProduct.map_smul_right`：map_smul_right (r : R₂) (f : M ->ₛₗ[σ₁₂] M
₂) (g : N ->ₛₗ[σ₁₂] N₂) : map f (r • g) = r • map f g

--- 原说明 ---
The tensor product of a pair of semilinear maps between modules, bilinear in bot
h maps.
-/
def mapBilinear : (M →ₛₗ[σ₁₂] M₂) →ₗ[R₂] (N →ₛₗ[σ₁₂] N₂) →ₗ[R₂] M ⊗[R] N →ₛₗ[σ₁₂] M₂ ⊗[R₂] N₂ :=
  LinearMap.mk₂ R₂ map map_add_left map_smul_left map_add_right map_smul_right

/-- The canonical linear map from `M₂ ⊗[R₂] (P →ₛₗ[σ₁₂] N₂)` to `P →ₛₗ[σ₁₂] M₂ ⊗[R₂] N₂`. -/
/-
**TensorProduct.lTensorHomToHomLTensor** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`
。
形式化陈述：lTensorHomToHomLTensor : M₂ otimes[R₂] (P ->ₛₗ[σ₁₂] N₂) ->ₗ[R₂] P ->ₛₗ[σ₁₂
] M₂ otimes[R₂] N₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical linear map from `M₂ ⊗[R₂] (P →ₛₗ[σ₁₂] N₂)` to `P →ₛₗ[σ₁₂] M₂ ⊗[R₂]
 N₂`.
-/
def lTensorHomToHomLTensor : M₂ ⊗[R₂] (P →ₛₗ[σ₁₂] N₂) →ₗ[R₂] P →ₛₗ[σ₁₂] M₂ ⊗[R₂] N₂ :=
  TensorProduct.lift (llcomp _ P N₂ _ ∘ₛₗ mk R₂ M₂ N₂)

/-- The canonical linear map from `(P →ₛₗ[σ₁₂] M₂) ⊗[R₂] N₂` to `P →ₛₗ[σ₁₂] M₂ ⊗[R₂] N₂`. -/
/-
**TensorProduct.rTensorHomToHomRTensor** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`
。
形式化陈述：rTensorHomToHomRTensor : (P ->ₛₗ[σ₁₂] M₂) otimes[R₂] N₂ ->ₗ[R₂] P ->ₛₗ[σ₁₂
] M₂ otimes[R₂] N₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical linear map from `(P →ₛₗ[σ₁₂] M₂) ⊗[R₂] N₂` to `P →ₛₗ[σ₁₂] M₂ ⊗[R₂]
 N₂`.
-/
def rTensorHomToHomRTensor : (P →ₛₗ[σ₁₂] M₂) ⊗[R₂] N₂ →ₗ[R₂] P →ₛₗ[σ₁₂] M₂ ⊗[R₂] N₂ :=
  TensorProduct.lift (llcomp _ P M₂ _ ∘ₗ (mk R₂ M₂ N₂).flip).flip

/-- The linear map from `(M →ₛₗ[σ₁₂] M₂) ⊗ (N →ₛₗ[σ₁₂] N₂)` to `M ⊗ N →ₛₗ[σ₁₂] M₂ ⊗ N₂`
sending `f ⊗ₜ g` to `TensorProduct.map f g`, the tensor product of the two maps. -/
/-
**TensorProduct.homTensorHomMap** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：homTensorHomMap : (M ->ₛₗ[σ₁₂] M₂) otimes[R₂] (N ->ₛₗ[σ₁₂] N₂) ->ₗ[R₂] M o
times[R] N ->ₛₗ[σ₁₂] M₂ otimes[R₂] N₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map from `(M →ₛₗ[σ₁₂] M₂) ⊗ (N →ₛₗ[σ₁₂] N₂)` to `M ⊗ N →ₛₗ[σ₁₂] M₂ ⊗ 
N₂`
sending `f ⊗ₜ g` to `TensorProduct.map f g`, the tensor product of the two maps.
-/
def homTensorHomMap : (M →ₛₗ[σ₁₂] M₂) ⊗[R₂] (N →ₛₗ[σ₁₂] N₂) →ₗ[R₂] M ⊗[R] N →ₛₗ[σ₁₂] M₂ ⊗[R₂] N₂ :=
  lift (mapBilinear σ₁₂ M N M₂ N₂)

variable {M N P M₂ N₂ σ₁₂}

/--
This is a binary version of `TensorProduct.map`: Given a bilinear map `f : M ⟶ P ⟶ Q` and a
bilinear map `g : N ⟶ S ⟶ T`, if we think `f` and `g` as semilinear maps with two inputs, then
`map₂ f g` is a bilinear map taking two inputs `M ⊗ N → P ⊗ S → Q ⊗ S` defined by
`map₂ f g (m ⊗ n) (p ⊗ s) = f m p ⊗ g n s`.

Mathematically, `TensorProduct.map₂` is defined as the composition
`M ⊗ N -map→ Hom(P, Q) ⊗ Hom(S, T) -homTensorHomMap→ Hom(P ⊗ S, Q ⊗ T)`.
-/
/-
**TensorProduct.map** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：map (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) : M otimes[R] N ->ₛₗ[σ₁₂] M₂
 otimes[R₂] N₂
参数：f : M ->ₛₗ[σ₁₂] M₂；g : N ->ₛₗ[σ₁₂] N₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a binary version of `TensorProduct.map`: Given a bilinear map `f : M ⟶ P
 ⟶ Q` and a
bilinear map `g : N ⟶ S ⟶ T`, if we think `f` and `g` as semilinear maps with tw
o inputs, then
`map₂ f g` is a bilinear map taking two inputs `M ⊗ N → P ⊗ S → Q ⊗ S` defined b
y
`map₂ f g (m ⊗ n) (p ⊗ s) = f m p ⊗ g n s`.

Mathematically, `TensorProduct.map₂` is defined as the composition
`M ⊗ N -map→ Hom(P, Q) ⊗ Hom(S, T) -homTensorHomMap→ Hom(P ⊗ S, Q ⊗ T)`.
-/
def map₂ (f : M →ₛₗ[σ₁₃] M₂ →ₛₗ[σ₂₃] M₃) (g : N →ₛₗ[σ₁₃] N₂ →ₛₗ[σ₂₃] N₃) :
    M ⊗[R] N →ₛₗ[σ₁₃] M₂ ⊗[R₂] N₂ →ₛₗ[σ₂₃] M₃ ⊗[R₃] N₃ :=
  homTensorHomMap σ₂₃ _ _ _ _ ∘ₛₗ map f g

@[simp]
/-
**TensorProduct.mapBilinear_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：mapBilinear_apply (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) : mapBilinear 
σ₁₂ M N M₂ N₂ f g = map f g
参数：f : M ->ₛₗ[σ₁₂] M₂；g : N ->ₛₗ[σ₁₂] N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem mapBilinear_apply (f : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) :
    mapBilinear σ₁₂ M N M₂ N₂ f g = map f g :=
  rfl

@[simp]
/-
**TensorProduct.lTensorHomToHomLTensor_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorPr
oduct`。
形式化陈述：lTensorHomToHomLTensor_apply (m₂ : M₂) (f : P ->ₛₗ[σ₁₂] N₂) (p : P) : lTen
sorHomToHomLTensor _ P M₂ N₂ (m₂ otimesₜ f) p = m₂ otimesₜ f p
参数：m₂ : M₂；f : P ->ₛₗ[σ₁₂] N₂；p : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lTensorHomToHomLTensor_apply (m₂ : M₂) (f : P →ₛₗ[σ₁₂] N₂) (p : P) :
    lTensorHomToHomLTensor _ P M₂ N₂ (m₂ ⊗ₜ f) p = m₂ ⊗ₜ f p :=
  rfl

@[simp]
/-
**TensorProduct.rTensorHomToHomRTensor_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorPr
oduct`。
形式化陈述：rTensorHomToHomRTensor_apply (f : P ->ₛₗ[σ₁₂] M₂) (n₂ : N₂) (p : P) : rTen
sorHomToHomRTensor _ P M₂ N₂ (f otimesₜ n₂) p = f p otimesₜ n₂
参数：f : P ->ₛₗ[σ₁₂] M₂；n₂ : N₂；p : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rTensorHomToHomRTensor_apply (f : P →ₛₗ[σ₁₂] M₂) (n₂ : N₂) (p : P) :
    rTensorHomToHomRTensor _ P M₂ N₂ (f ⊗ₜ n₂) p = f p ⊗ₜ n₂ :=
  rfl

@[simp]
/-
**TensorProduct.homTensorHomMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：homTensorHomMap_apply (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) : homTenso
rHomMap _ M N M₂ N₂ (f otimesₜ g) = map f g
参数：f : M ->ₛₗ[σ₁₂] M₂；g : N ->ₛₗ[σ₁₂] N₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homTensorHomMap_apply (f : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) :
    homTensorHomMap _ M N M₂ N₂ (f ⊗ₜ g) = map f g :=
  rfl

@[simp]
/-
**TensorProduct.map** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：map (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) : M otimes[R] N ->ₛₗ[σ₁₂] M₂
 otimes[R₂] N₂
参数：f : M ->ₛₗ[σ₁₂] M₂；g : N ->ₛₗ[σ₁₂] N₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂_apply_tmul (f : M →ₛₗ[σ₁₃] M₂ →ₛₗ[σ₂₃] M₃) (g : N →ₛₗ[σ₁₃] N₂ →ₛₗ[σ₂₃] N₃)
    (m : M) (n : N) :
    map₂ f g (m ⊗ₜ n) = map (f m) (g n) := rfl

@[simp]
/-
**TensorProduct.map_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：map_zero_left (g : N ->ₛₗ[σ₁₂] N₂) : map (0 : M ->ₛₗ[σ₁₂] M₂) g = 0
参数：g : N ->ₛₗ[σ₁₂] N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_zero₂`：map_zero₂ (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (y) : f 0
 y = 0
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem map_zero_left (g : N →ₛₗ[σ₁₂] N₂) : map (0 : M →ₛₗ[σ₁₂] M₂) g = 0 :=
  (mapBilinear _ M N M₂ N₂).map_zero₂ _

@[simp]
/-
**TensorProduct.map_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：map_zero_right (f : M ->ₛₗ[σ₁₂] M₂) : map f (0 : N ->ₛₗ[σ₁₂] N₂) = 0
参数：f : M ->ₛₗ[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem map_zero_right (f : M →ₛₗ[σ₁₂] M₂) : map f (0 : N →ₛₗ[σ₁₂] N₂) = 0 :=
  (mapBilinear _ M N M₂ N₂ f).map_zero

end

variable {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

/-- If `M` and `P` are semilinearly equivalent and `N` and `Q` are semilinearly equivalent
then `M ⊗ N` and `P ⊗ Q` are semilinearly equivalent. -/
/-
**TensorProduct.congr** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：congr (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) : M otimes[R] N ≃ₛₗ[σ₁₂] M₂ 
otimes[R₂] N₂
参数：f : M ≃ₛₗ[σ₁₂] M₂；g : N ≃ₛₗ[σ₁₂] N₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` and `P` are semilinearly equivalent and `N` and `Q` are semilinearly equi
valent
then `M ⊗ N` and `P ⊗ Q` are semilinearly equivalent.
-/
def congr (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) : M ⊗[R] N ≃ₛₗ[σ₁₂] M₂ ⊗[R₂] N₂ :=
  LinearEquiv.ofLinearMap (map f g) (map f.symm g.symm)
    (ext' fun m n => by simp)
    (ext' fun m n => by simp)

@[simp]
/-
**TensorProduct.toLinearMap_congr** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：toLinearMap_congr (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) : (congr f g).to
LinearMap = map f g
参数：f : M ≃ₛₗ[σ₁₂] M₂；g : N ≃ₛₗ[σ₁₂] N₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_congr (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) :
    (congr f g).toLinearMap = map f g := rfl

@[simp]
/-
**TensorProduct.congr_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：congr_tmul (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) (m : M) (n : N) : congr
 f g (m otimesₜ n) = f m otimesₜ g n
参数：f : M ≃ₛₗ[σ₁₂] M₂；g : N ≃ₛₗ[σ₁₂] N₂；m : M；n : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr_tmul (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) (m : M) (n : N) :
    congr f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
  rfl

@[simp]
/-
**TensorProduct.congr_symm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：congr_symm_tmul (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) (p : M₂) (q : N₂) 
: (congr f g).symm (p otimesₜ q) = f.symm p otimesₜ g.symm q
参数：f : M ≃ₛₗ[σ₁₂] M₂；g : N ≃ₛₗ[σ₁₂] N₂；p : M₂；q : N₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr_symm_tmul (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) (p : M₂) (q : N₂) :
    (congr f g).symm (p ⊗ₜ q) = f.symm p ⊗ₜ g.symm q :=
  rfl
/-
**TensorProduct.congr_symm** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：congr_symm (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) : (congr f g).symm = co
ngr f.symm g.symm
参数：f : M ≃ₛₗ[σ₁₂] M₂；g : N ≃ₛₗ[σ₁₂] N₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr_symm (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂] N₂) :
    (congr f g).symm = congr f.symm g.symm := rfl
/-
**TensorProduct.congr_refl_refl** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Type u_7} {N : Type u_8} [in
st_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M
] [inst_4 : _root_.Module R N],   TensorProduct.congr (LinearEquiv.refl R M) (Li
nearEquiv.refl R N) = LinearEquiv.refl R (TensorProduct R M N)
参数：LinearEquiv.refl R M；LinearEquiv.refl R N；TensorProduct R M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
-/
@[simp] theorem congr_refl_refl : congr (.refl R M) (.refl R N) = .refl R _ :=
  LinearEquiv.toLinearMap_injective <| ext' fun _ _ ↦ rfl

section congr_congr
variable {σ₃₂ : R₃ →+* R₂} [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
  {σ₃₁ : R₃ →+* R} [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]
  (f₂ : M₂ ≃ₛₗ[σ₂₃] M₃) (g₂ : N₂ ≃ₛₗ[σ₂₃] N₃) (f₁ : M ≃ₛₗ[σ₁₂] M₂) (g₁ : N ≃ₛₗ[σ₁₂] N₂)

/-
**TensorProduct.congr_trans** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：congr_trans : congr (f₁.trans f₂) (g₁.trans g₂) = (congr f₁ g₁).trans (con
gr f₂ g₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `TensorProduct.map_comp`：map_comp (f₂ : M₂ ->ₛₗ[σ₂₃] M₃) (g₂ : N₂ ->ₛₗ[σ₂
₃] N₃) (f₁ : M ->ₛₗ[σ₁₂] M₂) (g₁ : N ->ₛₗ[σ₁₂] N₂) : map (f₂ ∘ₛₗ f₁) (g₂ ∘ₛₗ g₁)
 = (map f₂ g…
-/
theorem congr_trans : congr (f₁.trans f₂) (g₁.trans g₂) = (congr f₁ g₁).trans (congr f₂ g₂) :=
  LinearEquiv.toLinearMap_injective <| map_comp _ _ _ _
/-
**TensorProduct.congr_congr** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：congr_congr (x : M otimes[R] N) : congr f₂ g₂ (congr f₁ g₁ x) = congr (f₁.
trans f₂) (g₁.trans g₂) x
参数：x : M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TensorProduct.congr_trans`：congr_trans : congr (f₁.trans f₂) (g₁.trans g
₂) = (congr f₁ g₁).trans (congr f₂ g₂)
-/
theorem congr_congr (x : M ⊗[R] N) :
    congr f₂ g₂ (congr f₁ g₁ x) = congr (f₁.trans f₂) (g₁.trans g₂) x :=
  DFunLike.congr_fun (congr_trans ..).symm x

end congr_congr

/-
**TensorProduct.congr_mul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：congr_mul (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (f' : M ≃ₗ[R] M) (g' : N ≃ₗ[R] N
) : congr (f * f') (g * g') = congr f g * congr f' g'
参数：f : M ≃ₗ[R] M；g : N ≃ₗ[R] N；f' : M ≃ₗ[R] M；g' : N ≃ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.congr_trans`：congr_trans : congr (f₁.trans f₂) (g₁.trans g
₂) = (congr f₁ g₁).trans (congr f₂ g₂)
-/
theorem congr_mul (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (f' : M ≃ₗ[R] M) (g' : N ≃ₗ[R] N) :
    congr (f * f') (g * g') = congr f g * congr f' g' := congr_trans _ _ _ _
/-
**TensorProduct.congr_pow** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Type u_7} {N : Type u_8} [in
st_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M
] [inst_4 : _root_.Module R N] (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N)   (n : ℕ), Tensor
Product.congr f g ^ n = TensorProduct.congr (f ^ n) (g ^ n)
参数：f : M ≃ₗ[R] M；g : N ≃ₗ[R] N；n : ℕ；f ^ n；g ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TensorProduct.congr_refl_refl`：∀ {R : Type u_1} [inst : CommSemiring R] 
{M : Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMono
id N] [inst_3 : _ro…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TensorProduct.congr_mul`：congr_mul (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (f' :
 M ≃ₗ[R] M) (g' : N ≃ₗ[R] N) : congr (f * f') (g * g') = congr f g * congr f' g'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem congr_pow (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (n : ℕ) :
    congr f g ^ n = congr (f ^ n) (g ^ n) := by
  induction n with
  | zero => exact congr_refl_refl.symm
  | succ n ih => simp_rw [pow_succ, ih, congr_mul]
/-
**TensorProduct.congr_zpow** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Type u_7} {N : Type u_8} [in
st_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M
] [inst_4 : _root_.Module R N] (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N)   (n : ℤ), Tensor
Product.congr f g ^ n = TensorProduct.congr (f ^ n) (g ^ n)
参数：f : M ≃ₗ[R] M；g : N ≃ₗ[R] N；n : ℤ；f ^ n；g ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.congr_pow`：∀ {R : Type u_1} [inst : CommSemiring R] {M : T
ype u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] 
[inst_3 : _ro…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.congr_symm`：congr_symm (f : M ≃ₛₗ[σ₁₂] M₂) (g : N ≃ₛₗ[σ₁₂]
 N₂) : (congr f g).symm = congr f.symm g.symm
-/
@[simp] theorem congr_zpow (f : M ≃ₗ[R] M) (g : N ≃ₗ[R] N) (n : ℤ) :
    congr f g ^ n = congr (f ^ n) (g ^ n) := by
  cases n with
  | ofNat n => exact congr_pow _ _ _
  | negSucc n => simp_rw [zpow_negSucc, congr_pow]; exact congr_symm _ _
/-
**TensorProduct.map_bijective** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：map_bijective {f : M ->ₗ[R] N} {g : P ->ₗ[R] Q} (hf : Function.Bijective f
) (hg : Function.Bijective g) : Function.Bijective (map f g)
参数：hf : Function.Bijective f；hg : Function.Bijective g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
lemma map_bijective {f : M →ₗ[R] N} {g : P →ₗ[R] Q}
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (map f g) :=
  (TensorProduct.congr (.ofBijective f hf) (.ofBijective g hg)).bijective

universe u in
/-
**TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Small.{u} M] [Small.{u} N] : Small.{u} (M ⊗[R] N) :=
  ⟨_, ⟨(TensorProduct.congr
    (Shrink.linearEquiv R M) (Shrink.linearEquiv R N)).symm.toEquiv⟩⟩

end TensorProduct

open scoped TensorProduct

variable [Module R P] [Module R Q]

namespace LinearMap

variable {N}

/-- `LinearMap.lTensor M f : M ⊗ N →ₗ M ⊗ P` is the natural linear map
induced by `f : N →ₗ P`. -/
/-
**LinearMap.lTensor** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：lTensor (f : N ->ₗ[R] P) : M otimes[R] N ->ₗ[R] M otimes[R] P
参数：f : N ->ₗ[R] P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearMap.lTensor M f : M ⊗ N →ₗ M ⊗ P` is the natural linear map
induced by `f : N →ₗ P`.
-/
def lTensor (f : N →ₗ[R] P) : M ⊗[R] N →ₗ[R] M ⊗[R] P :=
  TensorProduct.map id f

/-- `LinearMap.rTensor M f : N ⊗ M →ₗ P ⊗ M` is the natural linear map
induced by `f : N →ₗ P`. -/
/-
**LinearMap.rTensor** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：rTensor (f : N ->ₗ[R] P) : N otimes[R] M ->ₗ[R] P otimes[R] M
参数：f : N ->ₗ[R] P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearMap.rTensor M f : N ⊗ M →ₗ P ⊗ M` is the natural linear map
induced by `f : N →ₗ P`.
-/
def rTensor (f : N →ₗ[R] P) : N ⊗[R] M →ₗ[R] P ⊗[R] M :=
  TensorProduct.map f id

variable (g : P →ₗ[R] Q) (f : N →ₗ[R] P)
/-
**LinearMap.lTensor_def** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_def : f.lTensor M = TensorProduct.map LinearMap.id f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lTensor_def : f.lTensor M = TensorProduct.map LinearMap.id f := rfl
/-
**LinearMap.rTensor_def** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rTensor_def : f.rTensor M = TensorProduct.map f LinearMap.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rTensor_def : f.rTensor M = TensorProduct.map f LinearMap.id := rfl

@[simp]
/-
**LinearMap.lTensor_tmul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_tmul (m : M) (n : N) : f.lTensor M (m otimesₜ n) = m otimesₜ f n
参数：m : M；n : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lTensor_tmul (m : M) (n : N) : f.lTensor M (m ⊗ₜ n) = m ⊗ₜ f n :=
  rfl

@[simp]
/-
**LinearMap.rTensor_tmul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rTensor_tmul (m : M) (n : N) : f.rTensor M (n otimesₜ m) = f n otimesₜ m
参数：m : M；n : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rTensor_tmul (m : M) (n : N) : f.rTensor M (n ⊗ₜ m) = f n ⊗ₜ m :=
  rfl

@[simp]
/-
**LinearMap.lTensor_comp_mk** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_comp_mk (m : M) : f.lTensor M ∘ₗ TensorProduct.mk R M N m = Tensor
Product.mk R M P m ∘ₗ f
参数：m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lTensor_comp_mk (m : M) :
    f.lTensor M ∘ₗ TensorProduct.mk R M N m = TensorProduct.mk R M P m ∘ₗ f :=
  rfl

@[simp]
/-
**LinearMap.rTensor_comp_flip_mk** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rTensor_comp_flip_mk (m : M) : f.rTensor M ∘ₗ (TensorProduct.mk R N M).fli
p m = (TensorProduct.mk R P M).flip m ∘ₗ f
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
theorem rTensor_comp_flip_mk (m : M) :
    f.rTensor M ∘ₗ (TensorProduct.mk R N M).flip m = (TensorProduct.mk R P M).flip m ∘ₗ f :=
  rfl
/-
**LinearMap.comm_comp_rTensor_comp_comm_eq** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`
。
形式化陈述：comm_comp_rTensor_comp_comm_eq (g : N ->ₗ[R] P) : TensorProduct.comm R P Q
 ∘ₗ rTensor Q g ∘ₗ TensorProduct.comm R Q N = lTensor Q g
参数：g : N ->ₗ[R] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
-/
lemma comm_comp_rTensor_comp_comm_eq (g : N →ₗ[R] P) :
    TensorProduct.comm R P Q ∘ₗ rTensor Q g ∘ₗ TensorProduct.comm R Q N =
      lTensor Q g :=
  TensorProduct.ext rfl
/-
**LinearMap.comm_comp_lTensor_comp_comm_eq** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`
。
形式化陈述：comm_comp_lTensor_comp_comm_eq (g : N ->ₗ[R] P) : TensorProduct.comm R Q P
 ∘ₗ lTensor Q g ∘ₗ TensorProduct.comm R N Q = rTensor Q g
参数：g : N ->ₗ[R] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
-/
lemma comm_comp_lTensor_comp_comm_eq (g : N →ₗ[R] P) :
    TensorProduct.comm R Q P ∘ₗ lTensor Q g ∘ₗ TensorProduct.comm R N Q =
      rTensor Q g :=
  TensorProduct.ext rfl

/-- Given a linear map `f : N → P`, `f ⊗ M` is injective if and only if `M ⊗ f` is injective. -/
/-
**LinearMap.lTensor_inj_iff_rTensor_inj** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_inj_iff_rTensor_inj : Function.Injective (lTensor M f) ↔ Function.
Injective (rTensor M f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Given a linear map `f : N → P`, `f ⊗ M` is injective if and only if `M ⊗ f` is i
njective.
-/
theorem lTensor_inj_iff_rTensor_inj :
    Function.Injective (lTensor M f) ↔ Function.Injective (rTensor M f) := by
  simp [← comm_comp_rTensor_comp_comm_eq]

/-- Given a linear map `f : N → P`, `f ⊗ M` is surjective if and only if `M ⊗ f` is surjective. -/
/-
**LinearMap.lTensor_surj_iff_rTensor_surj** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_surj_iff_rTensor_surj : Function.Surjective (lTensor M f) ↔ Functi
on.Surjective (rTensor M f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Given a linear map `f : N → P`, `f ⊗ M` is surjective if and only if `M ⊗ f` is 
surjective.
-/
theorem lTensor_surj_iff_rTensor_surj :
    Function.Surjective (lTensor M f) ↔ Function.Surjective (rTensor M f) := by
  simp [← comm_comp_rTensor_comp_comm_eq]

/-- Given a linear map `f : N → P`, `f ⊗ M` is bijective if and only if `M ⊗ f` is bijective. -/
/-
**LinearMap.lTensor_bij_iff_rTensor_bij** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_bij_iff_rTensor_bij : Function.Bijective (lTensor M f) ↔ Function.
Bijective (rTensor M f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Given a linear map `f : N → P`, `f ⊗ M` is bijective if and only if `M ⊗ f` is b
ijective.
-/
theorem lTensor_bij_iff_rTensor_bij :
    Function.Bijective (lTensor M f) ↔ Function.Bijective (rTensor M f) := by
  simp [← comm_comp_rTensor_comp_comm_eq]

variable {M} in
/-
**LinearMap.smul_lTensor** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：smul_lTensor {S : Type*} [CommSemiring S] [SMul R S] [Module S M] [IsScala
rTower R S M] [SMulCommClass R S M] (s : S) (m : M otimes[R] N) : s • (f.lTensor
 M) m = (f.lTensor M) (s • m)
参数：s : S；m : M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem smul_lTensor {S : Type*} [CommSemiring S] [SMul R S] [Module S M] [IsScalarTower R S M]
    [SMulCommClass R S M] (s : S) (m : M ⊗[R] N) : s • (f.lTensor M) m = (f.lTensor M) (s • m) :=
  have h : s • (f.lTensor M) = f.lTensor M ∘ₗ (LinearMap.lsmul S (M ⊗[R] N) s).restrictScalars R :=
    TensorProduct.ext rfl
  congrFun (congrArg DFunLike.coe h) m

open TensorProduct

attribute [local ext high] TensorProduct.ext

/-- `lTensorHom M` is the natural linear map that sends a linear map `f : N →ₗ P` to `M ⊗ f`.

See also `Module.End.lTensorAlgHom`. -/
/-
**LinearMap.lTensorHom** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：lTensorHom : (N ->ₗ[R] P) ->ₗ[R] M otimes[R] N ->ₗ[R] M otimes[R] P where 
toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lTensorHom M` is the natural linear map that sends a linear map `f : N →ₗ P` to
 `M ⊗ f`.

See also `Module.End.lTensorAlgHom`.
-/
def lTensorHom : (N →ₗ[R] P) →ₗ[R] M ⊗[R] N →ₗ[R] M ⊗[R] P where
  toFun := lTensor M
  map_add' f g := by
    ext x y
    simp only [compr₂ₛₗ_apply, mk_apply, add_apply, lTensor_tmul, tmul_add]
  map_smul' r f := by
    dsimp
    ext x y
    simp only [compr₂ₛₗ_apply, mk_apply, tmul_smul, smul_apply, lTensor_tmul]

/-- `rTensorHom M` is the natural linear map that sends a linear map `f : N →ₗ P` to `f ⊗ M`.

See also `Module.End.rTensorAlgHom`. -/
/-
**LinearMap.rTensorHom** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：rTensorHom : (N ->ₗ[R] P) ->ₗ[R] N otimes[R] M ->ₗ[R] P otimes[R] M where 
toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`rTensorHom M` is the natural linear map that sends a linear map `f : N →ₗ P` to
 `f ⊗ M`.

See also `Module.End.rTensorAlgHom`.
-/
def rTensorHom : (N →ₗ[R] P) →ₗ[R] N ⊗[R] M →ₗ[R] P ⊗[R] M where
  toFun f := f.rTensor M
  map_add' f g := by
    ext x y
    simp only [compr₂ₛₗ_apply, mk_apply, add_apply, rTensor_tmul, add_tmul]
  map_smul' r f := by
    dsimp
    ext x y
    simp only [compr₂ₛₗ_apply, mk_apply, smul_tmul, tmul_smul, smul_apply, rTensor_tmul]

@[simp]
/-
**LinearMap.coe_lTensorHom** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_lTensorHom : (lTensorHom M : (N ->ₗ[R] P) -> M otimes[R] N ->ₗ[R] M ot
imes[R] P) = lTensor M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_lTensorHom : (lTensorHom M : (N →ₗ[R] P) → M ⊗[R] N →ₗ[R] M ⊗[R] P) = lTensor M :=
  rfl

@[simp]
/-
**LinearMap.coe_rTensorHom** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_rTensorHom : (rTensorHom M : (N ->ₗ[R] P) -> N otimes[R] M ->ₗ[R] P ot
imes[R] M) = rTensor M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_rTensorHom : (rTensorHom M : (N →ₗ[R] P) → N ⊗[R] M →ₗ[R] P ⊗[R] M) = rTensor M :=
  rfl

@[simp]
/-
**LinearMap.lTensor_add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_add (f g : N ->ₗ[R] P) : (f + g).lTensor M = f.lTensor M + g.lTens
or M
参数：f g : N ->ₗ[R] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
-/
theorem lTensor_add (f g : N →ₗ[R] P) : (f + g).lTensor M = f.lTensor M + g.lTensor M :=
  (lTensorHom M).map_add f g

@[simp]
/-
**LinearMap.rTensor_add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rTensor_add (f g : N ->ₗ[R] P) : (f + g).rTensor M = f.rTensor M + g.rTens
or M
参数：f g : N ->ₗ[R] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
-/
theorem rTensor_add (f g : N →ₗ[R] P) : (f + g).rTensor M = f.rTensor M + g.rTensor M :=
  (rTensorHom M).map_add f g

@[simp]
/-
**LinearMap.lTensor_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_zero : lTensor M (0 : N ->ₗ[R] P) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
-/
theorem lTensor_zero : lTensor M (0 : N →ₗ[R] P) = 0 :=
  (lTensorHom M).map_zero

@[simp]
/-
**LinearMap.rTensor_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rTensor_zero : rTensor M (0 : N ->ₗ[R] P) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
-/
theorem rTensor_zero : rTensor M (0 : N →ₗ[R] P) = 0 :=
  (rTensorHom M).map_zero

@[simp]
/-
**LinearMap.lTensor_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_smul (r : R) (f : N ->ₗ[R] P) : (r • f).lTensor M = r • f.lTensor 
M
参数：r : R；f : N ->ₗ[R] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
-/
theorem lTensor_smul (r : R) (f : N →ₗ[R] P) : (r • f).lTensor M = r • f.lTensor M :=
  (lTensorHom M).map_smul r f

@[simp]
/-
**LinearMap.rTensor_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rTensor_smul (r : R) (f : N ->ₗ[R] P) : (r • f).rTensor M = r • f.rTensor 
M
参数：r : R；f : N ->ₗ[R] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
-/
theorem rTensor_smul (r : R) (f : N →ₗ[R] P) : (r • f).rTensor M = r • f.rTensor M :=
  (rTensorHom M).map_smul r f
/-
**LinearMap.lTensor_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_comp : (g.comp f).lTensor M = (g.lTensor M).comp (f.lTensor M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lTensor_comp : (g.comp f).lTensor M = (g.lTensor M).comp (f.lTensor M) := by
  ext m n
  simp only [compr₂ₛₗ_apply, mk_apply, comp_apply, lTensor_tmul]
/-
**LinearMap.lTensor_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_comp_apply (x : M otimes[R] N) : (g.comp f).lTensor M x = (g.lTens
or M) ((f.lTensor M) x)
参数：x : M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.lTensor_comp`：lTensor_comp : (g.comp f).lTensor M = (g.lTensor
 M).comp (f.lTensor M)
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
-/
theorem lTensor_comp_apply (x : M ⊗[R] N) :
    (g.comp f).lTensor M x = (g.lTensor M) ((f.lTensor M) x) := by rw [lTensor_comp, coe_comp]; rfl
/-
**LinearMap.rTensor_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rTensor_comp : (g.comp f).rTensor M = (g.rTensor M).comp (f.rTensor M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rTensor_comp : (g.comp f).rTensor M = (g.rTensor M).comp (f.rTensor M) := by
  ext m n
  simp only [compr₂ₛₗ_apply, mk_apply, comp_apply, rTensor_tmul]
/-
**LinearMap.rTensor_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rTensor_comp_apply (x : N otimes[R] M) : (g.comp f).rTensor M x = (g.rTens
or M) ((f.rTensor M) x)
参数：x : N otimes[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.rTensor_comp`：rTensor_comp : (g.comp f).rTensor M = (g.rTensor
 M).comp (f.rTensor M)
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
-/
theorem rTensor_comp_apply (x : N ⊗[R] M) :
    (g.comp f).rTensor M x = (g.rTensor M) ((f.rTensor M) x) := by rw [rTensor_comp, coe_comp]; rfl
/-
**LinearMap.lTensor_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_mul (f g : Module.End R N) : (f * g).lTensor M = f.lTensor M * g.l
Tensor M
参数：f g : Module.End R N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.lTensor_comp`：lTensor_comp : (g.comp f).lTensor M = (g.lTensor
 M).comp (f.lTensor M)
-/
theorem lTensor_mul (f g : Module.End R N) : (f * g).lTensor M = f.lTensor M * g.lTensor M :=
  lTensor_comp M f g
/-
**LinearMap.rTensor_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rTensor_mul (f g : Module.End R N) : (f * g).rTensor M = f.rTensor M * g.r
Tensor M
参数：f g : Module.End R N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.rTensor_comp`：rTensor_comp : (g.comp f).rTensor M = (g.rTensor
 M).comp (f.rTensor M)
-/
theorem rTensor_mul (f g : Module.End R N) : (f * g).rTensor M = f.rTensor M * g.rTensor M :=
  rTensor_comp M f g

variable (N)

@[simp]
/-
**LinearMap.lTensor_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_id : (id : N ->ₗ[R] N).lTensor M = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.map_id`：map_id : map (id : M ->ₗ[R] M) (id : N ->ₗ[R] N) =
 .id
-/
theorem lTensor_id : (id : N →ₗ[R] N).lTensor M = id :=
  map_id

-- `simp` can prove this.
/-
**LinearMap.lTensor_id_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_id_apply (x : M otimes[R] N) : (LinearMap.id : N ->ₗ[R] N).lTensor
 M x = x
参数：x : M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.lTensor_id`：lTensor_id : (id : N ->ₗ[R] N).lTensor M = id
· 使用定理 `LinearMap.id_coe`：id_coe : ((LinearMap.id : M ->ₗ[R] M) : M -> M) = _roo
t_.id
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
-/
theorem lTensor_id_apply (x : M ⊗[R] N) : (LinearMap.id : N →ₗ[R] N).lTensor M x = x := by
  rw [lTensor_id, id_coe, _root_.id]

@[simp]
/-
**LinearMap.rTensor_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rTensor_id : (id : N ->ₗ[R] N).rTensor M = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.map_id`：map_id : map (id : M ->ₗ[R] M) (id : N ->ₗ[R] N) =
 .id
-/
theorem rTensor_id : (id : N →ₗ[R] N).rTensor M = id :=
  map_id

-- `simp` can prove this.
/-
**LinearMap.rTensor_id_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rTensor_id_apply (x : N otimes[R] M) : (LinearMap.id : N ->ₗ[R] N).rTensor
 M x = x
参数：x : N otimes[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.rTensor_id`：rTensor_id : (id : N ->ₗ[R] N).rTensor M = id
· 使用定理 `LinearMap.id_coe`：id_coe : ((LinearMap.id : M ->ₗ[R] M) : M -> M) = _roo
t_.id
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
-/
theorem rTensor_id_apply (x : N ⊗[R] M) : (LinearMap.id : N →ₗ[R] N).rTensor M x = x := by
  rw [rTensor_id, id_coe, _root_.id]

@[simp]
/-
**LinearMap.lTensor_smul_action** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_smul_action (r : R) : (DistribSMul.toLinearMap R N r).lTensor M = 
DistribSMul.toLinearMap R (M otimes[R] N) r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.lTensor_smul`：lTensor_smul (r : R) (f : N ->ₗ[R] P) : (r • f).
lTensor M = r • f.lTensor M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.lTensor_id`：lTensor_id : (id : N ->ₗ[R] N).lTensor M = id
-/
theorem lTensor_smul_action (r : R) :
    (DistribSMul.toLinearMap R N r).lTensor M =
      DistribSMul.toLinearMap R (M ⊗[R] N) r :=
  (lTensor_smul M r LinearMap.id).trans (congrArg _ (lTensor_id M N))

@[simp]
/-
**LinearMap.rTensor_smul_action** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rTensor_smul_action (r : R) : (DistribSMul.toLinearMap R N r).rTensor M = 
DistribSMul.toLinearMap R (N otimes[R] M) r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.rTensor_smul`：rTensor_smul (r : R) (f : N ->ₗ[R] P) : (r • f).
rTensor M = r • f.rTensor M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.rTensor_id`：rTensor_id : (id : N ->ₗ[R] N).rTensor M = id
-/
theorem rTensor_smul_action (r : R) :
    (DistribSMul.toLinearMap R N r).rTensor M =
      DistribSMul.toLinearMap R (N ⊗[R] M) r :=
  (rTensor_smul M r LinearMap.id).trans (congrArg _ (rTensor_id M N))

variable {N}

@[simp]
/-
**LinearMap.lTensor_comp_rTensor** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_comp_rTensor (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) : (g.lTensor P).com
p (f.rTensor N) = map f g
参数：f : M ->ₗ[R] P；g : N ->ₗ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lTensor_comp_rTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (g.lTensor P).comp (f.rTensor N) = map f g := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]

@[simp]
/-
**LinearMap.rTensor_comp_lTensor** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rTensor_comp_lTensor (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) : (f.rTensor Q).com
p (g.lTensor M) = map f g
参数：f : M ->ₗ[R] P；g : N ->ₗ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rTensor_comp_lTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (f.rTensor Q).comp (g.lTensor M) = map f g := by
  simp only [lTensor, rTensor, ← map_comp, id_comp, comp_id]

@[simp]
/-
**LinearMap.map_comp_rTensor** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：map_comp_rTensor (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (f' : S ->ₗ[R] M) : (ma
p f g).comp (f'.rTensor _) = map (f.comp f') g
参数：f : M ->ₗ[R] P；g : N ->ₗ[R] Q；f' : S ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_comp_rTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (f' : S →ₗ[R] M) :
    (map f g).comp (f'.rTensor _) = map (f.comp f') g := by
  simp only [rTensor, ← map_comp, comp_id]

@[simp]
/-
**LinearMap.map_rTensor** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：map_rTensor (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (f' : S ->ₗ[R] M) (x : S oti
mes[R] N) : map f g (f'.rTensor _ x) = map (f.comp f') g x
参数：f : M ->ₗ[R] P；g : N ->ₗ[R] Q；f' : S ->ₗ[R] M；x : S otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `LinearMap.map_comp_rTensor`：map_comp_rTensor (f : M ->ₗ[R] P) (g : N ->ₗ
[R] Q) (f' : S ->ₗ[R] M) : (map f g).comp (f'.rTensor _) = map (f.comp f') g
-/
theorem map_rTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (f' : S →ₗ[R] M) (x : S ⊗[R] N) :
    map f g (f'.rTensor _ x) = map (f.comp f') g x :=
  LinearMap.congr_fun (map_comp_rTensor _ _ _ _) x

@[simp]
/-
**LinearMap.map_comp_lTensor** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：map_comp_lTensor (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (g' : S ->ₗ[R] N) : (ma
p f g).comp (g'.lTensor _) = map f (g.comp g')
参数：f : M ->ₗ[R] P；g : N ->ₗ[R] Q；g' : S ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_comp_lTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (g' : S →ₗ[R] N) :
    (map f g).comp (g'.lTensor _) = map f (g.comp g') := by
  simp only [lTensor, ← map_comp, comp_id]

@[simp]
/-
**LinearMap.map_lTensor** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：map_lTensor (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (g' : S ->ₗ[R] N) (x : M oti
mes[R] S) : map f g (g'.lTensor M x) = map f (g ∘ₗ g') x
参数：f : M ->ₗ[R] P；g : N ->ₗ[R] Q；g' : S ->ₗ[R] N；x : M otimes[R] S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `LinearMap.map_comp_lTensor`：map_comp_lTensor (f : M ->ₗ[R] P) (g : N ->ₗ
[R] Q) (g' : S ->ₗ[R] N) : (map f g).comp (g'.lTensor _) = map f (g.comp g')
-/
lemma map_lTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (g' : S →ₗ[R] N) (x : M ⊗[R] S) :
    map f g (g'.lTensor M x) = map f (g ∘ₗ g') x :=
  LinearMap.congr_fun (map_comp_lTensor _ _ _ _) x

@[simp]
/-
**LinearMap.rTensor_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rTensor_comp_map (f' : P ->ₗ[R] S) (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) : (f'
.rTensor _).comp (map f g) = map (f'.comp f) g
参数：f' : P ->ₗ[R] S；f : M ->ₗ[R] P；g : N ->ₗ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rTensor_comp_map (f' : P →ₗ[R] S) (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (f'.rTensor _).comp (map f g) = map (f'.comp f) g := by
  simp only [rTensor, ← map_comp, id_comp]

@[simp]
/-
**LinearMap.rTensor_map** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：rTensor_map (f' : P ->ₗ[R] S) (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (x : M oti
mes[R] N) : f'.rTensor Q (map f g x) = map (f' ∘ₗ f) g x
参数：f' : P ->ₗ[R] S；f : M ->ₗ[R] P；g : N ->ₗ[R] Q；x : M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `LinearMap.rTensor_comp_map`：rTensor_comp_map (f' : P ->ₗ[R] S) (f : M ->
ₗ[R] P) (g : N ->ₗ[R] Q) : (f'.rTensor _).comp (map f g) = map (f'.comp f) g
-/
lemma rTensor_map (f' : P →ₗ[R] S) (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (x : M ⊗[R] N) :
    f'.rTensor Q (map f g x) = map (f' ∘ₗ f) g x :=
  LinearMap.congr_fun (rTensor_comp_map _ _ f g) x

@[simp]
/-
**LinearMap.lTensor_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_comp_map (g' : Q ->ₗ[R] S) (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) : (g'
.lTensor _).comp (map f g) = map f (g'.comp g)
参数：g' : Q ->ₗ[R] S；f : M ->ₗ[R] P；g : N ->ₗ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lTensor_comp_map (g' : Q →ₗ[R] S) (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (g'.lTensor _).comp (map f g) = map f (g'.comp g) := by
  simp only [lTensor, ← map_comp, id_comp]

@[simp]
/-
**LinearMap.lTensor_map** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_map (g' : Q ->ₗ[R] S) (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) (x : M oti
mes[R] N) : g'.lTensor P (map f g x) = map f (g' ∘ₗ g) x
参数：g' : Q ->ₗ[R] S；f : M ->ₗ[R] P；g : N ->ₗ[R] Q；x : M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `LinearMap.lTensor_comp_map`：lTensor_comp_map (g' : Q ->ₗ[R] S) (f : M ->
ₗ[R] P) (g : N ->ₗ[R] Q) : (g'.lTensor _).comp (map f g) = map f (g'.comp g)
-/
lemma lTensor_map (g' : Q →ₗ[R] S) (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (x : M ⊗[R] N) :
    g'.lTensor P (map f g x) = map f (g' ∘ₗ g) x :=
  LinearMap.congr_fun (lTensor_comp_map _ _ f g) x

variable {M}
/-
**LinearMap.lTensor_comp_comm** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_comp_comm (f : M ->ₗ[R] P) : lTensor N f ∘ₗ TensorProduct.comm R M
 N = TensorProduct.comm R P N ∘ₗ rTensor N f
参数：f : M ->ₗ[R] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TensorProduct.map_comp_comm_eq`：map_comp_comm_eq (f : M ->ₛₗ[σ₁₂] M₂) (g
 : N ->ₛₗ[σ₁₂] N₂) : map f g ∘ₛₗ (TensorProduct.comm R N M).toLinearMap = (Tenso
rProduct.comm R₂ N₂ …
-/
theorem lTensor_comp_comm (f : M →ₗ[R] P) :
    lTensor N f ∘ₗ TensorProduct.comm R M N = TensorProduct.comm R P N ∘ₗ rTensor N f :=
  TensorProduct.map_comp_comm_eq _ _
/-
**LinearMap.rTensor_comp_comm** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rTensor_comp_comm (f : M ->ₗ[R] P) : rTensor N f ∘ₗ TensorProduct.comm R N
 M = TensorProduct.comm R N P ∘ₗ lTensor N f
参数：f : M ->ₗ[R] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TensorProduct.map_comp_comm_eq`：map_comp_comm_eq (f : M ->ₛₗ[σ₁₂] M₂) (g
 : N ->ₛₗ[σ₁₂] N₂) : map f g ∘ₛₗ (TensorProduct.comm R N M).toLinearMap = (Tenso
rProduct.comm R₂ N₂ …
-/
theorem rTensor_comp_comm (f : M →ₗ[R] P) :
    rTensor N f ∘ₗ TensorProduct.comm R N M = TensorProduct.comm R N P ∘ₗ lTensor N f :=
  TensorProduct.map_comp_comm_eq _ _
/-
**LinearMap.lTensor_comm** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_comm (f : M ->ₗ[R] P) (x : M otimes[R] N) : lTensor N f (TensorPro
duct.comm R M N x) = TensorProduct.comm R P N (rTensor N f x)
参数：f : M ->ₗ[R] P；x : M otimes[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.lTensor_comp_comm`：lTensor_comp_comm (f : M ->ₗ[R] P) : lTenso
r N f ∘ₗ TensorProduct.comm R M N = TensorProduct.comm R P N ∘ₗ rTensor N f
-/
theorem lTensor_comm (f : M →ₗ[R] P) (x : M ⊗[R] N) :
    lTensor N f (TensorProduct.comm R M N x) = TensorProduct.comm R P N (rTensor N f x) :=
  congr($(LinearMap.lTensor_comp_comm f) _)
/-
**LinearMap.rTensor_comm** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rTensor_comm (f : M ->ₗ[R] P) (x : N otimes[R] M) : rTensor N f (TensorPro
duct.comm R N M x) = TensorProduct.comm R N P (lTensor N f x)
参数：f : M ->ₗ[R] P；x : N otimes[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.rTensor_comp_comm`：rTensor_comp_comm (f : M ->ₗ[R] P) : rTenso
r N f ∘ₗ TensorProduct.comm R N M = TensorProduct.comm R N P ∘ₗ lTensor N f
-/
theorem rTensor_comm (f : M →ₗ[R] P) (x : N ⊗[R] M) :
    rTensor N f (TensorProduct.comm R N M x) = TensorProduct.comm R N P (lTensor N f x) :=
  congr($(LinearMap.rTensor_comp_comm f) _)

@[simp]
/-
**LinearMap.rTensor_pow** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rTensor_pow (f : M ->ₗ[R] M) (n : Nat) : f.rTensor N ^ n = (f ^ n).rTensor
 N
参数：f : M ->ₗ[R] M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.map_pow`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Typ
e u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [i
nst_3 : _ro…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.End.id_pow`：id_pow (n : Nat) : (id : End R M) ^ n = .id
-/
theorem rTensor_pow (f : M →ₗ[R] M) (n : ℕ) : f.rTensor N ^ n = (f ^ n).rTensor N := by
  have h := TensorProduct.map_pow f (id : N →ₗ[R] N) n
  rwa [Module.End.id_pow] at h

@[simp]
/-
**LinearMap.lTensor_pow** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_pow (f : N ->ₗ[R] N) (n : Nat) : f.lTensor M ^ n = (f ^ n).lTensor
 M
参数：f : N ->ₗ[R] N；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.map_pow`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Typ
e u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [i
nst_3 : _ro…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.End.id_pow`：id_pow (n : Nat) : (id : End R M) ^ n = .id
-/
theorem lTensor_pow (f : N →ₗ[R] N) (n : ℕ) : f.lTensor M ^ n = (f ^ n).lTensor M := by
  have h := TensorProduct.map_pow (id : M →ₗ[R] M) f n
  rwa [Module.End.id_pow] at h

end LinearMap

namespace LinearEquiv

variable {N}

/-- `LinearEquiv.lTensor M f : M ⊗ N ≃ₗ M ⊗ P` is the natural linear equivalence
induced by `f : N ≃ₗ P`. -/
/-
**LinearEquiv.lTensor** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：lTensor (f : N ≃ₗ[R] P) : M otimes[R] N ≃ₗ[R] M otimes[R] P
参数：f : N ≃ₗ[R] P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearEquiv.lTensor M f : M ⊗ N ≃ₗ M ⊗ P` is the natural linear equivalence
induced by `f : N ≃ₗ P`.
-/
def lTensor (f : N ≃ₗ[R] P) : M ⊗[R] N ≃ₗ[R] M ⊗[R] P := TensorProduct.congr (refl R M) f

/-- `LinearEquiv.rTensor M f : N₁ ⊗ M ≃ₗ N₂ ⊗ M` is the natural linear equivalence
induced by `f : N₁ ≃ₗ N₂`. -/
/-
**LinearEquiv.rTensor** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：rTensor (f : N ≃ₗ[R] P) : N otimes[R] M ≃ₗ[R] P otimes[R] M
参数：f : N ≃ₗ[R] P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearEquiv.rTensor M f : N₁ ⊗ M ≃ₗ N₂ ⊗ M` is the natural linear equivalence
induced by `f : N₁ ≃ₗ N₂`.
-/
def rTensor (f : N ≃ₗ[R] P) : N ⊗[R] M ≃ₗ[R] P ⊗[R] M := TensorProduct.congr f (refl R M)

variable (g : P ≃ₗ[R] Q) (f : N ≃ₗ[R] P) (m : M) (n : N) (p : P) (x : M ⊗[R] N) (y : N ⊗[R] M)
/-
**LinearEquiv.symm_lTensor** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (M : Type u_7) {N : Type u_8} {P 
: Type u_9} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : Ad
dCommMonoid P] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst
_6 : _root_.Module R P] (f : N ≃ₗ[R] P), (LinearEquiv.lTensor M f).symm = Linear
Equiv.lTensor M f.symm
参数：M : Type u_7；f : N ≃ₗ[R] P；LinearEquiv.lTensor M f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem symm_lTensor : (f.lTensor M).symm = f.symm.lTensor M := rfl
/-
**LinearEquiv.symm_rTensor** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (M : Type u_7) {N : Type u_8} {P 
: Type u_9} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : Ad
dCommMonoid P] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst
_6 : _root_.Module R P] (f : N ≃ₗ[R] P), (LinearEquiv.rTensor M f).symm = Linear
Equiv.rTensor M f.symm
参数：M : Type u_7；f : N ≃ₗ[R] P；LinearEquiv.rTensor M f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem symm_rTensor : (f.rTensor M).symm = f.symm.rTensor M := rfl
/-
**LinearEquiv.coe_lTensor** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (M : Type u_7) {N : Type u_8} {P 
: Type u_9} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : Ad
dCommMonoid P] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst
_6 : _root_.Module R P] (f : N ≃ₗ[R] P), ↑(LinearEquiv.lTensor M f) = LinearMap.
lTensor M ↑f
参数：M : Type u_7；f : N ≃ₗ[R] P；LinearEquiv.lTensor M f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_lTensor : lTensor M f = (f : N →ₗ[R] P).lTensor M := rfl

@[deprecated "use symm_lTensor and coe_lTensor" (since := "2026-07-04")]
/-
**LinearEquiv.coe_lTensor_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_lTensor_symm : (lTensor M f).symm = (f.symm : P ->ₗ[R] N).lTensor M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_lTensor_symm : (lTensor M f).symm = (f.symm : P →ₗ[R] N).lTensor M := rfl
/-
**LinearEquiv.coe_rTensor** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (M : Type u_7) {N : Type u_8} {P 
: Type u_9} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : Ad
dCommMonoid P] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst
_6 : _root_.Module R P] (f : N ≃ₗ[R] P), ↑(LinearEquiv.rTensor M f) = LinearMap.
rTensor M ↑f
参数：M : Type u_7；f : N ≃ₗ[R] P；LinearEquiv.rTensor M f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_rTensor : rTensor M f = (f : N →ₗ[R] P).rTensor M := rfl

@[deprecated "use symm_rTensor and coe_rTensor" (since := "2026-07-04")]
/-
**LinearEquiv.coe_rTensor_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：coe_rTensor_symm : (rTensor M f).symm = (f.symm : P ->ₗ[R] N).rTensor M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_rTensor_symm : (rTensor M f).symm = (f.symm : P →ₗ[R] N).rTensor M := rfl
/-
**LinearEquiv.lTensor_tmul** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (M : Type u_7) {N : Type u_8} {P 
: Type u_9} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : Ad
dCommMonoid P] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst
_6 : _root_.Module R P] (f : N ≃ₗ[R] P) (m : M) (n : N), (LinearEquiv.lTensor M 
f) (m ⊗ₜ[R] n) = m ⊗ₜ[R] f n
参数：M : Type u_7；f : N ≃ₗ[R] P；m : M；n : N；LinearEquiv.lTensor M f；m ⊗ₜ[R] n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem lTensor_tmul : f.lTensor M (m ⊗ₜ n) = m ⊗ₜ f n := rfl

@[deprecated "use symm_lTensor and lTensor_tmul" (since := "2026-07-04")]
/-
**LinearEquiv.lTensor_symm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：lTensor_symm_tmul : (f.lTensor M).symm (m otimesₜ p) = m otimesₜ f.symm p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lTensor_symm_tmul : (f.lTensor M).symm (m ⊗ₜ p) = m ⊗ₜ f.symm p := rfl
/-
**LinearEquiv.rTensor_tmul** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (M : Type u_7) {N : Type u_8} {P 
: Type u_9} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : Ad
dCommMonoid P] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst
_6 : _root_.Module R P] (f : N ≃ₗ[R] P) (m : M) (n : N), (LinearEquiv.rTensor M 
f) (n ⊗ₜ[R] m) = f n ⊗ₜ[R] m
参数：M : Type u_7；f : N ≃ₗ[R] P；m : M；n : N；LinearEquiv.rTensor M f；n ⊗ₜ[R] m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem rTensor_tmul : f.rTensor M (n ⊗ₜ m) = f n ⊗ₜ m := rfl

@[deprecated "use symm_rTensor and rTensor_tmul" (since := "2026-07-04")]
/-
**LinearEquiv.rTensor_symm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：rTensor_symm_tmul : (f.rTensor M).symm (p otimesₜ m) = f.symm p otimesₜ m
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rTensor_symm_tmul : (f.rTensor M).symm (p ⊗ₜ m) = f.symm p ⊗ₜ m := rfl
/-
**LinearEquiv.comm_trans_rTensor_trans_comm_eq** 是 Mathlib 中的一个引理，位于命名空间 `Linear
Equiv`。
形式化陈述：comm_trans_rTensor_trans_comm_eq (g : N ≃ₗ[R] P) : TensorProduct.comm R Q 
N ≪≫ₗ rTensor Q g ≪≫ₗ TensorProduct.comm R P Q = lTensor Q g
参数：g : N ≃ₗ[R] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
-/
lemma comm_trans_rTensor_trans_comm_eq (g : N ≃ₗ[R] P) :
    TensorProduct.comm R Q N ≪≫ₗ rTensor Q g ≪≫ₗ TensorProduct.comm R P Q = lTensor Q g :=
  toLinearMap_injective <| TensorProduct.ext rfl
/-
**LinearEquiv.comm_trans_lTensor_trans_comm_eq** 是 Mathlib 中的一个引理，位于命名空间 `Linear
Equiv`。
形式化陈述：comm_trans_lTensor_trans_comm_eq (g : N ≃ₗ[R] P) : TensorProduct.comm R N 
Q ≪≫ₗ lTensor Q g ≪≫ₗ TensorProduct.comm R Q P = rTensor Q g
参数：g : N ≃ₗ[R] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `TensorProduct.ext`：ext {g h : M otimes N ->ₛₗ[σ₁₂] P₂} (H : (mk R M N).c
ompr₂ₛₗ g = (mk R M N).compr₂ₛₗ h) : g = h
-/
lemma comm_trans_lTensor_trans_comm_eq (g : N ≃ₗ[R] P) :
    TensorProduct.comm R N Q ≪≫ₗ lTensor Q g ≪≫ₗ TensorProduct.comm R Q P = rTensor Q g :=
  toLinearMap_injective <| TensorProduct.ext rfl
/-
**LinearEquiv.lTensor_trans** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：lTensor_trans : (f ≪≫ₗ g).lTensor M = f.lTensor M ≪≫ₗ g.lTensor M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `LinearMap.lTensor_comp`：lTensor_comp : (g.comp f).lTensor M = (g.lTensor
 M).comp (f.lTensor M)
-/
theorem lTensor_trans : (f ≪≫ₗ g).lTensor M = f.lTensor M ≪≫ₗ g.lTensor M :=
  toLinearMap_injective <| LinearMap.lTensor_comp M _ _
/-
**LinearEquiv.lTensor_trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：lTensor_trans_apply : (f ≪≫ₗ g).lTensor M x = g.lTensor M (f.lTensor M x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.lTensor_comp_apply`：lTensor_comp_apply (x : M otimes[R] N) : (
g.comp f).lTensor M x = (g.lTensor M) ((f.lTensor M) x)
-/
theorem lTensor_trans_apply : (f ≪≫ₗ g).lTensor M x = g.lTensor M (f.lTensor M x) :=
  LinearMap.lTensor_comp_apply M _ _ x
/-
**LinearEquiv.rTensor_trans** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：rTensor_trans : (f ≪≫ₗ g).rTensor M = f.rTensor M ≪≫ₗ g.rTensor M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `LinearMap.rTensor_comp`：rTensor_comp : (g.comp f).rTensor M = (g.rTensor
 M).comp (f.rTensor M)
-/
theorem rTensor_trans : (f ≪≫ₗ g).rTensor M = f.rTensor M ≪≫ₗ g.rTensor M :=
  toLinearMap_injective <| LinearMap.rTensor_comp M _ _
/-
**LinearEquiv.rTensor_trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：rTensor_trans_apply : (f ≪≫ₗ g).rTensor M y = g.rTensor M (f.rTensor M y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.rTensor_comp_apply`：rTensor_comp_apply (x : N otimes[R] M) : (
g.comp f).rTensor M x = (g.rTensor M) ((f.rTensor M) x)
-/
theorem rTensor_trans_apply : (f ≪≫ₗ g).rTensor M y = g.rTensor M (f.rTensor M y) :=
  LinearMap.rTensor_comp_apply M _ _ y
/-
**LinearEquiv.lTensor_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：lTensor_mul (f g : N ≃ₗ[R] N) : (f * g).lTensor M = f.lTensor M * g.lTenso
r M
参数：f g : N ≃ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.lTensor_trans`：lTensor_trans : (f ≪≫ₗ g).lTensor M = f.lTens
or M ≪≫ₗ g.lTensor M
-/
theorem lTensor_mul (f g : N ≃ₗ[R] N) : (f * g).lTensor M = f.lTensor M * g.lTensor M :=
  lTensor_trans M f g
/-
**LinearEquiv.rTensor_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：rTensor_mul (f g : N ≃ₗ[R] N) : (f * g).rTensor M = f.rTensor M * g.rTenso
r M
参数：f g : N ≃ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.rTensor_trans`：rTensor_trans : (f ≪≫ₗ g).rTensor M = f.rTens
or M ≪≫ₗ g.rTensor M
-/
theorem rTensor_mul (f g : N ≃ₗ[R] N) : (f * g).rTensor M = f.rTensor M * g.rTensor M :=
  rTensor_trans M f g

variable (N)
/-
**LinearEquiv.lTensor_refl** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (M : Type u_7) (N : Type u_8) [in
st_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M
] [inst_4 : _root_.Module R N],   LinearEquiv.lTensor M (LinearEquiv.refl R N) =
 LinearEquiv.refl R (TensorProduct R M N)
参数：M : Type u_7；N : Type u_8；LinearEquiv.refl R N；TensorProduct R M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.congr_refl_refl`：∀ {R : Type u_1} [inst : CommSemiring R] 
{M : Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMono
id N] [inst_3 : _ro…
-/
@[simp] theorem lTensor_refl : (refl R N).lTensor M = refl R _ := TensorProduct.congr_refl_refl
/-
**LinearEquiv.lTensor_refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：lTensor_refl_apply : (refl R N).lTensor M x = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.lTensor_refl`：∀ {R : Type u_1} [inst : CommSemiring R] (M : 
Type u_7) (N : Type u_8) [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N]
 [inst_3 : _ro…
· 使用定理 `LinearEquiv.refl_apply`：refl_apply [Module R M] (x : M) : refl R M x = x
-/
theorem lTensor_refl_apply : (refl R N).lTensor M x = x := by rw [lTensor_refl, refl_apply]
/-
**LinearEquiv.rTensor_refl** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (M : Type u_7) (N : Type u_8) [in
st_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M
] [inst_4 : _root_.Module R N],   LinearEquiv.rTensor M (LinearEquiv.refl R N) =
 LinearEquiv.refl R (TensorProduct R N M)
参数：M : Type u_7；N : Type u_8；LinearEquiv.refl R N；TensorProduct R N M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.congr_refl_refl`：∀ {R : Type u_1} [inst : CommSemiring R] 
{M : Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMono
id N] [inst_3 : _ro…
-/
@[simp] theorem rTensor_refl : (refl R N).rTensor M = refl R _ := TensorProduct.congr_refl_refl
/-
**LinearEquiv.rTensor_refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：rTensor_refl_apply : (refl R N).rTensor M y = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.rTensor_refl`：∀ {R : Type u_1} [inst : CommSemiring R] (M : 
Type u_7) (N : Type u_8) [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N]
 [inst_3 : _ro…
· 使用定理 `LinearEquiv.refl_apply`：refl_apply [Module R M] (x : M) : refl R M x = x
-/
theorem rTensor_refl_apply : (refl R N).rTensor M y = y := by rw [rTensor_refl, refl_apply]

variable {N}
/-
**LinearEquiv.rTensor_trans_lTensor** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (M : Type u_7) {N : Type u_8} {P 
: Type u_9} {Q : Type u_10}   [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid
 N] [inst_3 : AddCommMonoid P] [inst_4 : AddCommMonoid Q]   [inst_5 : _root_.Mod
ule R M] [inst_6 : _root_.Module R N] [inst_7 : _root_.Module R P] [inst_8 : _ro
ot_.Module R Q]   (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q), LinearEquiv.rTensor N f ≪≫ₗ L
inearEquiv.lTensor P g = TensorProduct.congr f g
参数：M : Type u_7；f : M ≃ₗ[R] P；g : N ≃ₗ[R] Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `LinearMap.lTensor_comp_rTensor`：lTensor_comp_rTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (g.lTensor P).comp (f.rTensor N) = map f g
-/
@[simp] theorem rTensor_trans_lTensor (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    f.rTensor N ≪≫ₗ g.lTensor P = TensorProduct.congr f g :=
  toLinearMap_injective <| LinearMap.lTensor_comp_rTensor M _ _
/-
**LinearEquiv.lTensor_trans_rTensor** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (M : Type u_7) {N : Type u_8} {P 
: Type u_9} {Q : Type u_10}   [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid
 N] [inst_3 : AddCommMonoid P] [inst_4 : AddCommMonoid Q]   [inst_5 : _root_.Mod
ule R M] [inst_6 : _root_.Module R N] [inst_7 : _root_.Module R P] [inst_8 : _ro
ot_.Module R Q]   (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q), LinearEquiv.lTensor M g ≪≫ₗ L
inearEquiv.rTensor Q f = TensorProduct.congr f g
参数：M : Type u_7；f : M ≃ₗ[R] P；g : N ≃ₗ[R] Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `LinearMap.rTensor_comp_lTensor`：rTensor_comp_lTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (f.rTensor Q).comp (g.lTensor M) = map f g
-/
@[simp] theorem lTensor_trans_rTensor (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    g.lTensor M ≪≫ₗ f.rTensor Q = TensorProduct.congr f g :=
  toLinearMap_injective <| LinearMap.rTensor_comp_lTensor M _ _
/-
**LinearEquiv.rTensor_trans_congr** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (M : Type u_7) {N : Type u_8} {P 
: Type u_9} {Q : Type u_10} {S : Type u_11}   [inst_1 : AddCommMonoid M] [inst_2
 : AddCommMonoid N] [inst_3 : AddCommMonoid P] [inst_4 : AddCommMonoid Q]   [ins
t_5 : AddCommMonoid S] [inst_6 : _root_.Module R M] [inst_7 : _root_.Module R N]
 [inst_8 : _root_.Module R S]   [inst_9 : _root_.Module R P] [inst_10 : _root_.M
odule R Q] (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (f' : S ≃ₗ[R] M),   LinearEquiv.rTens
or N f' ≪≫ₗ TensorProduct.congr f g = TensorProduct.congr (f' ≪≫ₗ f) g
参数：M : Type u_7；f : M ≃ₗ[R] P；g : N ≃ₗ[R] Q；f' : S ≃ₗ[R] M；f' ≪≫ₗ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `LinearMap.map_comp_rTensor`：map_comp_rTensor (f : M ->ₗ[R] P) (g : N ->ₗ
[R] Q) (f' : S ->ₗ[R] M) : (map f g).comp (f'.rTensor _) = map (f.comp f') g
-/
@[simp] theorem rTensor_trans_congr (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (f' : S ≃ₗ[R] M) :
    f'.rTensor _ ≪≫ₗ TensorProduct.congr f g = TensorProduct.congr (f' ≪≫ₗ f) g :=
  toLinearMap_injective <| LinearMap.map_comp_rTensor M _ _ _
/-
**LinearEquiv.lTensor_trans_congr** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (M : Type u_7) {N : Type u_8} {P 
: Type u_9} {Q : Type u_10} {S : Type u_11}   [inst_1 : AddCommMonoid M] [inst_2
 : AddCommMonoid N] [inst_3 : AddCommMonoid P] [inst_4 : AddCommMonoid Q]   [ins
t_5 : AddCommMonoid S] [inst_6 : _root_.Module R M] [inst_7 : _root_.Module R N]
 [inst_8 : _root_.Module R S]   [inst_9 : _root_.Module R P] [inst_10 : _root_.M
odule R Q] (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (g' : S ≃ₗ[R] N),   LinearEquiv.lTens
or M g' ≪≫ₗ TensorProduct.congr f g = TensorProduct.congr f (g' ≪≫ₗ g)
参数：M : Type u_7；f : M ≃ₗ[R] P；g : N ≃ₗ[R] Q；g' : S ≃ₗ[R] N；g' ≪≫ₗ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `LinearMap.map_comp_lTensor`：map_comp_lTensor (f : M ->ₗ[R] P) (g : N ->ₗ
[R] Q) (g' : S ->ₗ[R] N) : (map f g).comp (g'.lTensor _) = map f (g.comp g')
-/
@[simp] theorem lTensor_trans_congr (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (g' : S ≃ₗ[R] N) :
    g'.lTensor _ ≪≫ₗ TensorProduct.congr f g = TensorProduct.congr f (g' ≪≫ₗ g) :=
  toLinearMap_injective <| LinearMap.map_comp_lTensor M _ _ _
/-
**LinearEquiv.congr_trans_rTensor** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (M : Type u_7) {N : Type u_8} {P 
: Type u_9} {Q : Type u_10} {S : Type u_11}   [inst_1 : AddCommMonoid M] [inst_2
 : AddCommMonoid N] [inst_3 : AddCommMonoid P] [inst_4 : AddCommMonoid Q]   [ins
t_5 : AddCommMonoid S] [inst_6 : _root_.Module R M] [inst_7 : _root_.Module R N]
 [inst_8 : _root_.Module R S]   [inst_9 : _root_.Module R P] [inst_10 : _root_.M
odule R Q] (f' : P ≃ₗ[R] S) (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q),   TensorProduct.con
gr f g ≪≫ₗ LinearEquiv.rTensor Q f' = TensorProduct.congr (f ≪≫ₗ f') g
参数：M : Type u_7；f' : P ≃ₗ[R] S；f : M ≃ₗ[R] P；g : N ≃ₗ[R] Q；f ≪≫ₗ f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `LinearMap.rTensor_comp_map`：rTensor_comp_map (f' : P ->ₗ[R] S) (f : M ->
ₗ[R] P) (g : N ->ₗ[R] Q) : (f'.rTensor _).comp (map f g) = map (f'.comp f) g
-/
@[simp] theorem congr_trans_rTensor (f' : P ≃ₗ[R] S) (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    TensorProduct.congr f g ≪≫ₗ f'.rTensor _ = TensorProduct.congr (f ≪≫ₗ f') g :=
  toLinearMap_injective <| LinearMap.rTensor_comp_map M _ _ _
/-
**LinearEquiv.congr_trans_lTensor** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (M : Type u_7) {N : Type u_8} {P 
: Type u_9} {Q : Type u_10} {S : Type u_11}   [inst_1 : AddCommMonoid M] [inst_2
 : AddCommMonoid N] [inst_3 : AddCommMonoid P] [inst_4 : AddCommMonoid Q]   [ins
t_5 : AddCommMonoid S] [inst_6 : _root_.Module R M] [inst_7 : _root_.Module R N]
 [inst_8 : _root_.Module R S]   [inst_9 : _root_.Module R P] [inst_10 : _root_.M
odule R Q] (g' : Q ≃ₗ[R] S) (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q),   TensorProduct.con
gr f g ≪≫ₗ LinearEquiv.lTensor P g' = TensorProduct.congr f (g ≪≫ₗ g')
参数：M : Type u_7；g' : Q ≃ₗ[R] S；f : M ≃ₗ[R] P；g : N ≃ₗ[R] Q；g ≪≫ₗ g'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.toLinearMap_injective`：toLinearMap_injective : Injective (to
LinearMap : (M ≃ₛₗ[σ] M₂) -> M ->ₛₗ[σ] M₂)
· 使用定理 `LinearMap.lTensor_comp_map`：lTensor_comp_map (g' : Q ->ₗ[R] S) (f : M ->
ₗ[R] P) (g : N ->ₗ[R] Q) : (g'.lTensor _).comp (map f g) = map f (g'.comp g)
-/
@[simp] theorem congr_trans_lTensor (g' : Q ≃ₗ[R] S) (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) :
    TensorProduct.congr f g ≪≫ₗ g'.lTensor _ = TensorProduct.congr f (g ≪≫ₗ g') :=
  toLinearMap_injective <| LinearMap.lTensor_comp_map M _ _ _

variable {M}
/-
**LinearEquiv.rTensor_pow** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Type u_7} {N : Type u_8} [in
st_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M
] [inst_4 : _root_.Module R N] (f : M ≃ₗ[R] M) (n : ℕ),   LinearEquiv.rTensor N 
f ^ n = LinearEquiv.rTensor N (f ^ n)
参数：f : M ≃ₗ[R] M；n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `TensorProduct.congr_pow`：∀ {R : Type u_1} [inst : CommSemiring R] {M : T
ype u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] 
[inst_3 : _ro…
-/
@[simp] theorem rTensor_pow (f : M ≃ₗ[R] M) (n : ℕ) : f.rTensor N ^ n = (f ^ n).rTensor N := by
  simpa only [one_pow] using! TensorProduct.congr_pow f (1 : N ≃ₗ[R] N) n
/-
**LinearEquiv.rTensor_zpow** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Type u_7} {N : Type u_8} [in
st_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M
] [inst_4 : _root_.Module R N] (f : M ≃ₗ[R] M) (n : ℤ),   LinearEquiv.rTensor N 
f ^ n = LinearEquiv.rTensor N (f ^ n)
参数：f : M ≃ₗ[R] M；n : ℤ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `TensorProduct.congr_zpow`：∀ {R : Type u_1} [inst : CommSemiring R] {M : 
Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N]
 [inst_3 : _ro…
-/
@[simp] theorem rTensor_zpow (f : M ≃ₗ[R] M) (n : ℤ) : f.rTensor N ^ n = (f ^ n).rTensor N := by
  simpa only [one_zpow] using! TensorProduct.congr_zpow f (1 : N ≃ₗ[R] N) n
/-
**LinearEquiv.lTensor_pow** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Type u_7} {N : Type u_8} [in
st_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M
] [inst_4 : _root_.Module R N] (f : N ≃ₗ[R] N) (n : ℕ),   LinearEquiv.lTensor M 
f ^ n = LinearEquiv.lTensor M (f ^ n)
参数：f : N ≃ₗ[R] N；n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `TensorProduct.congr_pow`：∀ {R : Type u_1} [inst : CommSemiring R] {M : T
ype u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] 
[inst_3 : _ro…
-/
@[simp] theorem lTensor_pow (f : N ≃ₗ[R] N) (n : ℕ) : f.lTensor M ^ n = (f ^ n).lTensor M := by
  simpa only [one_pow] using! TensorProduct.congr_pow (1 : M ≃ₗ[R] M) f n
/-
**LinearEquiv.lTensor_zpow** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Type u_7} {N : Type u_8} [in
st_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M
] [inst_4 : _root_.Module R N] (f : N ≃ₗ[R] N) (n : ℤ),   LinearEquiv.lTensor M 
f ^ n = LinearEquiv.lTensor M (f ^ n)
参数：f : N ≃ₗ[R] N；n : ℤ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `TensorProduct.congr_zpow`：∀ {R : Type u_1} [inst : CommSemiring R] {M : 
Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N]
 [inst_3 : _ro…
-/
@[simp] theorem lTensor_zpow (f : N ≃ₗ[R] N) (n : ℤ) : f.lTensor M ^ n = (f ^ n).lTensor M := by
  simpa only [one_zpow] using! TensorProduct.congr_zpow (1 : M ≃ₗ[R] M) f n

end LinearEquiv

end Semiring

section Ring

variable {R : Type*} [CommSemiring R]
variable {M : Type*} {N : Type*} {P : Type*} {Q : Type*} {S : Type*}
variable [AddCommGroup M] [AddCommMonoid N] [AddCommGroup P] [AddCommMonoid Q]
variable [Module R M] [Module R N] [Module R P] [Module R Q]

namespace LinearMap

@[simp]
/-
**LinearMap.lTensor_sub** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_sub (f g : N ->ₗ[R] P) : (f - g).lTensor M = f.lTensor M - g.lTens
or M
参数：f g : N ->ₗ[R] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_sub`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : 
Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M]
 [inst_…
-/
theorem lTensor_sub (f g : N →ₗ[R] P) : (f - g).lTensor M = f.lTensor M - g.lTensor M := by
  simp_rw [← coe_lTensorHom]
  exact (lTensorHom (R := R) (N := N) (P := P) M).map_sub f g

@[simp]
/-
**LinearMap.rTensor_sub** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rTensor_sub (f g : N ->ₗ[R] P) : (f - g).rTensor Q = f.rTensor Q - g.rTens
or Q
参数：f g : N ->ₗ[R] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_sub`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : 
Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M]
 [inst_…
-/
theorem rTensor_sub (f g : N →ₗ[R] P) : (f - g).rTensor Q = f.rTensor Q - g.rTensor Q := by
  simp only [← coe_rTensorHom]
  exact (rTensorHom (R := R) (N := N) (P := P) Q).map_sub f g

@[simp]
/-
**LinearMap.lTensor_neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lTensor_neg (f : N ->ₗ[R] P) : (-f).lTensor M = -f.lTensor M
参数：f : N ->ₗ[R] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_neg`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : 
Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M]
 [inst_…
-/
theorem lTensor_neg (f : N →ₗ[R] P) : (-f).lTensor M = -f.lTensor M := by
  simp only [← coe_lTensorHom]
  exact (lTensorHom (R := R) (N := N) (P := P) M).map_neg f

@[simp]
/-
**LinearMap.rTensor_neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rTensor_neg (f : N ->ₗ[R] P) : (-f).rTensor Q = -f.rTensor Q
参数：f : N ->ₗ[R] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_neg`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : 
Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M]
 [inst_…
-/
theorem rTensor_neg (f : N →ₗ[R] P) : (-f).rTensor Q = -f.rTensor Q := by
  simp only [← coe_rTensorHom]
  exact (rTensorHom (R := R) (N := N) (P := P) Q).map_neg f

end LinearMap

end Ring

namespace Equiv
variable {R A A' B B' : Type*} [CommSemiring R]
  [AddCommMonoid A'] [AddCommMonoid B'] [Module R A'] [Module R B']

variable (R) in
open TensorProduct in
/-
**Equiv.tensorProductComm_def** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：tensorProductComm_def (eA : A ≃ A') (eB : B ≃ B') : letI
参数：eA : A ≃ A'；eB : B ≃ B'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
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
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
lemma tensorProductComm_def (eA : A ≃ A') (eB : B ≃ B') :
    letI := eA.addCommMonoid
    letI := eB.addCommMonoid
    letI := eA.module R
    letI := eB.module R
    TensorProduct.comm R A B = .trans
      (congr (eA.linearEquiv R) (eB.linearEquiv R)) (.trans
      (TensorProduct.comm R A' B') <| congr (eB.linearEquiv R).symm (eA.linearEquiv R).symm) := by
  ext x; induction x <;> simp [*]

end Equiv

