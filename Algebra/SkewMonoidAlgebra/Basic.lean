/-
Copyright (c) 2024 María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos Fernández, Xavier Généreux
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Algebra.NonUnitalHom

/-!
# Skew Monoid Algebras

Given a monoid `G` acting on a ring `k`, the skew monoid algebra of `G` over `k` is the set
of finitely supported functions `f : G → k` for which addition is defined pointwise and
multiplication of two elements `f` and `g` is given by the finitely supported function whose
value at `a` is the sum of `f x * (x • g y)` over all pairs `x, y` such that `x * y = a`,
where `•` denotes the action of `G` on `k`. When this action is trivial, this product is
the usual convolution product.

In fact the construction of the skew monoid algebra makes sense when `G` is not even a monoid, but
merely a magma, i.e., when `G` carries a multiplication which is not required to satisfy any
conditions at all, and `k` is a not-necessarily-associative semiring. In this case the construction
yields a not-necessarily-unital, not-necessarily-associative algebra.

## Main Definitions
- `SkewMonoidAlgebra k G`: the skew monoid algebra of `G` over `k` is the type of finite formal
  `k`-linear combinations of terms of `G`, endowed with a skewed convolution product.

-/

@[expose] public section


noncomputable section

/-- The skew monoid algebra of `G` over `k` is the type of finite formal `k`-linear
combinations of terms of `G`, endowed with a skewed convolution product. -/
/-
**SkewMonoidAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(k : Type u_1) → Type u_2 → [Zero k] → Type (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The skew monoid algebra of `G` over `k` is the type of finite formal `k`-linear
combinations of terms of `G`, endowed with a skewed convolution product.
-/
structure SkewMonoidAlgebra (k : Type*) (G : Type*) [Zero k] where
  /-- The natural map from `G →₀ k` to `SkewMonoidAlgebra k G`. -/
  ofCoeff ::
  /-- The natural map from `SkewMonoidAlgebra k G` to `G →₀ k`. -/
  coeff : G →₀ k

open Function
namespace SkewMonoidAlgebra

initialize_simps_projections SkewMonoidAlgebra (as_prefix coeff)

@[deprecated (since := "2026-07-06"), reducible] alias ofFinsupp := ofCoeff
@[deprecated (since := "2026-07-06"), reducible] alias toFinsupp := coeff

variable {k G : Type*}

section AddMonoid

variable [AddMonoid k]

/-
**SkewMonoidAlgebra.eta** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} [inst : AddMonoid k] (f : SkewMonoidAlgebr
a k G), { coeff := f.coeff } = f
参数：f : SkewMonoidAlgebra k G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma eta (f : SkewMonoidAlgebra k G) : ofCoeff f.coeff = f := rfl
/-
**SkewMonoidAlgebra.coeff_ofCoeff** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} [inst : AddMonoid k] (f : G →₀ k), { coeff
 := f }.coeff = f
参数：f : G →₀ k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coeff_ofCoeff (f : G →₀ k) : coeff (ofCoeff f) = f := rfl

set_option backward.privateInPublic true in
@[irreducible]
/-
**SkewMonoidAlgebra.add** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def add :
    SkewMonoidAlgebra k G → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

set_option backward.privateInPublic true in
/-
**SkewMonoidAlgebra.smul** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def smul {S : Type*} [SMulZeroClass S k] :
    S → SkewMonoidAlgebra k G → SkewMonoidAlgebra k G
  | s, ⟨b⟩ => ⟨s • b⟩
/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (SkewMonoidAlgebra k G) := ⟨⟨0⟩⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (SkewMonoidAlgebra k G) := ⟨add⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Type*} [SMulZeroClass S k] :
    SMulZeroClass S (SkewMonoidAlgebra k G) where
  smul s f := smul s f
  smul_zero a := by exact congr_arg ofCoeff (smul_zero a)

@[simp]
/-
**SkewMonoidAlgebra.ofCoeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：ofCoeff_zero : (⟨0⟩ : SkewMonoidAlgebra k G) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofCoeff_zero : (⟨0⟩ : SkewMonoidAlgebra k G) = 0 := rfl

@[deprecated (since := "2026-07-04")] alias ofFinsupp_zero := ofCoeff_zero

@[simp]
/-
**SkewMonoidAlgebra.ofCoeff_add** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：ofCoeff_add {a b} : (⟨a + b⟩ : SkewMonoidAlgebra k G) = ⟨a⟩ + ⟨b⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Algebra.SkewMonoidAlgebra.Basic.0.SkewMonoidAlgebra.add
.eq_1`：∀ {k : Type u_1} {G : Type u_2} [inst : AddMonoid k] (a b : G →₀ k),   Sk
ewMonoidAlgebra.add✝ { coeff := a } { coeff := b } = { coeff := a +…
-/
theorem ofCoeff_add {a b} : (⟨a + b⟩ : SkewMonoidAlgebra k G) = ⟨a⟩ + ⟨b⟩ :=
  show _ = add _ _ by rw [add]

@[deprecated (since := "2026-07-04")] alias ofFinsupp_add := ofCoeff_add

@[simp]
/-
**SkewMonoidAlgebra.ofCoeff_smul** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：ofCoeff_smul {S : Type*} [SMulZeroClass S k] (a : S) (b : G ->₀ k) : (⟨a •
 b⟩ : SkewMonoidAlgebra k G) = (a • ⟨b⟩ : SkewMonoidAlgebra k G)
参数：a : S；b : G ->₀ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Algebra.SkewMonoidAlgebra.Basic.0.SkewMonoidAlgebra.smu
l.eq_1`：∀ {k : Type u_1} {G : Type u_2} [inst : AddMonoid k] {S : Type u_3} [ins
t_1 : SMulZeroClass S k] (x : S) (b : G →₀ k),   SkewMonoidAlgebra.s…
-/
theorem ofCoeff_smul {S : Type*} [SMulZeroClass S k] (a : S) (b : G →₀ k) :
    (⟨a • b⟩ : SkewMonoidAlgebra k G) = (a • ⟨b⟩ : SkewMonoidAlgebra k G) :=
  show _ = smul _ _ by rw [smul]

@[deprecated (since := "2026-07-04")] alias ofFinsupp_smul := ofCoeff_smul

@[simp]
/-
**SkewMonoidAlgebra.coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：coeff_zero : (0 : SkewMonoidAlgebra k G).coeff = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_zero : (0 : SkewMonoidAlgebra k G).coeff = 0 := rfl

@[deprecated (since := "2026-07-04")] alias toFinsupp_zero := coeff_zero

@[simp]
/-
**SkewMonoidAlgebra.coeff_add** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：coeff_add (a b : SkewMonoidAlgebra k G) : (a + b).coeff = a.coeff + b.coef
f
参数：a b : SkewMonoidAlgebra k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SkewMonoidAlgebra.ofCoeff_add`：ofCoeff_add {a b} : (⟨a + b⟩ : SkewMonoid
Algebra k G) = ⟨a⟩ + ⟨b⟩
-/
theorem coeff_add (a b : SkewMonoidAlgebra k G) :
    (a + b).coeff = a.coeff + b.coeff := by
  rw [← ofCoeff_add]

@[deprecated (since := "2026-07-04")] alias toFinsupp_add := coeff_add

@[simp]
/-
**SkewMonoidAlgebra.coeff_smul** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：coeff_smul {S : Type*} [SMulZeroClass S k] (a : S) (b : SkewMonoidAlgebra 
k G) : (a • b).coeff = a • b.coeff
参数：a : S；b : SkewMonoidAlgebra k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SkewMonoidAlgebra.ofCoeff_smul`：ofCoeff_smul {S : Type*} [SMulZeroClass 
S k] (a : S) (b : G ->₀ k) : (⟨a • b⟩ : SkewMonoidAlgebra k G) = (a • ⟨b⟩ : Skew
MonoidAlgebra k G)
-/
theorem coeff_smul {S : Type*} [SMulZeroClass S k] (a : S) (b : SkewMonoidAlgebra k G) :
    (a • b).coeff = a • b.coeff := by
  rw [← ofCoeff_smul]

@[deprecated (since := "2026-07-04")] alias toFinsupp_smul := coeff_smul
/-
**SkewMonoidAlgebra._root_.IsSMulRegular.skewMonoidAlgebra** 是 Mathlib 中的一个定理，位于
命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsSMulRegular.skewMonoidAlgebra {S : Type*} [Monoid S] [DistribMulAction S k] {a : S}
    (ha : IsSMulRegular k a) : IsSMulRegular (SkewMonoidAlgebra k G) a
  | ⟨_⟩, ⟨_⟩, h => by
    exact congr_arg _ <| ha.finsupp (ofCoeff.inj h)
/-
**SkewMonoidAlgebra.coeff_injective** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra
`。
形式化陈述：coeff_injective : Function.Injective (coeff : SkewMonoidAlgebra k G -> Fin
supp _ _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem coeff_injective :
    Function.Injective (coeff : SkewMonoidAlgebra k G → Finsupp _ _) :=
  fun ⟨_⟩ _ ↦ congr_arg _

@[deprecated (since := "2026-07-04")] alias toFinsupp_injective := coeff_injective

@[simp]
/-
**SkewMonoidAlgebra.coeff_inj** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：coeff_inj {a b : SkewMonoidAlgebra k G} : a.coeff = b.coeff ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `SkewMonoidAlgebra.coeff_injective`：coeff_injective : Function.Injective 
(coeff : SkewMonoidAlgebra k G -> Finsupp _ _)
-/
theorem coeff_inj {a b : SkewMonoidAlgebra k G} : a.coeff = b.coeff ↔ a = b :=
  coeff_injective.eq_iff

@[deprecated (since := "2026-07-04")] alias toFinsupp_inj := coeff_inj
/-
**SkewMonoidAlgebra.ofCoeff_injective** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgeb
ra`。
形式化陈述：ofCoeff_injective : Function.Injective (ofCoeff : Finsupp _ _ -> SkewMonoi
dAlgebra k G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem ofCoeff_injective :
    Function.Injective (ofCoeff : Finsupp _ _ → SkewMonoidAlgebra k G) :=
  fun _ _ ↦ congr_arg coeff

@[deprecated (since := "2026-07-04")] alias ofFinsupp_injective := ofCoeff_injective

/-- A variant of `SkewMonoidAlgebra.ofCoeff_injective` in terms of `Iff`. -/
/-
**SkewMonoidAlgebra.ofCoeff_inj** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：ofCoeff_inj {a b} : (⟨a⟩ : SkewMonoidAlgebra k G) = ⟨b⟩ ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `SkewMonoidAlgebra.ofCoeff_injective`：ofCoeff_injective : Function.Inject
ive (ofCoeff : Finsupp _ _ -> SkewMonoidAlgebra k G)

--- 原说明 ---
A variant of `SkewMonoidAlgebra.ofCoeff_injective` in terms of `Iff`.
-/
theorem ofCoeff_inj {a b} : (⟨a⟩ : SkewMonoidAlgebra k G) = ⟨b⟩ ↔ a = b :=
  ofCoeff_injective.eq_iff

@[deprecated (since := "2026-07-04")] alias ofFinsupp_inj := ofCoeff_inj

@[simp]
/-
**SkewMonoidAlgebra.coeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：coeff_eq_zero {a : SkewMonoidAlgebra k G} : a.coeff = 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.coeff_inj`：coeff_inj {a b : SkewMonoidAlgebra k G} : a
.coeff = b.coeff ↔ a = b
-/
theorem coeff_eq_zero {a : SkewMonoidAlgebra k G} : a.coeff = 0 ↔ a = 0 :=
  coeff_inj

@[deprecated (since := "2026-07-04")] alias toFinsupp_eq_zero := coeff_eq_zero

@[simp]
/-
**SkewMonoidAlgebra.ofCoeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra
`。
形式化陈述：ofCoeff_eq_zero {a} : (⟨a⟩ : SkewMonoidAlgebra k G) = 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.ofCoeff_inj`：ofCoeff_inj {a b} : (⟨a⟩ : SkewMonoidAlge
bra k G) = ⟨b⟩ ↔ a = b
-/
theorem ofCoeff_eq_zero {a} : (⟨a⟩ : SkewMonoidAlgebra k G) = 0 ↔ a = 0 :=
  ofCoeff_inj

@[deprecated (since := "2026-07-04")] alias ofFinsupp_eq_zero := ofCoeff_eq_zero
/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (SkewMonoidAlgebra k G) := ⟨0⟩
/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial k] [Nonempty G] :
    Nontrivial (SkewMonoidAlgebra k G) := Function.Injective.nontrivial ofCoeff_injective
/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton k] : Unique (SkewMonoidAlgebra k G) :=
  Function.Injective.unique coeff_injective
/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddMonoid (SkewMonoidAlgebra k G) where
  __ := coeff_injective.addMonoid _ coeff_zero coeff_add
    (fun _ _ ↦ coeff_smul _ _)

section Support

/-- For `f : SkewMonoidAlgebra k G`, `f.support` is the set of all `a ∈ G` such that
`f.coeff a ≠ 0`. -/
/-
**SkewMonoidAlgebra.support** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：support (p : SkewMonoidAlgebra k G) : Finset G
参数：p : SkewMonoidAlgebra k G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `f : SkewMonoidAlgebra k G`, `f.support` is the set of all `a ∈ G` such that
`f.coeff a ≠ 0`.
-/
def support (p : SkewMonoidAlgebra k G) : Finset G := p.coeff.support

@[simp]
/-
**SkewMonoidAlgebra.support_ofCoeff** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra
`。
形式化陈述：support_ofCoeff (p) : support (⟨p⟩ : SkewMonoidAlgebra k G) = p.support
参数：p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.support.eq_1`：∀ {k : Type u_1} {G : Type u_2} [inst : 
AddMonoid k] (p : SkewMonoidAlgebra k G), p.support = p.coeff.support
-/
theorem support_ofCoeff (p) : support (⟨p⟩ : SkewMonoidAlgebra k G) = p.support := by
  rw [support]

@[deprecated (since := "2026-07-04")] alias support_ofFinsupp := support_ofCoeff
/-
**SkewMonoidAlgebra.support_coeff** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：support_coeff (p : SkewMonoidAlgebra k G) : p.coeff.support = p.support
参数：p : SkewMonoidAlgebra k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.support.eq_1`：∀ {k : Type u_1} {G : Type u_2} [inst : 
AddMonoid k] (p : SkewMonoidAlgebra k G), p.support = p.coeff.support
-/
theorem support_coeff (p : SkewMonoidAlgebra k G) : p.coeff.support = p.support := by
  rw [support]

@[deprecated (since := "2026-07-04")] alias support_toFinsupp := support_coeff

@[simp]
/-
**SkewMonoidAlgebra.support_zero** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：support_zero : (0 : SkewMonoidAlgebra k G).support = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_zero : (0 : SkewMonoidAlgebra k G).support = ∅ := rfl

@[simp]
/-
**SkewMonoidAlgebra.support_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebr
a`。
形式化陈述：support_eq_empty {p} : p.support = ∅ ↔ (p : SkewMonoidAlgebra k G) = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_eq_empty {p} : p.support = ∅ ↔ (p : SkewMonoidAlgebra k G) = 0 := by
  rcases p
  simp only [support, Finsupp.support_eq_empty, ofCoeff_eq_zero]
/-
**SkewMonoidAlgebra.support_add** 是 Mathlib 中的一个引理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：support_add [DecidableEq G] {p q : SkewMonoidAlgebra k G} : (p + q).suppor
t subseteq p.support union q.support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.coeff_add`：coeff_add (a b : SkewMonoidAlgebra k G) : (
a + b).coeff = a.coeff + b.coeff
· 使用引理 `Finsupp.support_add`：support_add [DecidableEq ι] : (g₁ + g₂).support sub
seteq g₁.support union g₂.support
-/
lemma support_add [DecidableEq G] {p q : SkewMonoidAlgebra k G} :
    (p + q).support ⊆ p.support ∪ q.support := by
  simpa [support] using Finsupp.support_add

end Support

section Coeff

@[deprecated (since := "2026-07-06")] alias coeff_ofFinsupp := coeff_ofCoeff

@[deprecated "Now a syntactic tautology" (since := "2026-07-04"), nolint synTaut]
/-
**SkewMonoidAlgebra.toFinsupp_apply** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra
`。
形式化陈述：toFinsupp_apply (f : SkewMonoidAlgebra k G) (g) : f.coeff g = f.coeff g
参数：f : SkewMonoidAlgebra k G；g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinsupp_apply (f : SkewMonoidAlgebra k G) (g) : f.coeff g = f.coeff g := rfl

@[simp]
/-
**SkewMonoidAlgebra.mem_support_iff** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra
`。
形式化陈述：mem_support_iff {f : SkewMonoidAlgebra k G} {a : G} : a in f.support ↔ f.c
oeff a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.support_ofCoeff`：support_ofCoeff (p) : support (⟨p⟩ : 
SkewMonoidAlgebra k G) = p.support
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_support_iff {f : SkewMonoidAlgebra k G} {a : G} : a ∈ f.support ↔ f.coeff a ≠ 0 := by
  rcases f with ⟨⟩
  simp only [support_ofCoeff, Finsupp.mem_support_iff, ne_eq]
/-
**SkewMonoidAlgebra.notMem_support_iff** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlge
bra`。
形式化陈述：notMem_support_iff {f : SkewMonoidAlgebra k G} {a : G} : a ∉ f.support ↔ f
.coeff a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem notMem_support_iff {f : SkewMonoidAlgebra k G} {a : G} :
    a ∉ f.support ↔ f.coeff a = 0 := by
  simp only [mem_support_iff, ne_eq, not_not]
/-
**SkewMonoidAlgebra.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：ext_iff {p q : SkewMonoidAlgebra k G} : p = q ↔ forall n, coeff p n = coef
f q n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.ofCoeff.injEq`：∀ {k : Type u_1} {G : Type u_2} [inst :
 Zero k] (coeff coeff_1 : G →₀ k),   ({ coeff := coeff } = { coeff := coeff_1 })
 = (coeff = coeff_1)
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
-/
theorem ext_iff {p q : SkewMonoidAlgebra k G} : p = q ↔ ∀ n, coeff p n = coeff q n := by
  rcases p with ⟨f : G →₀ k⟩
  rcases q with ⟨g : G →₀ k⟩
  simpa [coeff] using DFunLike.ext_iff (f := f) (g := g)

@[ext]
/-
**SkewMonoidAlgebra.ext** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：ext {p q : SkewMonoidAlgebra k G} : (forall a, coeff p a = coeff q a) -> p
 = q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SkewMonoidAlgebra.ext_iff`：ext_iff {p q : SkewMonoidAlgebra k G} : p = q
 ↔ forall n, coeff p n = coeff q n
-/
theorem ext {p q : SkewMonoidAlgebra k G} : (∀ a, coeff p a = coeff q a) → p = q := ext_iff.2

end Coeff

section Single

/-- `single a b` is the finitely supported function with value `b` at `a` and zero otherwise. -/
/-
**SkewMonoidAlgebra.single** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：single (a : G) (b : k) : SkewMonoidAlgebra k G
参数：a : G；b : k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`single a b` is the finitely supported function with value `b` at `a` and zero o
therwise.
-/
def single (a : G) (b : k) : SkewMonoidAlgebra k G := ⟨Finsupp.single a b⟩

@[simp]
/-
**SkewMonoidAlgebra.coeff_single** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：coeff_single (a : G) (b : k) : (single a b).coeff = Finsupp.single a b
参数：a : G；b : k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_single (a : G) (b : k) : (single a b).coeff = Finsupp.single a b := rfl

@[deprecated (since := "2026-07-04")] alias toFinsupp_single := coeff_single

@[simp]
/-
**SkewMonoidAlgebra.ofCoeff_single** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`
。
形式化陈述：ofCoeff_single (a : G) (b : k) : ⟨Finsupp.single a b⟩ = single a b
参数：a : G；b : k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofCoeff_single (a : G) (b : k) : ⟨Finsupp.single a b⟩ = single a b := rfl

@[deprecated (since := "2026-07-06")] alias ofFinsupp_single := ofCoeff_single
/-
**SkewMonoidAlgebra.coeff_single_apply** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlge
bra`。
形式化陈述：coeff_single_apply {a a' : G} {b : k} [Decidable (a = a')] : coeff (single
 a b) a' = if a = a' then b else 0
参数：a = a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_single_apply {a a' : G} {b : k} [Decidable (a = a')] :
    coeff (single a b) a' = if a = a' then b else 0 := by
  simp [Finsupp.single_apply]
/-
**SkewMonoidAlgebra.single_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgeb
ra`。
形式化陈述：single_zero_right (a : G) : single a (0 : k) = 0
参数：a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_zero_right (a : G) : single a (0 : k) = 0 := by
  simp [← coeff_inj]

@[simp]
/-
**SkewMonoidAlgebra.single_add** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：single_add (a : G) (b₁ b₂ : k) : single a (b₁ + b₂) = single a b₁ + single
 a b₂
参数：a : G；b₁ b₂ : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.single_add`：single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) 
= single a b₁ + single a b₂
· 使用定理 `SkewMonoidAlgebra.coeff_add`：coeff_add (a b : SkewMonoidAlgebra k G) : (
a + b).coeff = a.coeff + b.coeff
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_add (a : G) (b₁ b₂ : k) : single a (b₁ + b₂) = single a b₁ + single a b₂ := by
  simp [← coeff_inj]

@[simp]
/-
**SkewMonoidAlgebra.single_zero** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：single_zero (a : G) : (single a 0 : SkewMonoidAlgebra k G) = 0
参数：a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_zero (a : G) : (single a 0 : SkewMonoidAlgebra k G) = 0 := by
  simp [← coeff_inj]
/-
**SkewMonoidAlgebra.single_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`
。
形式化陈述：single_eq_zero {a : G} {b : k} : single a b = 0 ↔ b = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem single_eq_zero {a : G} {b : k} : single a b = 0 ↔ b = 0 := by
  simp [← coeff_inj]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Group isomorphism between `SkewMonoidAlgebra k G` and `G →₀ k`. -/
@[simps apply symm_apply]
/-
**SkewMonoidAlgebra.coeffAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：coeffAddEquiv : SkewMonoidAlgebra k G ≃+ (G ->₀ k) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.coeff_add`：coeff_add (a b : SkewMonoidAlgebra k G) : (
a + b).coeff = a.coeff + b.coeff

--- 原说明 ---
Group isomorphism between `SkewMonoidAlgebra k G` and `G →₀ k`.
-/
def coeffAddEquiv : SkewMonoidAlgebra k G ≃+ (G →₀ k) where
  toFun    := coeff
  invFun   := ofCoeff
  map_add' := coeff_add

@[deprecated (since := "2026-07-04")] alias toFinsuppAddEquiv := coeffAddEquiv
@[deprecated (since := "2026-07-04")] alias toFinsuppAddEquiv_apply := coeffAddEquiv_apply
@[deprecated (since := "2026-07-04")]
alias toFinsuppAddEquiv_symm_apply := coeffAddEquiv_symm_apply
/-
**SkewMonoidAlgebra.smul_single** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：smul_single {S} [SMulZeroClass S k] (s : S) (a : G) (b : k) : s • single a
 b = single a (s • b)
参数：s : S；a : G；b : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.coeff_injective`：coeff_injective : Function.Injective 
(coeff : SkewMonoidAlgebra k G -> Finsupp _ _)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.coeff_smul`：coeff_smul {S : Type*} [SMulZeroClass S k]
 (a : S) (b : SkewMonoidAlgebra k G) : (a • b).coeff = a • b.coeff
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_single {S} [SMulZeroClass S k] (s : S) (a : G) (b : k) :
    s • single a b = single a (s • b) :=
  coeff_injective <| by simp;
/-
**SkewMonoidAlgebra.single_injective** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebr
a`。
形式化陈述：single_injective (a : G) : Function.Injective (single a : k -> SkewMonoidA
lgebra k G)
参数：a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用定理 `Finsupp.single_injective`：single_injective (a : α) : Function.Injective 
(single a : M -> α ->₀ M)
-/
theorem single_injective (a : G) : Function.Injective (single a : k → SkewMonoidAlgebra k G) :=
  coeffAddEquiv.symm.injective.comp (Finsupp.single_injective a)
/-
**SkewMonoidAlgebra.single_left_inj** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra
`。
形式化陈述：single_left_inj {a a' : G} {b : k} (h : b != 0) : single a b = single a' b
 ↔ a = a'
参数：h : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SkewMonoidAlgebra.coeff_inj`：coeff_inj {a b : SkewMonoidAlgebra k G} : a
.coeff = b.coeff ↔ a = b
· 使用定理 `Finsupp.single_left_inj`：single_left_inj (h : b != 0) : single a b = sin
gle a' b ↔ a = a'
-/
theorem single_left_inj {a a' : G} {b : k} (h : b ≠ 0) : single a b = single a' b ↔ a = a' := by
  rw [← coeff_inj]
  exact Finsupp.single_left_inj h
/-
**SkewMonoidAlgebra._root_.IsSMulRegular.skewMonoidAlgebra_iff** 是 Mathlib 中的一个定
理，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsSMulRegular.skewMonoidAlgebra_iff {S : Type*} [Monoid S] [DistribMulAction S k]
    {a : S} [Nonempty G] : IsSMulRegular k a ↔ IsSMulRegular (SkewMonoidAlgebra k G) a := by
  inhabit G
  refine ⟨IsSMulRegular.skewMonoidAlgebra, fun ha b₁ b₂ inj ↦ ?_⟩
  rw [← (single_injective _).eq_iff, ← smul_single, ← smul_single] at inj
  exact single_injective default (ha inj)

end Single

end AddMonoid

section AddMonoidWithOne

section One

variable [One G] [AddMonoidWithOne k]

/-- The unit of the multiplication is `single 1 1`, i.e. the function that is `1` at `1` and
  zero elsewhere. -/
/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit of the multiplication is `single 1 1`, i.e. the function that is `1` at
 `1` and
  zero elsewhere.
-/
instance : One (SkewMonoidAlgebra k G) where
  one := single 1 1
/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddMonoidWithOne (SkewMonoidAlgebra k G) where
/-
**SkewMonoidAlgebra.ofCoeff_one** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：ofCoeff_one : (⟨Finsupp.single 1 1⟩ : SkewMonoidAlgebra k G) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofCoeff_one : (⟨Finsupp.single 1 1⟩ : SkewMonoidAlgebra k G) = 1 := rfl

@[deprecated (since := "2026-07-04")] alias ofFinsupp_one := ofCoeff_one

@[simp]
/-
**SkewMonoidAlgebra.coeff_one** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：coeff_one : (1 : SkewMonoidAlgebra k G).coeff = Finsupp.single 1 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_one : (1 : SkewMonoidAlgebra k G).coeff = Finsupp.single 1 1 := rfl

@[deprecated (since := "2026-07-04")] alias toFinsupp_one := coeff_one

@[simp]
/-
**SkewMonoidAlgebra.coeff_eq_single_one_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `SkewM
onoidAlgebra`。
形式化陈述：coeff_eq_single_one_one_iff {a : SkewMonoidAlgebra k G} : a.coeff = Finsup
p.single 1 1 ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coeff_eq_single_one_one_iff {a : SkewMonoidAlgebra k G} :
    a.coeff = Finsupp.single 1 1 ↔ a = 1 := by
  simp [← coeff_inj]

@[deprecated (since := "2026-07-04")]
alias toFinsupp_eq_single_one_one_iff := coeff_eq_single_one_one_iff

@[simp]
/-
**SkewMonoidAlgebra.ofCoeff_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`
。
形式化陈述：ofCoeff_eq_one {a} : (⟨a⟩ : SkewMonoidAlgebra k G) = 1 ↔ a = Finsupp.singl
e 1 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ofCoeff_eq_one {a} :
    (⟨a⟩ : SkewMonoidAlgebra k G) = 1 ↔ a = Finsupp.single 1 1 := by
  simp [← coeff_inj]

@[deprecated (since := "2026-07-04")] alias ofFinsupp_eq_one := ofCoeff_eq_one

@[simp]
/-
**SkewMonoidAlgebra.single_one_one** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`
。
形式化陈述：single_one_one : single (1 : G) (1 : k) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem single_one_one : single (1 : G) (1 : k) = 1 := rfl
/-
**SkewMonoidAlgebra.one_def** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：one_def : (1 : SkewMonoidAlgebra k G) = single 1 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : SkewMonoidAlgebra k G) = single 1 1 := rfl

@[deprecated coeff_one (since := "2026-07-04")]
/-
**SkewMonoidAlgebra.coeff_one_one** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：coeff_one_one : coeff (1 : SkewMonoidAlgebra k G) 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_one_one : coeff (1 : SkewMonoidAlgebra k G) 1 = 1 := by simp
/-
**SkewMonoidAlgebra.natCast_def** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：natCast_def (n : Nat) : (n : SkewMonoidAlgebra k G) = single (1 : G) (n : 
k)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `SkewMonoidAlgebra.single_zero`：single_zero (a : G) : (single a 0 : SkewM
onoidAlgebra k G) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `SkewMonoidAlgebra.single_add`：single_add (a : G) (b₁ b₂ : k) : single a 
(b₁ + b₂) = single a b₁ + single a b₂
-/
theorem natCast_def (n : ℕ) : (n : SkewMonoidAlgebra k G) = single (1 : G) (n : k) := by
  induction n <;> simp_all

@[simp]
/-
**SkewMonoidAlgebra.single_nat** 是 Mathlib 中的一个引理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：single_nat (n : Nat) : (single 1 n : SkewMonoidAlgebra k G) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SkewMonoidAlgebra.natCast_def`：natCast_def (n : Nat) : (n : SkewMonoidAl
gebra k G) = single (1 : G) (n : k)
-/
lemma single_nat (n : ℕ) : (single 1 n : SkewMonoidAlgebra k G) = n := (natCast_def _).symm

end One

end AddMonoidWithOne

section AddCommMonoid

variable [AddCommMonoid k]

/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommMonoid (SkewMonoidAlgebra k G) where
  __ := coeff_injective.addCommMonoid _ coeff_zero coeff_add
    (fun _ _ ↦ coeff_smul _ _)

section sum

/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq G] [DecidableEq k] : DecidableEq (SkewMonoidAlgebra k G) :=
  Equiv.decidableEq coeffAddEquiv.toEquiv

/-- `sum f g` is the sum of `g a (f.coeff a)` over the support of `f`. -/
/-
**SkewMonoidAlgebra.sum** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：sum {N : Type*} [AddCommMonoid N] (f : SkewMonoidAlgebra k G) (g : G -> k 
-> N) : N
参数：f : SkewMonoidAlgebra k G；g : G -> k -> N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sum f g` is the sum of `g a (f.coeff a)` over the support of `f`.
-/
def sum {N : Type*} [AddCommMonoid N] (f : SkewMonoidAlgebra k G) (g : G → k → N) : N :=
  f.coeff.sum g
/-
**SkewMonoidAlgebra.sum_def** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：sum_def {N : Type*} [AddCommMonoid N] (f : SkewMonoidAlgebra k G) (g : G -
> k -> N) : sum f g = f.coeff.sum g
参数：f : SkewMonoidAlgebra k G；g : G -> k -> N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sum_def {N : Type*} [AddCommMonoid N] (f : SkewMonoidAlgebra k G) (g : G → k → N) :
    sum f g = f.coeff.sum g := rfl

/-- Unfolded version of `sum_def` in terms of `Finset.sum`. -/
/-
**SkewMonoidAlgebra.sum_def'** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：sum_def' {N : Type*} [AddCommMonoid N] (f : SkewMonoidAlgebra k G) (g : G 
-> k -> N) : sum f g = ∑ a in f.support, g a (f.coeff a)
参数：f : SkewMonoidAlgebra k G；g : G -> k -> N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Unfolded version of `sum_def` in terms of `Finset.sum`.
-/
theorem sum_def' {N : Type*} [AddCommMonoid N] (f : SkewMonoidAlgebra k G) (g : G → k → N) :
    sum f g = ∑ a ∈ f.support, g a (f.coeff a) := rfl

@[simp]
/-
**SkewMonoidAlgebra.sum_single_index** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebr
a`。
形式化陈述：sum_single_index {N} [AddCommMonoid N] {a : G} {b : k} {h : G -> k -> N} (
h_zero : h a 0 = 0) : (SkewMonoidAlgebra.single a b).sum h = h a b
参数：h_zero : h a 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
-/
theorem sum_single_index {N} [AddCommMonoid N] {a : G} {b : k} {h : G → k → N}
    (h_zero : h a 0 = 0) : (SkewMonoidAlgebra.single a b).sum h = h a b :=
  Finsupp.sum_single_index h_zero
/-
**SkewMonoidAlgebra.map_sum** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：map_sum {N P : Type*} [AddCommMonoid N] [AddCommMonoid P] {H : Type*} [Fun
Like H N P] [AddMonoidHomClass H N P] (h : H) (f : SkewMonoidAlgebra k G) (g : G
 -> k -> N) : h (sum f g) = sum f fun a b => h (g a b)
参数：h : H；f : SkewMonoidAlgebra k G；g : G -> k -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
-/
theorem map_sum {N P : Type*} [AddCommMonoid N] [AddCommMonoid P] {H : Type*} [FunLike H N P]
    [AddMonoidHomClass H N P] (h : H) (f : SkewMonoidAlgebra k G) (g : G → k → N) :
    h (sum f g) = sum f fun a b ↦ h (g a b) :=
  _root_.map_sum h _ _

/-- Variant where the image of `g` is a `SkewMonoidAlgebra`. -/
/-
**SkewMonoidAlgebra.coeff_sum'** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：coeff_sum' {k' G' : Type*} [AddCommMonoid k'] (f : SkewMonoidAlgebra k G) 
(g : G -> k -> SkewMonoidAlgebra k' G') : (sum f g).coeff = Finsupp.sum f.coeff 
(coeff <| g · ·)
参数：f : SkewMonoidAlgebra k G；g : G -> k -> SkewMonoidAlgebra k' G'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N

--- 原说明 ---
Variant where the image of `g` is a `SkewMonoidAlgebra`.
-/
theorem coeff_sum' {k' G' : Type*} [AddCommMonoid k'] (f : SkewMonoidAlgebra k G)
    (g : G → k → SkewMonoidAlgebra k' G') :
    (sum f g).coeff = Finsupp.sum f.coeff (coeff <| g · ·) :=
  _root_.map_sum coeffAddEquiv (fun a ↦ g a (f.coeff a)) f.coeff.support

@[deprecated (since := "2026-07-04")] alias toFinsupp_sum' := coeff_sum'
/-
**SkewMonoidAlgebra.ofCoeff_sum** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：ofCoeff_sum {k' G' : Type*} [AddCommMonoid k'] (f : G ->₀ k) (g : G -> k -
> G' ->₀ k') : (⟨Finsupp.sum f g⟩ : SkewMonoidAlgebra k' G') = sum ⟨f⟩ (⟨g · ·⟩)
参数：f : G ->₀ k；g : G -> k -> G' ->₀ k'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.coeff_injective`：coeff_injective : Function.Injective 
(coeff : SkewMonoidAlgebra k G -> Finsupp _ _)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.coeff_sum'`：coeff_sum' {k' G' : Type*} [AddCommMonoid 
k'] (f : SkewMonoidAlgebra k G) (g : G -> k -> SkewMonoidAlgebra k' G') : (sum f
 g).coeff = Finsup…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofCoeff_sum {k' G' : Type*} [AddCommMonoid k'] (f : G →₀ k)
    (g : G → k → G' →₀ k') :
    (⟨Finsupp.sum f g⟩ : SkewMonoidAlgebra k' G') = sum ⟨f⟩ (⟨g · ·⟩) := by
  apply coeff_injective; simp only [coeff_sum']

@[deprecated (since := "2026-07-04")] alias ofFinsupp_sum := ofCoeff_sum
/-
**SkewMonoidAlgebra.sum_single** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：sum_single (f : SkewMonoidAlgebra k G) : f.sum single = f
参数：f : SkewMonoidAlgebra k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.coeff_injective`：coeff_injective : Function.Injective 
(coeff : SkewMonoidAlgebra k G -> Finsupp _ _)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.coeff_sum'`：coeff_sum' {k' G' : Type*} [AddCommMonoid 
k'] (f : SkewMonoidAlgebra k G) (g : G -> k -> SkewMonoidAlgebra k' G') : (sum f
 g).coeff = Finsup…
· 使用定理 `Finsupp.sum_single`：sum_single [AddCommMonoid M] (f : α ->₀ M) : f.sum s
ingle = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_single (f : SkewMonoidAlgebra k G) : f.sum single = f := by
  apply coeff_injective; simp only [coeff_sum', coeff_single, Finsupp.sum_single]

/-- Taking the `sum` under `h` is an additive homomorphism, if `h` is an additive homomorphism.
This is a more specific version of `SkewMonoidAlgebra.sum_add_index` with simpler hypotheses. -/
/-
**SkewMonoidAlgebra.sum_add_index'** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`
。
形式化陈述：sum_add_index' {S : Type*} [AddCommMonoid S] {f g : SkewMonoidAlgebra k G}
 {h : G -> k -> S} (hf : forall i, h i 0 = 0) (h_add : forall a b₁ b₂, h a (b₁ +
 b₂) = h a b₁ + h a b₂) : (f + g).sum h = f.sum h + g.sum h
参数：hf : forall i, h i 0 = 0；h_add : forall a b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a
 b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.ofCoeff_add`：ofCoeff_add {a b} : (⟨a + b⟩ : SkewMonoid
Algebra k G) = ⟨a⟩ + ⟨b⟩
· 使用定理 `SkewMonoidAlgebra.eta`：∀ {k : Type u_1} {G : Type u_2} [inst : AddMonoid
 k] (f : SkewMonoidAlgebra k G), { coeff := f.coeff } = f
· 使用定理 `Finsupp.sum_add_index'`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} 
[inst : AddZeroClass M] [inst_1 : AddCommMonoid N] {f g : α →₀ M}   {h : α → M →
 N},   (∀ (a…

--- 原说明 ---
Taking the `sum` under `h` is an additive homomorphism, if `h` is an additive ho
momorphism.
This is a more specific version of `SkewMonoidAlgebra.sum_add_index` with simple
r hypotheses.
-/
theorem sum_add_index' {S : Type*} [AddCommMonoid S] {f g : SkewMonoidAlgebra k G} {h : G → k → S}
    (hf : ∀ i, h i 0 = 0) (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂) :
    (f + g).sum h = f.sum h + g.sum h := by
  rw [show f + g = ⟨f.coeff + g.coeff⟩ by rw [ofCoeff_add, eta]]
  exact Finsupp.sum_add_index' hf h_add

/-- Taking the `sum` under `h` is an additive homomorphism, if `h` is an additive homomorphism.
This is a more general version of `SkewMonoidAlgebra.sum_add_index'`;
the latter has simpler hypotheses. -/
/-
**SkewMonoidAlgebra.sum_add_index** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：sum_add_index {S : Type*} [DecidableEq G] [AddCommMonoid S] {f g : SkewMon
oidAlgebra k G} {h : G -> k -> S} (h_zero : forall a in f.support union g.suppor
t, h a 0 = 0) (h_add : forall a in f.support union g.support, forall b₁ b₂, h a 
(b₁ + b₂) = h a b₁ + h a b₂) : (f + g).sum h = f.sum h + g.sum h
参数：h_zero : forall a in f.support union g.support, h a 0 = 0；h_add : forall a in
 f.support union g.support, forall b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.ofCoeff_add`：ofCoeff_add {a b} : (⟨a + b⟩ : SkewMonoid
Algebra k G) = ⟨a⟩ + ⟨b⟩
· 使用定理 `SkewMonoidAlgebra.eta`：∀ {k : Type u_1} {G : Type u_2} [inst : AddMonoid
 k] (f : SkewMonoidAlgebra k G), { coeff := f.coeff } = f
· 使用定理 `Finsupp.sum_add_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : DecidableEq α] [inst_1 : AddZeroClass M]   [inst_2 : AddCommMonoid N] {f 
g : α →₀ M}…

--- 原说明 ---
Taking the `sum` under `h` is an additive homomorphism, if `h` is an additive ho
momorphism.
This is a more general version of `SkewMonoidAlgebra.sum_add_index'`;
the latter has simpler hypotheses.
-/
theorem sum_add_index {S : Type*} [DecidableEq G] [AddCommMonoid S]
    {f g : SkewMonoidAlgebra k G} {h : G → k → S} (h_zero : ∀ a ∈ f.support ∪ g.support, h a 0 = 0)
    (h_add : ∀ a ∈ f.support ∪ g.support, ∀ b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂) :
    (f + g).sum h = f.sum h + g.sum h := by
  rw [show f + g = ⟨f.coeff + g.coeff⟩ by rw [ofCoeff_add, eta]]
  exact Finsupp.sum_add_index h_zero h_add

@[simp]
/-
**SkewMonoidAlgebra.sum_add** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：sum_add {S : Type*} [AddCommMonoid S] (p : SkewMonoidAlgebra k G) (f g : G
 -> k -> S) : (p.sum fun n x => f n x + g n x) = p.sum f + p.sum g
参数：p : SkewMonoidAlgebra k G；f g : G -> k -> S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_add`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst :
 Zero M] [inst_1 : AddCommMonoid N] {f : α →₀ M}   {h₁ h₂ : α → M → N}, (f.sum f
un a …
-/
theorem sum_add {S : Type*} [AddCommMonoid S] (p : SkewMonoidAlgebra k G) (f g : G → k → S) :
    (p.sum fun n x ↦ f n x + g n x) = p.sum f + p.sum g := Finsupp.sum_add

@[simp]
/-
**SkewMonoidAlgebra.sum_zero_index** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`
。
形式化陈述：sum_zero_index {S : Type*} [AddCommMonoid S] {f : G -> k -> S} : (0 : Skew
MonoidAlgebra k G).sum f = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_zero_index {S : Type*} [AddCommMonoid S] {f : G → k → S} :
    (0 : SkewMonoidAlgebra k G).sum f = 0 := by simp [sum]

@[simp]
/-
**SkewMonoidAlgebra.sum_zero** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：sum_zero {N : Type*} [AddCommMonoid N] {f : SkewMonoidAlgebra k G} : (f.su
m fun _ _ => (0 : N)) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
-/
theorem sum_zero {N : Type*} [AddCommMonoid N] {f : SkewMonoidAlgebra k G} :
    (f.sum fun _ _ ↦ (0 : N)) = 0 := Finset.sum_const_zero
/-
**SkewMonoidAlgebra.sum_sum_index** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：sum_sum_index {α β M N P : Type*} [AddCommMonoid M] [AddCommMonoid N] [Add
CommMonoid P] {f : SkewMonoidAlgebra M α} {g : α -> M -> SkewMonoidAlgebra N β} 
{h : β -> N -> P} (h_zero : forall (a : β), h a 0 = 0) (h_add : forall (a : β) (
b₁ b₂ : N), h a (b₁ + b₂) = h a b₁ + h a b₂) : sum (sum f g) h = sum f fun a b =
> sum (g a b) h
参数：h_zero : forall (a : β), h a 0 = 0；h_add : forall (a : β) (b₁ b₂ : N), h a (b
₁ + b₂) = h a b₁ + h a b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.sum_def`：sum_def {N : Type*} [AddCommMonoid N] (f : Sk
ewMonoidAlgebra k G) (g : G -> k -> N) : sum f g = f.coeff.sum g
· 使用定理 `SkewMonoidAlgebra.coeff_sum'`：coeff_sum' {k' G' : Type*} [AddCommMonoid 
k'] (f : SkewMonoidAlgebra k G) (g : G -> k -> SkewMonoidAlgebra k' G') : (sum f
 g).coeff = Finsup…
· 使用定理 `Finsupp.sum_sum_index`：∀ {α : Type u_1} {β : Type u_7} {M : Type u_8} {N
 : Type u_10} {P : Type u_11} [inst : Zero M]   [inst_1 : AddCommMonoid N] [inst
_2 : AddCom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_sum_index {α β M N P : Type*} [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    {f : SkewMonoidAlgebra M α} {g : α → M → SkewMonoidAlgebra N β} {h : β → N → P}
    (h_zero : ∀ (a : β), h a 0 = 0)
    (h_add : ∀ (a : β) (b₁ b₂ : N), h a (b₁ + b₂) = h a b₁ + h a b₂) :
    sum (sum f g) h = sum f fun a b ↦ sum (g a b) h := by
  rw [sum_def, coeff_sum' f g, Finsupp.sum_sum_index h_zero h_add]; simp [sum_def]

@[simp]
/-
**SkewMonoidAlgebra.coeff_sum** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：coeff_sum {k' G' : Type*} [AddCommMonoid k'] {f : SkewMonoidAlgebra k G} {
g : G -> k -> SkewMonoidAlgebra k' G'} {a₂ : G'} : (f.sum g).coeff a₂ = f.sum fu
n a₁ b => (g a₁ b).coeff a₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.coeff_sum'`：coeff_sum' {k' G' : Type*} [AddCommMonoid 
k'] (f : SkewMonoidAlgebra k G) (g : G -> k -> SkewMonoidAlgebra k' G') : (sum f
 g).coeff = Finsup…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.sum_apply`：sum_apply [Zero M] [AddCommMonoid N] {f : α ->₀ M} {g
 : α -> M -> β ->₀ N} {a₂ : β} : (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_sum {k' G' : Type*} [AddCommMonoid k'] {f : SkewMonoidAlgebra k G}
    {g : G → k → SkewMonoidAlgebra k' G'} {a₂ : G'} :
    (f.sum g).coeff a₂ = f.sum fun a₁ b ↦ (g a₁ b).coeff a₂ := by
  simp_rw [coeff_sum', sum_def, Finsupp.sum_apply]
/-
**SkewMonoidAlgebra.sum_mul** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：sum_mul {S : Type*} [NonUnitalNonAssocSemiring S] (b : S) (s : SkewMonoidA
lgebra k G) {f : G -> k -> S} : s.sum f * b = s.sum fun a c => f a c * b
参数：b : S；s : SkewMonoidAlgebra k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_mul {S : Type*} [NonUnitalNonAssocSemiring S] (b : S) (s : SkewMonoidAlgebra k G)
    {f : G → k → S} : s.sum f * b = s.sum fun a c ↦ f a c * b := by
  simp only [sum, Finsupp.sum, Finset.sum_mul]
/-
**SkewMonoidAlgebra.mul_sum** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：mul_sum {S : Type*} [NonUnitalNonAssocSemiring S] (b : S) (s : SkewMonoidA
lgebra k G) {f : G -> k -> S} : b * s.sum f = s.sum fun a c => b * f a c
参数：b : S；s : SkewMonoidAlgebra k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_sum {S : Type*} [NonUnitalNonAssocSemiring S] (b : S) (s : SkewMonoidAlgebra k G)
    {f : G → k → S} : b * s.sum f = s.sum fun a c ↦ b * f a c := by
  simp only [sum, Finsupp.sum, Finset.mul_sum]

set_option backward.isDefEq.respectTransparency false in
/-- Analogue of `Finsupp.sum_ite_eq'` for `SkewMonoidAlgebra`. -/
@[simp]
/-
**SkewMonoidAlgebra.sum_ite_eq'** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：sum_ite_eq' {N : Type*} [AddCommMonoid N] [DecidableEq G] (f : SkewMonoidA
lgebra k G) (a : G) (b : G -> k -> N) : (f.sum fun (x : G) (v : k) => if x = a t
hen b x v else 0) = if a in f.support then b a (f.coeff a) else 0
参数：f : SkewMonoidAlgebra k G；a : G；b : G -> k -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Analogue of `Finsupp.sum_ite_eq'` for `SkewMonoidAlgebra`.
-/
theorem sum_ite_eq' {N : Type*} [AddCommMonoid N] [DecidableEq G] (f : SkewMonoidAlgebra k G)
    (a : G) (b : G → k → N) : (f.sum fun (x : G) (v : k) ↦ if x = a then b x v else 0) =
      if a ∈ f.support then b a (f.coeff a) else 0 := by
  simp only [sum_def', f.coeff.support.sum_ite_eq', support]
/-
**SkewMonoidAlgebra.smul_sum** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：smul_sum {M : Type*} {R : Type*} [AddCommMonoid M] [DistribSMul R M] {v : 
SkewMonoidAlgebra k G} {c : R} {h : G -> k -> M} : c • v.sum h = v.sum fun a b =
> c • h a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.smul_sum`：smul_sum [Zero β] [AddCommMonoid M] [DistribSMul R M] 
{v : α ->₀ β} {c : R} {h : α -> β -> M} : c • v.sum h = v.sum fun a b => c • h a
 b
-/
theorem smul_sum {M : Type*} {R : Type*} [AddCommMonoid M] [DistribSMul R M]
    {v : SkewMonoidAlgebra k G} {c : R} {h : G → k → M} :
    c • v.sum h = v.sum fun a b ↦ c • h a b := Finsupp.smul_sum
/-
**SkewMonoidAlgebra.sum_congr** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：sum_congr {f : SkewMonoidAlgebra k G} {M : Type*} [AddCommMonoid M] {g₁ g₂
 : G -> k -> M} (h : forall x in f.support, g₁ x (f.coeff x) = g₂ x (f.coeff x))
 : f.sum g₁ = f.sum g₂
参数：h : forall x in f.support, g₁ x (f.coeff x) = g₂ x (f.coeff x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
-/
theorem sum_congr {f : SkewMonoidAlgebra k G} {M : Type*} [AddCommMonoid M] {g₁ g₂ : G → k → M}
    (h : ∀ x ∈ f.support, g₁ x (f.coeff x) = g₂ x (f.coeff x)) :
    f.sum g₁ = f.sum g₂ := Finset.sum_congr rfl h

@[elab_as_elim]
/-
**SkewMonoidAlgebra.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：induction_on {p : SkewMonoidAlgebra k G -> Prop} (f : SkewMonoidAlgebra k 
G) (zero : p 0) (single : forall g a, p (single g a)) (add : forall f g : SkewMo
noidAlgebra k G, p f -> p g -> p (f + g)) : p f
参数：f : SkewMonoidAlgebra k G；zero : p 0；single : forall g a, p (single g a)；add 
: forall f g : SkewMonoidAlgebra k G, p f -> p g -> p (f + g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SkewMonoidAlgebra.sum_single`：sum_single (f : SkewMonoidAlgebra k G) : f
.sum single = f
· 使用定理 `SkewMonoidAlgebra.sum_def'`：sum_def' {N : Type*} [AddCommMonoid N] (f : 
SkewMonoidAlgebra k G) (g : G -> k -> N) : sum f g = ∑ a in f.support, g a (f.co
eff a)
· 使用定理 `Finset.sum_induction`：∀ {ι : Type u_1} {s : Finset ι} {M : Type u_7} [in
st : AddCommMonoid M] (f : ι → M) (p : M → Prop),   (∀ (a b : M), p a → p b → p 
(a + b)) →…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem induction_on {p : SkewMonoidAlgebra k G → Prop} (f : SkewMonoidAlgebra k G)
    (zero : p 0) (single : ∀ g a, p (single g a)) (add : ∀ f g :
    SkewMonoidAlgebra k G, p f → p g → p (f + g)) : p f := by
  rw [← sum_single f, sum_def']
  exact Finset.sum_induction _ _ add zero (by simp_all)

/-- Slightly less general but more convenient version of `SkewMonoidAlgebra.induction_on`. -/
@[induction_eliminator]
/-
**SkewMonoidAlgebra.induction_on'** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：induction_on' [instNonempty : Nonempty G] {p : SkewMonoidAlgebra k G -> Pr
op} (f : SkewMonoidAlgebra k G) (single : forall g a, p (single g a)) (add : for
all f g : SkewMonoidAlgebra k G, p f -> p g -> p (f + g)) : p f
参数：f : SkewMonoidAlgebra k G；single : forall g a, p (single g a)；add : forall f 
g : SkewMonoidAlgebra k G, p f -> p g -> p (f + g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.induction_on`：induction_on {p : SkewMonoidAlgebra k G 
-> Prop} (f : SkewMonoidAlgebra k G) (zero : p 0) (single : forall g a, p (singl
e g a)) (add : foral…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.single_zero`：single_zero (a : G) : (single a 0 : SkewM
onoidAlgebra k G) = 0

--- 原说明 ---
Slightly less general but more convenient version of `SkewMonoidAlgebra.inductio
n_on`.
-/
theorem induction_on' [instNonempty : Nonempty G] {p : SkewMonoidAlgebra k G → Prop}
    (f : SkewMonoidAlgebra k G) (single : ∀ g a, p (single g a)) (add : ∀ f g :
    SkewMonoidAlgebra k G, p f → p g → p (f + g)) : p f :=
  induction_on f (by simpa using single (Classical.choice instNonempty) 0) single add

/-- If two additive homomorphisms from `SkewMonoidAlgebra k G ` are equal on each `single a b`,
then they are equal. -/
@[ext high]
/-
**SkewMonoidAlgebra.addHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：addHom_ext {M : Type*} [AddZeroClass M] {f g : SkewMonoidAlgebra k G ->+ M
} (h : forall a b, f (single a b) = g (single a b)) : f = g
参数：h : forall a b, f (single a b) = g (single a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `SkewMonoidAlgebra.induction_on`：induction_on {p : SkewMonoidAlgebra k G 
-> Prop} (f : SkewMonoidAlgebra k G) (zero : p 0) (single : forall g a, p (singl
e g a)) (add : foral…
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
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […

--- 原说明 ---
If two additive homomorphisms from `SkewMonoidAlgebra k G ` are equal on each `s
ingle a b`,
then they are equal.
-/
theorem addHom_ext {M : Type*} [AddZeroClass M] {f g : SkewMonoidAlgebra k G →+ M}
    (h : ∀ a b, f (single a b) = g (single a b)) : f = g := by
  ext p; induction p using SkewMonoidAlgebra.induction_on <;> simp_all

end sum

section mapDomain

variable {G' G'' : Type*} (f : G → G') {g : G' → G''} (v : SkewMonoidAlgebra k G)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Given `f : G → G'` and `v : SkewMonoidAlgebra k G`, `mapDomain f v : SkewMonoidAlgebra k G'`
is the finitely supported additive homomorphism whose value at `a : G'` is the sum of `v x` over
all `x` such that `f x = a`.
Note that `SkewMonoidAlgebra.mapDomain` is defined as an `AddHom`, while `MonoidAlgebra.mapDomain`
is defined as a function. -/
@[simps]
/-
**SkewMonoidAlgebra.mapDomain** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：mapDomain : SkewMonoidAlgebra k G ->+ SkewMonoidAlgebra k G' where toFun v
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : G → G'` and `v : SkewMonoidAlgebra k G`, `mapDomain f v : SkewMonoidA
lgebra k G'`
is the finitely supported additive homomorphism whose value at `a : G'` is the s
um of `v x` over
all `x` such that `f x = a`.
Note that `SkewMonoidAlgebra.mapDomain` is defined as an `AddHom`, while `Monoid
Algebra.mapDomain`
is defined as a function.
-/
def mapDomain :
    SkewMonoidAlgebra k G →+ SkewMonoidAlgebra k G' where
  toFun v      := v.sum fun a ↦ single (f a)
  map_zero'    := sum_zero_index
  map_add' _ _ := sum_add_index' (fun _ ↦ single_zero _) fun _ ↦ single_add _
/-
**SkewMonoidAlgebra.coeff_mapDomain** 是 Mathlib 中的一个引理，位于命名空间 `SkewMonoidAlgebra
`。
形式化陈述：coeff_mapDomain : (mapDomain f v).coeff = Finsupp.mapDomain f v.coeff
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.mapDomain_apply`：∀ {k : Type u_1} {G : Type u_2} [inst
 : AddCommMonoid k] {G' : Type u_3} (f : G → G') (v : SkewMonoidAlgebra k G),   
(SkewMonoidAlgebra.mapD…
· 使用定理 `SkewMonoidAlgebra.coeff_sum'`：coeff_sum' {k' G' : Type*} [AddCommMonoid 
k'] (f : SkewMonoidAlgebra k G) (g : G -> k -> SkewMonoidAlgebra k' G') : (sum f
 g).coeff = Finsup…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_mapDomain :
    (mapDomain f v).coeff = Finsupp.mapDomain f v.coeff := by
  simp_rw [mapDomain_apply, Finsupp.mapDomain, coeff_sum', single]

@[deprecated (since := "2026-07-04")] alias toFinsupp_mapDomain := coeff_mapDomain

variable {f v}
/-
**SkewMonoidAlgebra.mapDomain_id** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：mapDomain_id : mapDomain id v = v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.sum_single`：sum_single (f : SkewMonoidAlgebra k G) : f
.sum single = f
-/
theorem mapDomain_id : mapDomain id v = v := sum_single _
/-
**SkewMonoidAlgebra.mapDomain_comp** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`
。
形式化陈述：mapDomain_comp : mapDomain (g ∘ f) v = mapDomain g (mapDomain f v)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SkewMonoidAlgebra.sum_sum_index`：sum_sum_index {α β M N P : Type*} [AddC
ommMonoid M] [AddCommMonoid N] [AddCommMonoid P] {f : SkewMonoidAlgebra M α} {g 
: α -> M -> SkewMonoi…
· 使用定理 `SkewMonoidAlgebra.single_zero`：single_zero (a : G) : (single a 0 : SkewM
onoidAlgebra k G) = 0
· 使用定理 `SkewMonoidAlgebra.single_add`：single_add (a : G) (b₁ b₂ : k) : single a 
(b₁ + b₂) = single a b₁ + single a b₂
· 使用定理 `SkewMonoidAlgebra.sum_congr`：sum_congr {f : SkewMonoidAlgebra k G} {M : 
Type*} [AddCommMonoid M] {g₁ g₂ : G -> k -> M} (h : forall x in f.support, g₁ x 
(f.coeff x) = g₂ …
· 使用定理 `SkewMonoidAlgebra.sum_single_index`：sum_single_index {N} [AddCommMonoid 
N] {a : G} {b : k} {h : G -> k -> N} (h_zero : h a 0 = 0) : (SkewMonoidAlgebra.s
ingle a b).sum h = h a b
-/
theorem mapDomain_comp : mapDomain (g ∘ f) v = mapDomain g (mapDomain f v) :=
  ((sum_sum_index (single_zero <| g ·) (single_add <| g ·)).trans
    (sum_congr fun _ _ ↦ sum_single_index (single_zero _))).symm
/-
**SkewMonoidAlgebra.sum_mapDomain_index** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlg
ebra`。
形式化陈述：sum_mapDomain_index {k' : Type*} [AddCommMonoid k'] {h : G' -> k -> k'} (h
_zero : forall (b : G'), h b 0 = 0) (h_add : forall (b : G') (m₁ m₂ : k), h b (m
₁ + m₂) = h b m₁ + h b m₂) : sum (mapDomain f v) h = sum v fun a m => h (f a) m
参数：h_zero : forall (b : G'), h b 0 = 0；h_add : forall (b : G') (m₁ m₂ : k), h b 
(m₁ + m₂) = h b m₁ + h b m₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SkewMonoidAlgebra.sum_sum_index`：sum_sum_index {α β M N P : Type*} [AddC
ommMonoid M] [AddCommMonoid N] [AddCommMonoid P] {f : SkewMonoidAlgebra M α} {g 
: α -> M -> SkewMonoi…
· 使用定理 `SkewMonoidAlgebra.sum_congr`：sum_congr {f : SkewMonoidAlgebra k G} {M : 
Type*} [AddCommMonoid M] {g₁ g₂ : G -> k -> M} (h : forall x in f.support, g₁ x 
(f.coeff x) = g₂ …
· 使用定理 `SkewMonoidAlgebra.sum_single_index`：sum_single_index {N} [AddCommMonoid 
N] {a : G} {b : k} {h : G -> k -> N} (h_zero : h a 0 = 0) : (SkewMonoidAlgebra.s
ingle a b).sum h = h a b
-/
theorem sum_mapDomain_index {k' : Type*} [AddCommMonoid k'] {h : G' → k → k'}
    (h_zero : ∀ (b : G'), h b 0 = 0)
    (h_add : ∀ (b : G') (m₁ m₂ : k), h b (m₁ + m₂) = h b m₁ + h b m₂) :
    sum (mapDomain f v) h = sum v fun a m ↦ h (f a) m :=
  (sum_sum_index h_zero h_add).trans <| sum_congr fun _ _ ↦ sum_single_index (h_zero _)
/-
**SkewMonoidAlgebra.mapDomain_single** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebr
a`。
形式化陈述：mapDomain_single {a : G} {b : k} : mapDomain f (single a b) = single (f a)
 b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.sum_single_index`：sum_single_index {N} [AddCommMonoid 
N] {a : G} {b : k} {h : G -> k -> N} (h_zero : h a 0 = 0) : (SkewMonoidAlgebra.s
ingle a b).sum h = h a b
· 使用定理 `SkewMonoidAlgebra.single_zero`：single_zero (a : G) : (single a 0 : SkewM
onoidAlgebra k G) = 0
-/
theorem mapDomain_single {a : G} {b : k} : mapDomain f (single a b) = single (f a) b :=
  sum_single_index <| single_zero _
/-
**SkewMonoidAlgebra.mapDomain_smul** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`
。
形式化陈述：mapDomain_smul {R : Type*} [Monoid R] [DistribMulAction R k] {b : R} : map
Domain f (b • v) = b • mapDomain f v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.coeff_smul`：coeff_smul {S : Type*} [SMulZeroClass S k]
 (a : S) (b : SkewMonoidAlgebra k G) : (a • b).coeff = a • b.coeff
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `SkewMonoidAlgebra.coeff_mapDomain`：coeff_mapDomain : (mapDomain f v).coe
ff = Finsupp.mapDomain f v.coeff
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.mapDomain_smul`：mapDomain_smul [AddCommMonoid M] [DistribSMul R 
M] {f : α -> β} (b : R) (v : α ->₀ M) : mapDomain f (b • v) = b • mapDomain f v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapDomain_smul {R : Type*} [Monoid R] [DistribMulAction R k] {b : R} :
    mapDomain f (b • v) = b • mapDomain f v := by
  simp_rw [← coeff_inj, coeff_smul, coeff_mapDomain]
  simp [Finsupp.mapDomain_smul]

/-- A non-commutative version of `SkewMonoidAlgebra.lift`: given an additive homomorphism
`f : k →+ R` and a homomorphism `g : G → R`, returns the additive homomorphism from
`SkewMonoidAlgebra k G` such that `liftNC f g (single a b) = f b * g a`.

If `k` is a semiring and `f` is a ring homomorphism and for all `x : R`, `y : G` the equality
`(f (y • x)) * g y = (g y) * (f x))` holds, then the result is a ring homomorphism (see
`SkewMonoidAlgebra.liftNCRingHom`).

If `R` is a `k`-algebra and `f = algebraMap k R`, then the result is an algebra homomorphism called
`SkewMonoidAlgebra.lift`. -/
/-
**SkewMonoidAlgebra.liftNC** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：liftNC {R : Type*} [NonUnitalNonAssocSemiring R] (f : k ->+ R) (g : G -> R
) : SkewMonoidAlgebra k G ->+ R
参数：f : k ->+ R；g : G -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-commutative version of `SkewMonoidAlgebra.lift`: given an additive homomor
phism
`f : k →+ R` and a homomorphism `g : G → R`, returns the additive homomorphism f
rom
`SkewMonoidAlgebra k G` such that `liftNC f g (single a b) = f b * g a`.

If `k` is a semiring and `f` is a ring homomorphism and for all `x : R`, `y : G`
 the equality
`(f (y • x)) * g y = (g y) * (f x))` holds, then the result is a ring homomorphi
sm (see
`SkewMonoidAlgebra.liftNCRingHom`).

If `R` is a `k`-algebra and `f = algebraMap k R`, then the result is an algebra 
homomorphism called
`SkewMonoidAlgebra.lift`.
-/
def liftNC {R : Type*} [NonUnitalNonAssocSemiring R] (f : k →+ R) (g : G → R) :
    SkewMonoidAlgebra k G →+ R :=
  (Finsupp.liftAddHom fun x ↦ (AddMonoidHom.mulRight (g x)).comp f).comp
    (AddEquiv.toAddMonoidHom coeffAddEquiv)
/-
**SkewMonoidAlgebra.liftNC_single** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} [inst : AddCommMonoid k] {R : Type u_5} [i
nst_1 : NonUnitalNonAssocSemiring R]   (f : k →+ R) (g : G → R) (a : G) (b : k),
 (SkewMonoidAlgebra.liftNC f g) (SkewMonoidAlgebra.single a b) = f b * g a
参数：f : k →+ R；g : G → R；a : G；b : k；SkewMonoidAlgebra.liftNC f g；SkewMonoidAlgeb
ra.single a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.liftAddHom_apply_single`：liftAddHom_apply_single [AddZeroClass M
] [AddCommMonoid N] (f : α -> M ->+ N) (a : α) (b : M) : (liftAddHom (α
-/
@[simp] theorem liftNC_single {R : Type*} [NonUnitalNonAssocSemiring R] (f : k →+ R)
    (g : G → R) (a : G) (b : k) : liftNC f g (single a b) = f b * g a :=
  Finsupp.liftAddHom_apply_single _ _ _
/-
**SkewMonoidAlgebra.eq_liftNC** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：eq_liftNC {R : Type*} [NonUnitalNonAssocSemiring R] (f : k ->+ R) (g : G -
> R) (l : SkewMonoidAlgebra k G ->+ R) (h : forall a b, l (single a b) = f b * g
 a) : l = liftNC f g
参数：f : k ->+ R；g : G -> R；l : SkewMonoidAlgebra k G ->+ R；h : forall a b, l (sin
gle a b) = f b * g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.addHom_ext`：addHom_ext {M : Type*} [AddZeroClass M] {f
 g : SkewMonoidAlgebra k G ->+ M} (h : forall a b, f (single a b) = g (single a 
b)) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.liftNC_single`：∀ {k : Type u_1} {G : Type u_2} [inst :
 AddCommMonoid k] {R : Type u_5} [inst_1 : NonUnitalNonAssocSemiring R]   (f : k
 →+ R) (g : G → R) (a…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_liftNC {R : Type*} [NonUnitalNonAssocSemiring R] (f : k →+ R) (g : G → R)
    (l : SkewMonoidAlgebra k G →+ R) (h : ∀ a b, l (single a b) = f b * g a) : l = liftNC f g := by
  ext a b; simp_all

end mapDomain

end AddCommMonoid

section AddGroup

variable [AddGroup k]

/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[no_expose] instance : Neg (SkewMonoidAlgebra k G) :=
  ⟨fun ⟨a⟩ ↦ ⟨-a⟩⟩

@[simp]
/-
**SkewMonoidAlgebra.ofCoeff_neg** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：ofCoeff_neg {a} : (⟨-a⟩ : SkewMonoidAlgebra k G) = -⟨a⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofCoeff_neg {a} : (⟨-a⟩ : SkewMonoidAlgebra k G) = -⟨a⟩ :=
  (rfl)

@[deprecated (since := "2026-07-04")] alias ofFinsupp_neg := ofCoeff_neg
/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddGroup (SkewMonoidAlgebra k G) where
  zsmul := zsmulRec
  neg_add_cancel a := by cases a; simp [← ofCoeff_neg, ← ofCoeff_add]

@[simp]
/-
**SkewMonoidAlgebra.coeff_neg** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：coeff_neg (a : SkewMonoidAlgebra k G) : (-a).coeff = -a.coeff
参数：a : SkewMonoidAlgebra k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.map_neg`：∀ {G : Type u_7} {H : Type u_8} [inst : AddGroup G] [i
nst_1 : SubtractionMonoid H] (h : G ≃+ H) (x : G), h (-x) = -h x
-/
theorem coeff_neg (a : SkewMonoidAlgebra k G) : (-a).coeff = -a.coeff :=
  coeffAddEquiv.map_neg a

@[deprecated (since := "2026-07-04")] alias toFinsupp_neg := coeff_neg

@[simp]
/-
**SkewMonoidAlgebra.ofCoeff_sub** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：ofCoeff_sub {a b} : (⟨a - b⟩ : SkewMonoidAlgebra k G) = ⟨a⟩ - ⟨b⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.map_sub`：∀ {G : Type u_7} {H : Type u_8} [inst : AddGroup G] [i
nst_1 : SubtractionMonoid H] (h : G ≃+ H) (x y : G),   h (x - y) = h x - h y
-/
theorem ofCoeff_sub {a b} : (⟨a - b⟩ : SkewMonoidAlgebra k G) = ⟨a⟩ - ⟨b⟩ :=
  coeffAddEquiv.symm.map_sub a b

@[deprecated (since := "2026-07-04")] alias ofFinsupp_sub := ofCoeff_sub

@[simp]
/-
**SkewMonoidAlgebra.coeff_sub** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：coeff_sub (a b : SkewMonoidAlgebra k G) : (a - b).coeff = a.coeff - b.coef
f
参数：a b : SkewMonoidAlgebra k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.map_sub`：∀ {G : Type u_7} {H : Type u_8} [inst : AddGroup G] [i
nst_1 : SubtractionMonoid H] (h : G ≃+ H) (x y : G),   h (x - y) = h x - h y
-/
theorem coeff_sub (a b : SkewMonoidAlgebra k G) :
    (a - b).coeff = a.coeff - b.coeff :=
  coeffAddEquiv.map_sub a b

@[deprecated (since := "2026-07-04")] alias toFinsupp_sub := coeff_sub

@[simp]
/-
**SkewMonoidAlgebra.single_neg** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：single_neg (a : G) (b : k) : single a (-b) = -single a b
参数：a : G；b : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.single_neg`：single_neg (a : ι) (b : G) : single a (-b) = -single
 a b
· 使用定理 `SkewMonoidAlgebra.ofCoeff_neg`：ofCoeff_neg {a} : (⟨-a⟩ : SkewMonoidAlgeb
ra k G) = -⟨a⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_neg (a : G) (b : k) : single a (-b) = -single a b := by
  simp [← ofCoeff_single]

end AddGroup

section AddCommGroup

variable [AddCommGroup k]

/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (SkewMonoidAlgebra k G) where
  add_comm

end AddCommGroup

section AddGroupWithOne

variable [AddGroupWithOne k] [One G]

/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddGroupWithOne (SkewMonoidAlgebra k G) where
  __ := instAddGroup
/-
**SkewMonoidAlgebra.intCast_def** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：intCast_def (z : Int) : (z : SkewMonoidAlgebra k G) = single (1 : G) (z : 
k)
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `SkewMonoidAlgebra.single_nat`：single_nat (n : Nat) : (single 1 n : SkewM
onoidAlgebra k G) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `SkewMonoidAlgebra.single_add`：single_add (a : G) (b₁ b₂ : k) : single a 
(b₁ + b₂) = single a b₁ + single a b₂
· 使用定理 `SkewMonoidAlgebra.single_neg`：single_neg (a : G) (b : k) : single a (-b)
 = -single a b
-/
theorem intCast_def (z : ℤ) : (z : SkewMonoidAlgebra k G) = single (1 : G) (z : k) := by
  cases z <;> simp

end AddGroupWithOne

section Mul

/-- Interaction of `sum` and `•` assuming some multiplication structure. -/
/-
**SkewMonoidAlgebra.sum_smul_index** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`
。
形式化陈述：sum_smul_index {N : Type*} [AddCommMonoid N] [NonUnitalNonAssocSemiring k]
 {g : SkewMonoidAlgebra k G} {b : k} {h : G -> k -> N} (h0 : forall i, h i 0 = 0
) : (b • g).sum h = g.sum (h · <| b * ·)
参数：h0 : forall i, h i 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.coeff_smul`：coeff_smul {S : Type*} [SMulZeroClass S k]
 (a : S) (b : SkewMonoidAlgebra k G) : (a • b).coeff = a • b.coeff
· 使用定理 `Finsupp.sum_smul_index'`：sum_smul_index' [Zero M] [SMulZeroClass R M] [A
ddCommMonoid N] {g : α ->₀ M} {b : R} {h : α -> M -> N} (h0 : forall i, h i 0 = 
0) : (b • g).…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Interaction of `sum` and `•` assuming some multiplication structure.
-/
theorem sum_smul_index {N : Type*} [AddCommMonoid N] [NonUnitalNonAssocSemiring k]
    {g : SkewMonoidAlgebra k G} {b : k} {h : G → k → N} (h0 : ∀ i, h i 0 = 0) :
    (b • g).sum h = g.sum (h · <| b * ·) := by
  simp [sum_def, Finsupp.sum_smul_index' h0]

/-- Variant of the interaction of `sum` and `•` assuming some scalar multiplication structure. -/
/-
**SkewMonoidAlgebra.sum_smul_index'** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra
`。
形式化陈述：sum_smul_index' {N R : Type*} [AddCommMonoid k] [DistribSMul R k] [AddComm
Monoid N] {g : SkewMonoidAlgebra k G} {b : R} {h : G -> k -> N} (h0 : forall i, 
h i 0 = 0) : (b • g).sum h = g.sum (h · <| b • ·)
参数：h0 : forall i, h i 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.coeff_smul`：coeff_smul {S : Type*} [SMulZeroClass S k]
 (a : S) (b : SkewMonoidAlgebra k G) : (a • b).coeff = a • b.coeff
· 使用定理 `Finsupp.sum_smul_index'`：sum_smul_index' [Zero M] [SMulZeroClass R M] [A
ddCommMonoid N] {g : α ->₀ M} {b : R} {h : α -> M -> N} (h0 : forall i, h i 0 = 
0) : (b • g).…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Variant of the interaction of `sum` and `•` assuming some scalar multiplication 
structure.
-/
theorem sum_smul_index' {N R : Type*} [AddCommMonoid k]
    [DistribSMul R k] [AddCommMonoid N]
    {g : SkewMonoidAlgebra k G} {b : R} {h : G → k → N} (h0 : ∀ i, h i 0 = 0) :
    (b • g).sum h = g.sum (h · <| b • ·) := by
  simp only [sum_def, coeff_smul, Finsupp.sum_smul_index' h0]

@[simp]
/-
**SkewMonoidAlgebra.liftNC_one** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：liftNC_one {g_hom R : Type*} [NonAssocSemiring k] [One G] [Semiring R] [Fu
nLike g_hom G R] [OneHomClass g_hom G R] (f : k ->+* R) (g : g_hom) : liftNC (f 
: k ->+ R) g 1 = 1
参数：f : k ->+* R；g : g_hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.liftNC_single`：∀ {k : Type u_1} {G : Type u_2} [inst :
 AddCommMonoid k] {R : Type u_5} [inst_1 : NonUnitalNonAssocSemiring R]   (f : k
 →+ R) (g : G → R) (a…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftNC_one {g_hom R : Type*} [NonAssocSemiring k] [One G] [Semiring R] [FunLike g_hom G R]
    [OneHomClass g_hom G R] (f : k →+* R) (g : g_hom) : liftNC (f : k →+ R) g 1 = 1 := by
  simp only [one_def, liftNC_single, AddMonoidHom.coe_coe, map_one, mul_one]

end Mul

section Mul

variable [Mul G]

section SMul

variable [SMul G k] [NonUnitalNonAssocSemiring k]

/-- The product of `f g : SkewMonoidAlgebra k G` is the finitely supported function whose value
  at `a` is the sum of `f x * (x • g y)` over all pairs `x, y` such that `x * y = a`.
  (Think of a skew group ring.) -/
/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of `f g : SkewMonoidAlgebra k G` is the finitely supported function 
whose value
  at `a` is the sum of `f x * (x • g y)` over all pairs `x, y` such that `x * y 
= a`.
  (Think of a skew group ring.)
-/
instance : Mul (SkewMonoidAlgebra k G) :=
  ⟨fun f g ↦ f.sum fun a₁ b₁ ↦ g.sum fun a₂ b₂ ↦ single (a₁ * a₂) (b₁ * (a₁ • b₂))⟩
/-
**SkewMonoidAlgebra.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：mul_def {f g : SkewMonoidAlgebra k G} : f * g = f.sum fun a₁ b₁ => g.sum f
un a₂ b₂ => single (a₁ * a₂) (b₁ * (a₁ • b₂))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def {f g : SkewMonoidAlgebra k G} :
    f * g = f.sum fun a₁ b₁ ↦ g.sum fun a₂ b₂ ↦ single (a₁ * a₂) (b₁ * (a₁ • b₂)) :=
  rfl

end SMul

section DistribSMul

/-
**SkewMonoidAlgebra.instNonUnitalNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Ske
wMonoidAlgebra`。
形式化陈述：instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring k] [DistribSMul G
 k] : NonUnitalNonAssocSemiring (SkewMonoidAlgebra k G) where left_distrib f g h
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring k] [DistribSMul G k] :
    NonUnitalNonAssocSemiring (SkewMonoidAlgebra k G) where
  left_distrib f g h := by
    classical
    simp only [mul_def]
    refine Eq.trans (congr_arg (sum f) (funext₂ fun _ _ ↦ sum_add_index ?_ ?_)) ?_ <;>
      simp only [smul_zero, smul_add, mul_add, mul_zero, single_zero, single_add,
        forall_true_iff, sum_add]
  right_distrib f g h := by
    classical
    simp only [mul_def]
    refine Eq.trans (sum_add_index ?_ ?_) ?_ <;>
      simp only [add_mul, zero_mul, single_zero, single_add, forall_true_iff, sum_zero, sum_add]
  zero_mul f := sum_zero_index
  mul_zero f := Eq.trans (congr_arg (sum f) (funext₂ fun _ _ ↦ sum_zero_index)) sum_zero

variable {R : Type*} [Semiring R] [NonAssocSemiring k] [SMul G k]
/-
**SkewMonoidAlgebra.liftNC_mul** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：liftNC_mul {g_hom : Type*} [FunLike g_hom G R] [MulHomClass g_hom G R] (f 
: k ->+* R) (g : g_hom) (a b : SkewMonoidAlgebra k G) (h_comm : forall {x y}, y 
in a.support -> (f (y • b.coeff x)) * g y = (g y) * (f (b.coeff x))) : liftNC (f
 : k ->+ R) g (a * b) = liftNC (f : k ->+ R) g a * liftNC (f : k ->+ R) g b
参数：f : k ->+* R；g : g_hom；a b : SkewMonoidAlgebra k G；h_comm : forall {x y}, y i
n a.support -> (f (y • b.coeff x)) * g y = (g y) * (f (b.coeff x))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SkewMonoidAlgebra.sum_single`：sum_single (f : SkewMonoidAlgebra k G) : f
.sum single = f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SkewMonoidAlgebra.map_sum`：map_sum {N P : Type*} [AddCommMonoid N] [AddC
ommMonoid P] {H : Type*} [FunLike H N P] [AddMonoidHomClass H N P] (h : H) (f : 
SkewMonoidAlgeb…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SkewMonoidAlgebra.liftNC_single`：∀ {k : Type u_1} {G : Type u_2} [inst :
 AddCommMonoid k] {R : Type u_5} [inst_1 : NonUnitalNonAssocSemiring R]   (f : k
 →+ R) (g : G → R) (a…
· 使用定理 `SkewMonoidAlgebra.sum_mul`：sum_mul {S : Type*} [NonUnitalNonAssocSemirin
g S] (b : S) (s : SkewMonoidAlgebra k G) {f : G -> k -> S} : s.sum f * b = s.sum
 fun a c => f a…
· 使用定理 `SkewMonoidAlgebra.mul_sum`：mul_sum {S : Type*} [NonUnitalNonAssocSemirin
g S] (b : S) (s : SkewMonoidAlgebra k G) {f : G -> k -> S} : b * s.sum f = s.sum
 fun a c => b *…
· 使用定理 `SkewMonoidAlgebra.sum_congr`：sum_congr {f : SkewMonoidAlgebra k G} {M : 
Type*} [AddCommMonoid M] {g₁ g₂ : G -> k -> M} (h : forall x in f.support, g₁ x 
(f.coeff x) = g₂ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem liftNC_mul {g_hom : Type*} [FunLike g_hom G R]
    [MulHomClass g_hom G R] (f : k →+* R) (g : g_hom) (a b : SkewMonoidAlgebra k G)
    (h_comm : ∀ {x y}, y ∈ a.support → (f (y • b.coeff x)) * g y = (g y) * (f (b.coeff x))) :
    liftNC (f : k →+ R) g (a * b) = liftNC (f : k →+ R) g a * liftNC (f : k →+ R) g b := by
  conv_rhs => rw [← sum_single a, ← sum_single b]
  simp_rw [mul_def, map_sum, liftNC_single, sum_mul, mul_sum]
  refine sum_congr fun y hy ↦ sum_congr fun x _hx ↦ ?_
  simp only [AddMonoidHom.coe_coe, map_mul]
  rw [mul_assoc, ← mul_assoc (f (y • b.coeff x)), h_comm hy, mul_assoc, mul_assoc]

end DistribSMul

end Mul

/-! #### Semiring structure -/

section Semiring

variable [Semiring k] [Monoid G] [MulSemiringAction G k]

open MulSemiringAction

/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NonUnitalSemiring (SkewMonoidAlgebra k G) where
  mul_assoc f g h := by
    induction f with
    | single x a => induction g with
      | single y b => induction h with
        | single z c => simp [mul_assoc, mul_smul, mul_def]
        | add => simp_all [mul_add]
      | add => simp_all [add_mul, mul_add]
    | add => simp_all [add_mul]
/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NonAssocSemiring (SkewMonoidAlgebra k G) where
  one_mul f := by
    induction f with
    | single g a => rw [one_def, mul_def, sum_single_index] <;> simp
    | add f g _ _ => simp_all [mul_add]
  mul_one f := by
    induction f with
    | single g a => rw [one_def, mul_def, sum_single_index, sum_single_index] <;> simp
    | add f g _ _ => simp_all [add_mul]
/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Semiring (SkewMonoidAlgebra k G) where
  __ := instNonUnitalSemiring
  __ := instNonAssocSemiring

variable {R : Type*} [Semiring R]

/-- `liftNC` as a `RingHom`, for when `f x` and `g y` commute -/
/-
**SkewMonoidAlgebra.liftNCRingHom** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：liftNCRingHom (f : k ->+* R) (g : G ->* R) (h_comm : forall {x y}, (f (y •
 x)) * g y = (g y) * (f x)) : SkewMonoidAlgebra k G ->+* R where __
参数：f : k ->+* R；g : G ->* R；h_comm : forall {x y}, (f (y • x)) * g y = (g y) * (
f x)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`liftNC` as a `RingHom`, for when `f x` and `g y` commute
-/
def liftNCRingHom (f : k →+* R) (g : G →* R) (h_comm : ∀ {x y}, (f (y • x)) * g y = (g y) * (f x)) :
    SkewMonoidAlgebra k G →+* R where
  __ := liftNC (f : k →+ R) g
  map_one' := liftNC_one _ _
  map_mul' _ _ := liftNC_mul _ _ _ _ fun {_ _} _ ↦ h_comm

end Semiring

/-! #### Derived instances -/

section DerivedInstances

/-
**SkewMonoidAlgebra.instNonUnitalNonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `SkewMon
oidAlgebra`。
形式化陈述：instNonUnitalNonAssocRing [Ring k] [Monoid G] [MulSemiringAction G k] : No
nUnitalNonAssocRing (SkewMonoidAlgebra k G) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNonAssocRing [Ring k] [Monoid G] [MulSemiringAction G k] :
    NonUnitalNonAssocRing (SkewMonoidAlgebra k G) where
  __ := instAddCommGroup
  __ := instNonUnitalNonAssocSemiring
/-
**SkewMonoidAlgebra.instNonUnitalRing** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgeb
ra`。
形式化陈述：instNonUnitalRing [Ring k] [Monoid G] [MulSemiringAction G k] : NonUnitalR
ing (SkewMonoidAlgebra k G) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalRing [Ring k] [Monoid G] [MulSemiringAction G k] :
    NonUnitalRing (SkewMonoidAlgebra k G) where
  __ := instAddCommGroup
  __ := instNonUnitalSemiring
/-
**SkewMonoidAlgebra.instNonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebr
a`。
形式化陈述：instNonAssocRing [Ring k] [Monoid G] [MulSemiringAction G k] : NonAssocRin
g (SkewMonoidAlgebra k G) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonAssocRing [Ring k] [Monoid G] [MulSemiringAction G k] :
    NonAssocRing (SkewMonoidAlgebra k G) where
  __ := instAddCommGroup
  __ := instNonAssocSemiring
/-
**SkewMonoidAlgebra.instCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebr
a`。
形式化陈述：instCommSemiring [CommSemiring k] [CommMonoid G] [MulSemiringAction G k] [
SMulCommClass G k k] : CommSemiring (SkewMonoidAlgebra k G) where mul_comm a b
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommSemiring [CommSemiring k] [CommMonoid G] [MulSemiringAction G k]
    [SMulCommClass G k k] : CommSemiring (SkewMonoidAlgebra k G) where
  mul_comm a b := by
    have hgk (g : G) (r : k) : g • r = r := by
      rw [← Algebra.algebraMap_self_apply r, smul_algebraMap g r]
    simp only [mul_def, hgk, sum_def]
    rw [Finsupp.sum_comm]
    exact Finsupp.sum_congr (fun x _ ↦ Finsupp.sum_congr
      (fun y _ ↦ by rw [mul_comm, mul_comm (a.coeff y) _]))
/-
**SkewMonoidAlgebra.instRing** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：instRing [Ring k] [Monoid G] [MulSemiringAction G k] : Ring (SkewMonoidAlg
ebra k G) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRing [Ring k] [Monoid G] [MulSemiringAction G k] : Ring (SkewMonoidAlgebra k G) where
  __ := instNonAssocRing
  __ := instSemiring

variable {S S₁ S₂ : Type*}
/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid k] [DistribSMul S k] :
    DistribSMul S (SkewMonoidAlgebra k G) where
  __ := coeff_injective.distribSMul ⟨⟨coeff, coeff_zero⟩, coeff_add⟩
    coeff_smul
/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid S] [AddMonoid k] [DistribMulAction S k] :
    DistribMulAction S (SkewMonoidAlgebra k G) where
  __ := coeff_injective.distribMulAction ⟨⟨coeff, coeff_zero (k := k)⟩, coeff_add⟩
      coeff_smul
/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring S] [AddCommMonoid k] [Module S k] :
    Module S (SkewMonoidAlgebra k G) where
  __ := coeff_injective.module _ ⟨⟨coeff, coeff_zero⟩, coeff_add⟩ coeff_smul
/-
**SkewMonoidAlgebra.instFaithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebr
a`。
形式化陈述：instFaithfulSMul [AddMonoid k] [SMulZeroClass S k] [FaithfulSMul S k] [Non
empty G] : FaithfulSMul S (SkewMonoidAlgebra k G) where eq_of_smul_eq_smul {_s₁ 
_s₂} h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.ofCoeff_smul`：ofCoeff_smul {S : Type*} [SMulZeroClass 
S k] (a : S) (b : G ->₀ k) : (⟨a • b⟩ : SkewMonoidAlgebra k G) = (a • ⟨b⟩ : Skew
MonoidAlgebra k G)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instFaithfulSMul [AddMonoid k] [SMulZeroClass S k] [FaithfulSMul S k] [Nonempty G] :
    FaithfulSMul S (SkewMonoidAlgebra k G) where
  eq_of_smul_eq_smul {_s₁ _s₂} h := by
    apply eq_of_smul_eq_smul fun a : G →₀ k ↦ congr_arg coeff _
    intro a
    simp_rw [ofCoeff_smul, h]
/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid k] [SMul S₁ S₂] [SMulZeroClass S₁ k] [SMulZeroClass S₂ k]
    [IsScalarTower S₁ S₂ k] : IsScalarTower S₁ S₂ (SkewMonoidAlgebra k G) :=
  ⟨fun _ _ ⟨_⟩ ↦ by simp_rw [← ofCoeff_smul, smul_assoc]⟩
/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid k] [SMulZeroClass S₁ k] [SMulZeroClass S₂ k] [SMulCommClass S₁ S₂ k] :
    SMulCommClass S₁ S₂ (SkewMonoidAlgebra k G) :=
  ⟨fun _ _ ⟨_⟩ ↦ by simp_rw [← ofCoeff_smul, smul_comm]⟩
/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid k] [SMulZeroClass S k] [SMulZeroClass Sᵐᵒᵖ k] [IsCentralScalar S k] :
    IsCentralScalar S (SkewMonoidAlgebra k G) :=
  ⟨fun _ ⟨_⟩ ↦ by simp_rw [← ofCoeff_smul, op_smul_eq_smul]⟩

section Module.Free

variable [Semiring S]

/-- Linear equivalence between `SkewMonoidAlgebra k G` and `G →₀ k`. -/
/-
**SkewMonoidAlgebra.coeffLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebr
a`。
形式化陈述：coeffLinearEquiv [AddCommMonoid k] [Module S k] : SkewMonoidAlgebra k G ≃ₗ
[S] (G ->₀ k)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear equivalence between `SkewMonoidAlgebra k G` and `G →₀ k`.
-/
def coeffLinearEquiv [AddCommMonoid k] [Module S k] : SkewMonoidAlgebra k G ≃ₗ[S] (G →₀ k) :=
  AddEquiv.toLinearEquiv coeffAddEquiv (by simp)

@[deprecated (since := "2026-07-04")] alias toFinsuppLinearEquiv := coeffLinearEquiv

/-- The basis on `SkewMonoidAlgebra k G` with basis vectors `fun i ↦ single i 1` -/
/-
**SkewMonoidAlgebra.basisSingleOne** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`
。
形式化陈述：basisSingleOne [Semiring k] : Module.Basis G k (SkewMonoidAlgebra k G) whe
re repr
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The basis on `SkewMonoidAlgebra k G` with basis vectors `fun i ↦ single i 1`
-/
def basisSingleOne [Semiring k] : Module.Basis G k (SkewMonoidAlgebra k G) where
  repr := coeffLinearEquiv
/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring k] : Module.Free k (SkewMonoidAlgebra k G) :=
  Module.Free.of_basis basisSingleOne

end Module.Free

variable {M α : Type*} [Monoid G] [AddCommMonoid M] [MulAction G α]

/-- Scalar multiplication acting on the domain.

This is not an instance as it would conflict with the action on the range.
See the file `MathlibTest/instance_diamonds.lean` for examples of such conflicts. -/
@[instance_reducible]
/-
**SkewMonoidAlgebra.comapSMul** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：comapSMul : SMul G (SkewMonoidAlgebra M α) where smul g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication acting on the domain.

This is not an instance as it would conflict with the action on the range.
See the file `MathlibTest/instance_diamonds.lean` for examples of such conflicts
.
-/
def comapSMul : SMul G (SkewMonoidAlgebra M α) where smul g := mapDomain (g • ·)

attribute [local instance] comapSMul
/-
**SkewMonoidAlgebra.comapSMul_def** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：comapSMul_def (g : G) (f : SkewMonoidAlgebra M α) : g • f = mapDomain (g •
 ·) f
参数：g : G；f : SkewMonoidAlgebra M α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comapSMul_def (g : G) (f : SkewMonoidAlgebra M α) : g • f = mapDomain (g • ·) f := rfl

@[simp]
/-
**SkewMonoidAlgebra.comapSMul_single** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebr
a`。
形式化陈述：comapSMul_single (g : G) (a : α) (b : M) : g • single a b = single (g • a)
 b
参数：g : G；a : α；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.mapDomain_single`：mapDomain_single {a : G} {b : k} : m
apDomain f (single a b) = single (f a) b
-/
theorem comapSMul_single (g : G) (a : α) (b : M) : g • single a b = single (g • a) b :=
  mapDomain_single

/-- `comapSMul` is multiplicative -/
@[instance_reducible]
/-
**SkewMonoidAlgebra.comapMulAction** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`
。
形式化陈述：comapMulAction : MulAction G (SkewMonoidAlgebra M α) where one_smul f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`comapSMul` is multiplicative
-/
def comapMulAction : MulAction G (SkewMonoidAlgebra M α) where
  one_smul f := by rw [comapSMul_def, one_smul_eq_id, mapDomain_id]
  mul_smul g g' f := by
    rw [comapSMul_def, comapSMul_def, comapSMul_def, ← comp_smul_left, mapDomain_comp]

attribute [local instance] comapMulAction
/-- This is not an instance as it conflicts with `SkewMonoidAlgebra.distribMulAction`
  when `G = kˣ`. -/
@[instance_reducible]
/-
**SkewMonoidAlgebra.comapDistribMulActionSelf** 是 Mathlib 中的一个定义，位于命名空间 `SkewMon
oidAlgebra`。
形式化陈述：comapDistribMulActionSelf [AddCommMonoid k] : DistribMulAction G (SkewMono
idAlgebra k G) where smul_zero g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is not an instance as it conflicts with `SkewMonoidAlgebra.distribMulAction
`
  when `G = kˣ`.
-/
def comapDistribMulActionSelf [AddCommMonoid k] :
    DistribMulAction G (SkewMonoidAlgebra k G) where
  smul_zero g := by
    ext
    simp [comapSMul_def, mapDomain]
  smul_add g f f' := by
    ext
    simp [comapSMul_def, map_add]

end DerivedInstances

section coeff_mul

variable [Semiring k]

section Mul

variable [Mul G] [SMulZeroClass G k]

/-
**SkewMonoidAlgebra.coeff_mul** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：coeff_mul [DecidableEq G] (f g : SkewMonoidAlgebra k G) (x : G) : (f * g).
coeff x = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => if a₁ * a₂ = x then b₁ * a₁ • b₂
 else 0
参数：f g : SkewMonoidAlgebra k G；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.mul_def`：mul_def {f g : SkewMonoidAlgebra k G} : f * g
 = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => single (a₁ * a₂) (b₁ * (a₁ • b₂))
· 使用定理 `SkewMonoidAlgebra.coeff_sum`：coeff_sum {k' G' : Type*} [AddCommMonoid k'
] {f : SkewMonoidAlgebra k G} {g : G -> k -> SkewMonoidAlgebra k' G'} {a₂ : G'} 
: (f.sum g).coeff…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SkewMonoidAlgebra.coeff_single_apply`：coeff_single_apply {a a' : G} {b :
 k} [Decidable (a = a')] : coeff (single a b) a' = if a = a' then b else 0
-/
theorem coeff_mul [DecidableEq G] (f g : SkewMonoidAlgebra k G)
    (x : G) : (f * g).coeff x = f.sum fun a₁ b₁ ↦ g.sum fun a₂ b₂ ↦
      if a₁ * a₂ = x then b₁ * a₁ • b₂ else 0 := by
  rw [mul_def, coeff_sum]; congr; ext
  rw [coeff_sum]; congr; ext
  exact coeff_single_apply
/-
**SkewMonoidAlgebra.coeff_mul_antidiagonal_of_finset** 是 Mathlib 中的一个定理，位于命名空间 `
SkewMonoidAlgebra`。
形式化陈述：coeff_mul_antidiagonal_of_finset (f g : SkewMonoidAlgebra k G) (x : G) (s 
: Finset (G × G)) (hs : forall {p : G × G}, p in s ↔ p.1 * p.2 = x) : (f * g).co
eff x = ∑ p in s, f.coeff p.1 * p.1 • g.coeff p.2
参数：f g : SkewMonoidAlgebra k G；x : G；s : Finset (G × G)；hs : forall {p : G × G},
 p in s ↔ p.1 * p.2 = x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.coeff_mul`：coeff_mul [DecidableEq G] (f g : SkewMonoid
Algebra k G) (x : G) : (f * g).coeff x = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => i
f a₁ * a₂ = x the…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst
 : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈ s ×ˢ 
t, f x =…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_filter`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst 
: AddCommMonoid M] (p : ι → Prop) [inst_1 : DecidablePred p]   (f : ι → M), ∑ a 
∈ s wit…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem coeff_mul_antidiagonal_of_finset (f g : SkewMonoidAlgebra k G) (x : G)
    (s : Finset (G × G)) (hs : ∀ {p : G × G}, p ∈ s ↔ p.1 * p.2 = x) :
    (f * g).coeff x = ∑ p ∈ s, f.coeff p.1 * p.1 • g.coeff p.2 := by
  classical
  let F : G × G → k := fun p ↦ if p.1 * p.2 = x then f.coeff p.1 * p.1 • g.coeff p.2 else 0
  calc
    (f * g).coeff x = ∑ a₁ ∈ f.support, ∑ a₂ ∈ g.support, F (a₁, a₂) := coeff_mul f g x
    _ = ∑ p ∈ f.support ×ˢ g.support, F p := by rw [Finset.sum_product]
    _ = ∑ p ∈ (f.support ×ˢ g.support).filter fun p : G × G ↦ p.1 * p.2 = x,
      f.coeff p.1 * p.1 • g.coeff p.2 := (Finset.sum_filter _ _).symm
    _ = ∑ p ∈ s.filter fun p : G × G ↦ p.1 ∈ f.support ∧ p.2 ∈ g.support,
      f.coeff p.1 * p.1 • g.coeff p.2 :=
      (Finset.sum_congr (by ext; simp [Finset.mem_filter, Finset.mem_product, hs, and_comm])
        fun _ _ ↦ rfl)
    _ = ∑ p ∈ s, f.coeff p.1 * p.1 • g.coeff p.2 :=
      Finset.sum_subset (Finset.filter_subset _ _) fun p hps hp ↦ by
        simp only [Finset.mem_filter, mem_support_iff, not_and, Classical.not_not] at hp ⊢
        by_cases h1 : f.coeff p.1 = 0 <;> simp_all
/-
**SkewMonoidAlgebra.coeff_mul_antidiagonal_finsum** 是 Mathlib 中的一个定理，位于命名空间 `Ske
wMonoidAlgebra`。
形式化陈述：coeff_mul_antidiagonal_finsum (f g : SkewMonoidAlgebra k G) (x : G) : (f *
 g).coeff x = ∑ᶠ p in {p : G × G | p.1 * p.2 = x}, f.coeff p.1 * p.1 • g.coeff p
.2
参数：f g : SkewMonoidAlgebra k G；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.inter_of_right`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t :
 Set α), (t ∩ s).Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_product`：coe_product (s : Finset α) (t : Finset β) : (↑(s ×ˢ 
t) : Set (α × β)) = (s : Set α) ×ˢ t
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finsum_mem_inter_support`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCom
mMonoid M] (f : α → M) (s : Set α),   ∑ᶠ (i : α) (_ : i ∈ s ∩ Function.support f
), f i = ∑ᶠ (i…
· 使用定理 `finsum_mem_eq_finite_toFinset_sum`：∀ {α : Type u_1} {M : Type u_5} [inst
 : AddCommMonoid M] (f : α → M) {s : Set α} (hs : s.Finite),   ∑ᶠ (i : α) (_ : i
 ∈ s), f i = ∑ i ∈ hs.t…
· 使用定理 `SkewMonoidAlgebra.coeff_mul`：coeff_mul [DecidableEq G] (f g : SkewMonoid
Algebra k G) (x : G) : (f * g).coeff x = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => i
f a₁ * a₂ = x the…
· 使用定理 `Finset.sum_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst
 : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈ s ×ˢ 
t, f x =…
· 使用定理 `Finset.sum_filter`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst 
: AddCommMonoid M] (p : ι → Prop) [inst_1 : DecidablePred p]   (f : ι → M), ∑ a 
∈ s wit…
· 使用定理 `Finset.sum_congr_of_eq_on_inter`：∀ {ι : Type u_5} {M : Type u_6} {s₁ s₂ 
: Finset ι} {f g : ι → M} [inst : AddCommMonoid M],   (∀ a ∈ s₁, a ∉ s₂ → f a = 
0) →     (∀ a ∈ s₂, a…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
（共 36 条，此处仅展示前 30 条）
-/
theorem coeff_mul_antidiagonal_finsum (f g : SkewMonoidAlgebra k G) (x : G) :
    (f * g).coeff x = ∑ᶠ p ∈ {p : G × G | p.1 * p.2 = x}, f.coeff p.1 * p.1 • g.coeff p.2 := by
  have : ({p : G × G | p.1 * p.2 = x}
      ∩ Function.support fun p ↦ f.coeff p.1 * p.1 • g.coeff p.2).Finite := by
    apply Set.Finite.inter_of_right
    apply Set.Finite.subset (Finset.finite_toSet ((f.support).product (g.support)))
    aesop
  rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ this]
  classical
  let s := Set.Finite.toFinset (s := ({p : G × G | p.1 * p.2 = x}
    ∩ Function.support fun p ↦ f.coeff p.1 * p.1 • g.coeff p.2)) this
  let F : G × G → k := fun p ↦ if p.1 * p.2 = x then f.coeff p.1 * p.1 • g.coeff p.2 else 0
  calc
    (f * g).coeff x = ∑ a₁ ∈ f.support, ∑ a₂ ∈ g.support, F (a₁, a₂) := coeff_mul f g x
    _ = ∑ p ∈ f.support ×ˢ g.support, F p := by rw [Finset.sum_product]
    _ = ∑ p ∈ (f.support ×ˢ g.support).filter fun p : G × G ↦ p.1 * p.2 = x,
      f.coeff p.1 * p.1 • g.coeff p.2 := (Finset.sum_filter _ _).symm
    _ = ∑ p ∈ s.filter fun p : G × G ↦ p.1 ∈ f.support ∧ p.2 ∈ g.support,
      f.coeff p.1 * p.1 • g.coeff p.2 := by
        apply Finset.sum_congr_of_eq_on_inter <;> aesop
    _ = ∑ p ∈ s, f.coeff p.1 * p.1 • g.coeff p.2 :=
      Finset.sum_subset (Finset.filter_subset _ _) fun p hps hp ↦ by
        simp only [Finset.mem_filter, mem_support_iff, not_and, Classical.not_not] at hp ⊢
        by_cases h1 : f.coeff p.1 = 0 <;> simp_all
/-
**SkewMonoidAlgebra.coeff_mul_single_aux** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAl
gebra`。
形式化陈述：coeff_mul_single_aux (f : SkewMonoidAlgebra k G) {r : k} {x y z : G} (H : 
forall a, a * x = z ↔ a = y) : (f * single x r).coeff z = f.coeff y * y • r
参数：f : SkewMonoidAlgebra k G；H : forall a, a * x = z ↔ a = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.sum_single_index`：sum_single_index {N} [AddCommMonoid 
N] {a : G} {b : k} {h : G -> k -> N} (h_zero : h a 0 = 0) : (SkewMonoidAlgebra.s
ingle a b).sum h = h a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SkewMonoidAlgebra.coeff_mul`：coeff_mul [DecidableEq G] (f g : SkewMonoid
Algebra k G) (x : G) : (f * g).coeff x = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => i
f a₁ * a₂ = x the…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SkewMonoidAlgebra.sum_ite_eq'`：sum_ite_eq' {N : Type*} [AddCommMonoid N]
 [DecidableEq G] (f : SkewMonoidAlgebra k G) (a : G) (b : G -> k -> N) : (f.sum 
fun (x : G) (v : k)…
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem coeff_mul_single_aux (f : SkewMonoidAlgebra k G) {r : k} {x y z : G}
    (H : ∀ a, a * x = z ↔ a = y) : (f * single x r).coeff z = f.coeff y * y • r := by
  classical
  have A : ∀ a₁ b₁, ((single x r).sum fun a₂ b₂ ↦ ite (a₁ * a₂ = z) (b₁ * a₁ • b₂) 0) =
      ite (a₁ * x = z) (b₁ * a₁ • r) 0 :=
    fun a₁ b₁ ↦ sum_single_index <| by simp
  calc
    (f * (single x r)).coeff z =
        sum f fun a b ↦ if a = y then b * y • r else 0 := by simp [coeff_mul, A, H, sum_ite_eq']
    _ = if y ∈ f.support then f.coeff y * y • r else 0 := (f.support.sum_ite_eq' _ _)
    _ = f.coeff y * y • r := by
      split_ifs with h <;> simp [support] at h <;> simp [h]
/-
**SkewMonoidAlgebra.coeff_mul_single_of_not_exists_mul** 是 Mathlib 中的一个定理，位于命名空间
 `SkewMonoidAlgebra`。
形式化陈述：coeff_mul_single_of_not_exists_mul (r : k) {g g' : G} (x : SkewMonoidAlgeb
ra k G) (h : forall x, ¬g' = x * g) : (x * single g r).coeff g' = 0
参数：r : k；x : SkewMonoidAlgebra k G；h : forall x, ¬g' = x * g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SkewMonoidAlgebra.coeff_mul`：coeff_mul [DecidableEq G] (f g : SkewMonoid
Algebra k G) (x : G) : (f * g).coeff x = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => i
f a₁ * a₂ = x the…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SkewMonoidAlgebra.sum_single_index`：sum_single_index {N} [AddCommMonoid 
N] {a : G} {b : k} {h : G -> k -> N} (h_zero : h a 0 = 0) : (SkewMonoidAlgebra.s
ingle a b).sum h = h a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem coeff_mul_single_of_not_exists_mul (r : k) {g g' : G} (x : SkewMonoidAlgebra k G)
    (h : ∀ x, ¬g' = x * g) : (x * single g r).coeff g' = 0 := by
  classical
  simp only [coeff_mul, smul_zero, mul_zero, ite_self, sum_single_index]
  apply Finset.sum_eq_zero
  simp_rw [ite_eq_right_iff]
  rintro _ _ rfl
  exact False.elim (h _ rfl)
/-
**SkewMonoidAlgebra.coeff_single_mul_aux** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAl
gebra`。
形式化陈述：coeff_single_mul_aux (f : SkewMonoidAlgebra k G) {r : k} {x y z : G} (H : 
forall a, x * a = y ↔ a = z) : (single x r * f).coeff y = r * x • f.coeff z
参数：f : SkewMonoidAlgebra k G；H : forall a, x * a = y ↔ a = z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `SkewMonoidAlgebra.sum_zero`：sum_zero {N : Type*} [AddCommMonoid N] {f : 
SkewMonoidAlgebra k G} : (f.sum fun _ _ => (0 : N)) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SkewMonoidAlgebra.coeff_mul`：coeff_mul [DecidableEq G] (f g : SkewMonoid
Algebra k G) (x : G) : (f * g).coeff x = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => i
f a₁ * a₂ = x the…
· 使用定理 `SkewMonoidAlgebra.sum_single_index`：sum_single_index {N} [AddCommMonoid 
N] {a : G} {b : k} {h : G -> k -> N} (h_zero : h a 0 = 0) : (SkewMonoidAlgebra.s
ingle a b).sum h = h a b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SkewMonoidAlgebra.sum_ite_eq'`：sum_ite_eq' {N : Type*} [AddCommMonoid N]
 [DecidableEq G] (f : SkewMonoidAlgebra k G) (a : G) (b : G -> k -> N) : (f.sum 
fun (x : G) (v : k)…
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem coeff_single_mul_aux (f : SkewMonoidAlgebra k G) {r : k} {x y z : G}
    (H : ∀ a, x * a = y ↔ a = z) : (single x r * f).coeff y = r * x • f.coeff z := by
  classical
  have : (f.sum fun a b ↦ ite (x * a = y) (0 * x • b) 0) = 0 := by simp
  calc
    (single x r * f).coeff y =
        sum f fun a b ↦ ite (x * a = y) (r * x • b) 0 :=
      (coeff_mul _ _ _).trans <| sum_single_index this
    _ = f.sum fun a b ↦ ite (a = z) (r * x • b) 0 := by simp [H]
    _ = if z ∈ f.support then r * x • f.coeff z else 0 := (f.support.sum_ite_eq' _ _)
    _ = _ := by split_ifs with h <;> simp [support] at h <;> simp [h]
/-
**SkewMonoidAlgebra.coeff_single_mul_of_not_exists_mul** 是 Mathlib 中的一个定理，位于命名空间
 `SkewMonoidAlgebra`。
形式化陈述：coeff_single_mul_of_not_exists_mul (r : k) {g g' : G} (x : SkewMonoidAlgeb
ra k G) (h : ¬exists d, g' = g * d) : (single g r * x).coeff g' = 0
参数：r : k；x : SkewMonoidAlgebra k G；h : ¬exists d, g' = g * d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.coeff_mul`：coeff_mul [DecidableEq G] (f g : SkewMonoid
Algebra k G) (x : G) : (f * g).coeff x = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => i
f a₁ * a₂ = x the…
· 使用定理 `SkewMonoidAlgebra.sum_single_index`：sum_single_index {N} [AddCommMonoid 
N] {a : G} {b : k} {h : G -> k -> N} (h_zero : h a 0 = 0) : (SkewMonoidAlgebra.s
ingle a b).sum h = h a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `SkewMonoidAlgebra.sum_zero`：sum_zero {N : Type*} [AddCommMonoid N] {f : 
SkewMonoidAlgebra k G} : (f.sum fun _ _ => (0 : N)) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem coeff_single_mul_of_not_exists_mul (r : k) {g g' : G} (x : SkewMonoidAlgebra k G)
    (h : ¬∃ d, g' = g * d) : (single g r * x).coeff g' = 0 := by
  classical
  rw [coeff_mul, sum_single_index]
  · apply Finset.sum_eq_zero
    simp_rw [ite_eq_right_iff]
    rintro g'' _hg'' rfl
    exact absurd ⟨_, rfl⟩ h
  · simp

end Mul

section Monoid

variable [Monoid G] [MulSemiringAction G k]

/-
**SkewMonoidAlgebra.coeff_mul_single_one** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAl
gebra`。
形式化陈述：coeff_mul_single_one (f : SkewMonoidAlgebra k G) (r : k) (x : G) : (f * si
ngle 1 r).coeff x = f.coeff x * x • r
参数：f : SkewMonoidAlgebra k G；r : k；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.coeff_mul_single_aux`：coeff_mul_single_aux (f : SkewMo
noidAlgebra k G) {r : k} {x y z : G} (H : forall a, a * x = z ↔ a = y) : (f * si
ngle x r).coeff z = f.coeff …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coeff_mul_single_one (f : SkewMonoidAlgebra k G) (r : k) (x : G) :
    (f * single 1 r).coeff x = f.coeff x * x • r :=
  f.coeff_mul_single_aux fun a ↦ by rw [mul_one]
/-
**SkewMonoidAlgebra.coeff_single_one_mul** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAl
gebra`。
形式化陈述：coeff_single_one_mul (f : SkewMonoidAlgebra k G) (r : k) (x : G) : (single
 (1 : G) r * f).coeff x = r * f.coeff x
参数：f : SkewMonoidAlgebra k G；r : k；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.coeff_single_mul_aux`：coeff_single_mul_aux (f : SkewMo
noidAlgebra k G) {r : k} {x y z : G} (H : forall a, x * a = y ↔ a = z) : (single
 x r * f).coeff y = r * x • …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_single_one_mul (f : SkewMonoidAlgebra k G) (r : k) (x : G) :
    (single (1 : G) r * f).coeff x = r * f.coeff x := by
  simp [coeff_single_mul_aux, one_smul]

end Monoid

section Group

-- We now prove some additional statements that hold for group algebras.
variable [Group G] [MulSemiringAction G k]

@[simp]
/-
**SkewMonoidAlgebra.coeff_mul_single** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebr
a`。
形式化陈述：coeff_mul_single (f : SkewMonoidAlgebra k G) (r : k) (x y : G) : (f * sing
le x r).coeff y = f.coeff (y * x⁻¹) * (y * x⁻¹) • r
参数：f : SkewMonoidAlgebra k G；r : k；x y : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.coeff_mul_single_aux`：coeff_mul_single_aux (f : SkewMo
noidAlgebra k G) {r : k} {x y z : G} (H : forall a, a * x = z ↔ a = y) : (f * si
ngle x r).coeff z = f.coeff …
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `eq_mul_inv_iff_mul_eq`：eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b
-/
theorem coeff_mul_single (f : SkewMonoidAlgebra k G) (r : k) (x y : G) :
    (f * single x r).coeff y = f.coeff (y * x⁻¹) * (y * x⁻¹) • r :=
  f.coeff_mul_single_aux fun _a ↦ eq_mul_inv_iff_mul_eq.symm

@[simp]
/-
**SkewMonoidAlgebra.coeff_single_mul** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebr
a`。
形式化陈述：coeff_single_mul (r : k) (x : G) (f : SkewMonoidAlgebra k G) (y : G) : (si
ngle x r * f).coeff y = r * x • f.coeff (x⁻¹ * y)
参数：r : k；x : G；f : SkewMonoidAlgebra k G；y : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.coeff_single_mul_aux`：coeff_single_mul_aux (f : SkewMo
noidAlgebra k G) {r : k} {x y z : G} (H : forall a, x * a = y ↔ a = z) : (single
 x r * f).coeff y = r * x • …
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `eq_inv_mul_iff_mul_eq`：eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c
-/
theorem coeff_single_mul (r : k) (x : G) (f : SkewMonoidAlgebra k G) (y : G) :
    (single x r * f).coeff y = r * x • f.coeff (x⁻¹ * y) :=
  f.coeff_single_mul_aux fun _z ↦ eq_inv_mul_iff_mul_eq.symm
/-
**SkewMonoidAlgebra.coeff_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`
。
形式化陈述：coeff_mul_left (f g : SkewMonoidAlgebra k G) (x : G) : (f * g).coeff x = f
.sum fun a b => b * a • g.coeff (a⁻¹ * x)
参数：f g : SkewMonoidAlgebra k G；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SkewMonoidAlgebra.coeff_sum`：coeff_sum {k' G' : Type*} [AddCommMonoid k'
] {f : SkewMonoidAlgebra k G} {g : G -> k -> SkewMonoidAlgebra k' G'} {a₂ : G'} 
: (f.sum g).coeff…
· 使用定理 `SkewMonoidAlgebra.sum_mul`：sum_mul {S : Type*} [NonUnitalNonAssocSemirin
g S] (b : S) (s : SkewMonoidAlgebra k G) {f : G -> k -> S} : s.sum f * b = s.sum
 fun a c => f a…
· 使用定理 `SkewMonoidAlgebra.sum_single`：sum_single (f : SkewMonoidAlgebra k G) : f
.sum single = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SkewMonoidAlgebra.coeff_single_mul`：coeff_single_mul (r : k) (x : G) (f 
: SkewMonoidAlgebra k G) (y : G) : (single x r * f).coeff y = r * x • f.coeff (x
⁻¹ * y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_mul_left (f g : SkewMonoidAlgebra k G) (x : G) :
    (f * g).coeff x = f.sum fun a b ↦ b * a • g.coeff (a⁻¹ * x) :=
  calc
    (f * g).coeff x = sum f fun a b ↦ (single a b * g).coeff x := by
      rw [← coeff_sum, ← sum_mul g f, f.sum_single]
    _ = _ := by simp
/-
**SkewMonoidAlgebra.coeff_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra
`。
形式化陈述：coeff_mul_right (f g : SkewMonoidAlgebra k G) (x : G) : (f * g).coeff x = 
g.sum fun a b => f.coeff (x * a⁻¹) * (x * a⁻¹) • b
参数：f g : SkewMonoidAlgebra k G；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SkewMonoidAlgebra.coeff_sum`：coeff_sum {k' G' : Type*} [AddCommMonoid k'
] {f : SkewMonoidAlgebra k G} {g : G -> k -> SkewMonoidAlgebra k' G'} {a₂ : G'} 
: (f.sum g).coeff…
· 使用定理 `SkewMonoidAlgebra.mul_sum`：mul_sum {S : Type*} [NonUnitalNonAssocSemirin
g S] (b : S) (s : SkewMonoidAlgebra k G) {f : G -> k -> S} : b * s.sum f = s.sum
 fun a c => b *…
· 使用定理 `SkewMonoidAlgebra.sum_single`：sum_single (f : SkewMonoidAlgebra k G) : f
.sum single = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SkewMonoidAlgebra.coeff_mul_single`：coeff_mul_single (f : SkewMonoidAlge
bra k G) (r : k) (x y : G) : (f * single x r).coeff y = f.coeff (y * x⁻¹) * (y *
 x⁻¹) • r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_mul_right (f g : SkewMonoidAlgebra k G) (x : G) :
    (f * g).coeff x = g.sum fun a b ↦ f.coeff (x * a⁻¹) * (x * a⁻¹) • b :=
  calc
    (f * g).coeff x = sum g fun a b ↦ (f * single a b).coeff x := by
      rw [← coeff_sum, ← mul_sum f g, g.sum_single]
    _ = _ := by simp

end Group

end coeff_mul

section AddHom

variable [AddCommMonoid k]

/-- `single` as an `AddMonoidHom`.

See `lsingle` for the stronger version as a linear map. -/
@[simps]
/-
**SkewMonoidAlgebra.singleAddHom** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：singleAddHom (a : G) : k ->+ SkewMonoidAlgebra k G where toFun
参数：a : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`single` as an `AddMonoidHom`.

See `lsingle` for the stronger version as a linear map.
-/
def singleAddHom (a : G) : k →+ SkewMonoidAlgebra k G where
  toFun := single a
  map_zero' := single_zero a
  map_add' _ := single_add a _

@[ext high]
/-
**SkewMonoidAlgebra.addHom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：addHom_ext' {N : Type*} [AddZeroClass N] ⦃f g : SkewMonoidAlgebra k G ->+ 
N⦄ (H : forall x, f.comp (singleAddHom x) = g.comp (singleAddHom x)) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.addHom_ext`：addHom_ext {M : Type*} [AddZeroClass M] {f
 g : SkewMonoidAlgebra k G ->+ M} (h : forall a b, f (single a b) = g (single a 
b)) : f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem addHom_ext' {N : Type*} [AddZeroClass N] ⦃f g : SkewMonoidAlgebra k G →+ N⦄
    (H : ∀ x, f.comp (singleAddHom x) = g.comp (singleAddHom x)) : f = g :=
  addHom_ext fun x ↦ DFunLike.congr_fun (H x)

end AddHom

section Semiring

variable [Semiring k]

section singleOneRingHom

variable [Monoid G] [MulSemiringAction G k]

@[simp]
/-
**SkewMonoidAlgebra.single_mul_single** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgeb
ra`。
形式化陈述：single_mul_single {a₁ a₂ : G} {b₁ b₂ : k} : (single a₁ b₁) * (single a₂ b₂
) = single (a₁ * a₂) (b₁ * a₁ • b₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SkewMonoidAlgebra.sum_single_index`：sum_single_index {N} [AddCommMonoid 
N] {a : G} {b : k} {h : G -> k -> N} (h_zero : h a 0 = 0) : (SkewMonoidAlgebra.s
ingle a b).sum h = h a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `SkewMonoidAlgebra.single_zero`：single_zero (a : G) : (single a 0 : SkewM
onoidAlgebra k G) = 0
· 使用定理 `SkewMonoidAlgebra.sum_zero`：sum_zero {N : Type*} [AddCommMonoid N] {f : 
SkewMonoidAlgebra k G} : (f.sum fun _ _ => (0 : N)) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem single_mul_single {a₁ a₂ : G} {b₁ b₂ : k} :
    (single a₁ b₁) * (single a₂ b₂) = single (a₁ * a₂) (b₁ * a₁ • b₂) :=
  (sum_single_index (by simp [zero_mul, single_zero, sum_zero])).trans
    (sum_single_index (by simp [smul_zero, mul_zero, single_zero]))

/-- `single 1` as a `RingHom` -/
/-
**SkewMonoidAlgebra.singleOneRingHom** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebr
a`。
形式化陈述：singleOneRingHom : k ->+* SkewMonoidAlgebra k G where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`single 1` as a `RingHom`
-/
def singleOneRingHom : k →+* SkewMonoidAlgebra k G where
  __ := singleAddHom 1
  map_one' := rfl
  map_mul' x y := by simp [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, singleAddHom_apply,
    single_mul_single, mul_one, one_smul]

/-- If two ring homomorphisms from `SkewMonoidAlgebra k G` are equal on all `single a 1`
and `single 1 b`, then they are equal. -/
/-
**SkewMonoidAlgebra.ringHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：ringHom_ext {f g : SkewMonoidAlgebra k G ->+* k} (h₁ : forall b, f (single
 1 b) = g (single 1 b)) (h_of : forall a, f (single a 1) = g (single a 1)) : f =
 g
参数：h₁ : forall b, f (single 1 b) = g (single 1 b)；h_of : forall a, f (single a 1
) = g (single a 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.single_mul_single`：single_mul_single {a₁ a₂ : G} {b₁ b
₂ : k} : (single a₁ b₁) * (single a₂ b₂) = single (a₁ * a₂) (b₁ * a₁ • b₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RingHom.coe_addMonoidHom_injective`：coe_addMonoidHom_injective : Injecti
ve (fun f : α ->+* β => (f : α ->+ β))
· 使用定理 `SkewMonoidAlgebra.addHom_ext`：addHom_ext {M : Type*} [AddZeroClass M] {f
 g : SkewMonoidAlgebra k G ->+ M} (h : forall a b, f (single a b) = g (single a 
b)) : f = g
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `AddMonoidHom.coe_coe`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [in
st : AddZero M] [inst_1 : AddZero N] [inst_2 : FunLike F M N]   [inst_3 : AddMon
oidHomClas…
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b

--- 原说明 ---
If two ring homomorphisms from `SkewMonoidAlgebra k G` are equal on all `single 
a 1`
and `single 1 b`, then they are equal.
-/
theorem ringHom_ext {f g : SkewMonoidAlgebra k G →+* k} (h₁ : ∀ b, f (single 1 b) = g (single 1 b))
    (h_of : ∀ a, f (single a 1) = g (single a 1)) : f = g :=
  have {a : G} {b₁ b₂ : k} : (single 1 b₁) * (single a b₂) = single a (b₁ * b₂) := by
    simp [single_mul_single, one_mul, one_smul]
  RingHom.coe_addMonoidHom_injective <|
    addHom_ext fun a b ↦ by rw [← mul_one b, ← this, AddMonoidHom.coe_coe f,
      AddMonoidHom.coe_coe g, f.map_mul, g.map_mul, h₁, h_of]

end singleOneRingHom

section MapDomain

variable {α α₂ β F : Type*} [Semiring β] [Monoid α] [Monoid α₂] [FunLike F α α₂]

/-- Like `mapDomain_zero`, but for the `1` we define in this file -/
/-
**SkewMonoidAlgebra.mapDomain_one** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：mapDomain_one [MonoidHomClass F α α₂] (f : F) : (mapDomain f (1 : SkewMono
idAlgebra β α) : SkewMonoidAlgebra β α₂) = (1 : SkewMonoidAlgebra β α₂)
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.mapDomain_single`：mapDomain_single {a : G} {b : k} : m
apDomain f (single a b) = single (f a) b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Like `mapDomain_zero`, but for the `1` we define in this file
-/
theorem mapDomain_one [MonoidHomClass F α α₂] (f : F) :
    (mapDomain f (1 : SkewMonoidAlgebra β α) : SkewMonoidAlgebra β α₂) =
      (1 : SkewMonoidAlgebra β α₂) := by
  simp_rw [one_def, mapDomain_single, map_one]

/-- Like `mapDomain_add`, but for the skewed convolutive multiplication we define in this
  file. This theorem holds assuming that `(hf : ∀ (a : α) (x : β), a • x = (f a) • x)`. -/
/-
**SkewMonoidAlgebra.mapDomain_mul** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：mapDomain_mul [MulSemiringAction α β] [MulSemiringAction α₂ β] [MulHomClas
s F α α₂] {f : F} (x y : SkewMonoidAlgebra β α) (hf : forall (a : α) (x : β), a 
• x = (f a) • x) : mapDomain f (x * y) = mapDomain f x * mapDomain f y
参数：x y : SkewMonoidAlgebra β α；hf : forall (a : α) (x : β), a • x = (f a) • x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.mul_def`：mul_def {f g : SkewMonoidAlgebra k G} : f * g
 = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => single (a₁ * a₂) (b₁ * (a₁ • b₂))
· 使用定理 `SkewMonoidAlgebra.map_sum`：map_sum {N P : Type*} [AddCommMonoid N] [AddC
ommMonoid P] {H : Type*} [FunLike H N P] [AddMonoidHomClass H N P] (h : H) (f : 
SkewMonoidAlgeb…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SkewMonoidAlgebra.mapDomain_single`：mapDomain_single {a : G} {b : k} : m
apDomain f (single a b) = single (f a) b
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `SkewMonoidAlgebra.sum_mapDomain_index`：sum_mapDomain_index {k' : Type*} 
[AddCommMonoid k'] {h : G' -> k -> k'} (h_zero : forall (b : G'), h b 0 = 0) (h_
add : forall (b : G') (m₁ m…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SkewMonoidAlgebra.mapDomain_apply`：∀ {k : Type u_1} {G : Type u_2} [inst
 : AddCommMonoid k] {G' : Type u_3} (f : G → G') (v : SkewMonoidAlgebra k G),   
(SkewMonoidAlgebra.mapD…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `SkewMonoidAlgebra.single_zero`：single_zero (a : G) : (single a 0 : SkewM
onoidAlgebra k G) = 0
· 使用定理 `SkewMonoidAlgebra.sum_zero`：sum_zero {N : Type*} [AddCommMonoid N] {f : 
SkewMonoidAlgebra k G} : (f.sum fun _ _ => (0 : N)) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `SkewMonoidAlgebra.single_add`：single_add (a : G) (b₁ b₂ : k) : single a 
(b₁ + b₂) = single a b₁ + single a b₂
· 使用定理 `SkewMonoidAlgebra.sum_add`：sum_add {S : Type*} [AddCommMonoid S] (p : Sk
ewMonoidAlgebra k G) (f g : G -> k -> S) : (p.sum fun n x => f n x + g n x) = p.
sum f + p.sum g
· 使用定理 `SkewMonoidAlgebra.ext`：ext {p q : SkewMonoidAlgebra k G} : (forall a, co
eff p a = coeff q a) -> p = q
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
Like `mapDomain_add`, but for the skewed convolutive multiplication we define in
 this
  file. This theorem holds assuming that `(hf : ∀ (a : α) (x : β), a • x = (f a)
 • x)`.
-/
theorem mapDomain_mul [MulSemiringAction α β] [MulSemiringAction α₂ β]
    [MulHomClass F α α₂] {f : F} (x y : SkewMonoidAlgebra β α)
    (hf : ∀ (a : α) (x : β), a • x = (f a) • x) :
    mapDomain f (x * y) = mapDomain f x * mapDomain f y := by
  rw [mul_def, map_sum]
  have : (sum x fun a b ↦ sum y fun a₂ b₂ ↦ mapDomain (↑f) (single (a * a₂) (b * a • b₂))) =
      sum (mapDomain (↑f) x) fun a₁ b₁ ↦
        sum (mapDomain (↑f) y) fun a₂ b₂ ↦ single (a₁ * a₂) (b₁ * a₁ • b₂) := by
    simp_rw [mapDomain_single, map_mul]
    rw [sum_mapDomain_index (by simp) (by simp [add_mul, single_add, sum_add])]
    congr
    ext a b c
    rw [sum_mapDomain_index (by simp) (by simp [smul_add, mul_add, single_add])]
    simp_rw [hf]
  convert! this using 4
  rw [map_sum]

/-- If f : G → H is a multiplicative homomorphism between two monoids and
  `∀ (a : G) (x : k), a • x = (f a) • x`, then `mapDomain f` is a ring homomorphism
  between their skew monoid algebras. -/
/-
**SkewMonoidAlgebra.mapDomainRingHom** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebr
a`。
形式化陈述：mapDomainRingHom [MulSemiringAction α β] [MulSemiringAction α₂ β] [MonoidH
omClass F α α₂] {f : F} (hf : forall (a : α) (x : β), a • x = (f a) • x) : SkewM
onoidAlgebra β α ->+* SkewMonoidAlgebra β α₂ where __
参数：hf : forall (a : α) (x : β), a • x = (f a) • x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.mapDomain_one`：mapDomain_one [MonoidHomClass F α α₂] (
f : F) : (mapDomain f (1 : SkewMonoidAlgebra β α) : SkewMonoidAlgebra β α₂) = (1
 : SkewMonoidAlgebra …

--- 原说明 ---
If f : G → H is a multiplicative homomorphism between two monoids and
  `∀ (a : G) (x : k), a • x = (f a) • x`, then `mapDomain f` is a ring homomorph
ism
  between their skew monoid algebras.
-/
def mapDomainRingHom [MulSemiringAction α β] [MulSemiringAction α₂ β]
    [MonoidHomClass F α α₂] {f : F} (hf : ∀ (a : α) (x : β), a • x = (f a) • x) :
    SkewMonoidAlgebra β α →+* SkewMonoidAlgebra β α₂ where
  __ := (mapDomain f : SkewMonoidAlgebra β α →+ SkewMonoidAlgebra β α₂)
  map_one' := mapDomain_one f
  map_mul' x y := mapDomain_mul x y hf

end MapDomain

section of

variable (k G)

variable [Monoid G] [MulSemiringAction G k]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The embedding of a monoid into its skew monoid algebra. -/
/-
**SkewMonoidAlgebra.of** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：of : G ->* SkewMonoidAlgebra k G where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding of a monoid into its skew monoid algebra.
-/
def of : G →* SkewMonoidAlgebra k G where
  toFun a      := single a 1
  map_one'     := rfl
  map_mul' a b := by simp

@[simp]
/-
**SkewMonoidAlgebra.of_apply** 是 Mathlib 中的一个引理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：of_apply (a : G) : (of k G) a = single a 1
参数：a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma of_apply (a : G) : (of k G) a = single a 1 := by
  simp [of, MonoidHom.coe_mk, OneHom.coe_mk]
/-
**SkewMonoidAlgebra.smul_of** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：smul_of (g : G) (r : k) : r • of k G g = single g r
参数：g : G；r : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewMonoidAlgebra.of_apply`：of_apply (a : G) : (of k G) a = single a 1
· 使用定理 `SkewMonoidAlgebra.smul_single`：smul_single {S} [SMulZeroClass S k] (s : 
S) (a : G) (b : k) : s • single a b = single a (s • b)
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem smul_of (g : G) (r : k) : r • of k G g = single g r := by
  rw [of_apply, smul_single, smul_eq_mul, mul_one]
/-
**SkewMonoidAlgebra.of_injective** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：of_injective [Nontrivial k] : Function.Injective (of k G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.single_eq_single_iff`：single_eq_single_iff (a₁ a₂ : α) (b₁ b₂ : 
M) : single a₁ b₁ = single a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0
· 使用引理 `SkewMonoidAlgebra.of_apply`：of_apply (a : G) : (of k G) a = single a 1
-/
theorem of_injective [Nontrivial k] :
    Function.Injective (of k G) := fun a b h ↦ by
  simp_rw [of_apply, ← coeff_inj] at h
  simpa using (Finsupp.single_eq_single_iff _ _ _ _).mp h

/-- If two ring homomorphisms from `SkewMonoidAlgebra k G` are equal on all `single a 1`
and `single 1 b`, then they are equal.

See note [partially-applied ext lemmas]. -/
@[ext high]
/-
**SkewMonoidAlgebra.ringHom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：ringHom_ext' {f g : SkewMonoidAlgebra k G ->+* k} (h₁ : f.comp singleOneRi
ngHom = g.comp singleOneRingHom) (h_of : (f : SkewMonoidAlgebra k G ->* k).comp 
(of k G) = (g : SkewMonoidAlgebra k G ->* k).comp (of k G)) : f = g
参数：h₁ : f.comp singleOneRingHom = g.comp singleOneRingHom；h_of : (f : SkewMonoid
Algebra k G ->* k).comp (of k G) = (g : SkewMonoidAlgebra k G ->* k).comp (of k 
G)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `SkewMonoidAlgebra.ringHom_ext`：ringHom_ext {f g : SkewMonoidAlgebra k G 
->+* k} (h₁ : forall b, f (single 1 b) = g (single 1 b)) (h_of : forall a, f (si
ngle a 1) = g (sing…
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
If two ring homomorphisms from `SkewMonoidAlgebra k G` are equal on all `single 
a 1`
and `single 1 b`, then they are equal.

See note [partially-applied ext lemmas].
-/
theorem ringHom_ext' {f g : SkewMonoidAlgebra k G →+* k}
    (h₁ : f.comp singleOneRingHom = g.comp singleOneRingHom)
    (h_of : (f : SkewMonoidAlgebra k G →* k).comp (of k G) =
      (g : SkewMonoidAlgebra k G →* k).comp (of k G)) : f = g :=
  ringHom_ext (RingHom.congr_fun h₁) (DFunLike.congr_fun h_of)

end of

/-! #### Non-unital, non-associative algebra structure -/

section NonUnitalNonAssocAlgebra

/-
**SkewMonoidAlgebra.liftNC_smul** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：liftNC_smul [MulOneClass G] {R : Type*} [Semiring R] (f : k ->+* R) (g : G
 ->* R) (c : k) (φ : SkewMonoidAlgebra k G) : liftNC (f : k ->+ R) g (c • φ) = f
 c * liftNC (f : k ->+ R) g φ
参数：f : k ->+* R；g : G ->* R；c : k；φ : SkewMonoidAlgebra k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `SkewMonoidAlgebra.addHom_ext'`：addHom_ext' {N : Type*} [AddZeroClass N] 
⦃f g : SkewMonoidAlgebra k G ->+ N⦄ (H : forall x, f.comp (singleAddHom x) = g.c
omp (singleAddHom x…
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.singleAddHom_apply`：∀ {k : Type u_1} {G : Type u_2} [i
nst : AddCommMonoid k] (a : G) (b : k),   (SkewMonoidAlgebra.singleAddHom a) b =
 SkewMonoidAlgebra.single …
· 使用定理 `SkewMonoidAlgebra.smul_single`：smul_single {S} [SMulZeroClass S k] (s : 
S) (a : G) (b : k) : s • single a b = single a (s • b)
· 使用定理 `SkewMonoidAlgebra.liftNC_single`：∀ {k : Type u_1} {G : Type u_2} [inst :
 AddCommMonoid k] {R : Type u_5} [inst_1 : NonUnitalNonAssocSemiring R]   (f : k
 →+ R) (g : G → R) (a…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem liftNC_smul [MulOneClass G] {R : Type*} [Semiring R] (f : k →+* R) (g : G →* R) (c : k)
    (φ : SkewMonoidAlgebra k G) :
    liftNC (f : k →+ R) g (c • φ) = f c * liftNC (f : k →+ R) g φ := by
  suffices this :
    (liftNC ↑f g).comp (smulAddHom k (SkewMonoidAlgebra k G) c) =
      (AddMonoidHom.mulLeft (f c)).comp (liftNC ↑f g) by simpa using congr($this φ)
  refine addHom_ext' fun a => AddMonoidHom.ext fun b => ?_
  simp [smul_single, mul_assoc]

variable (k G) [Monoid G] [MulSemiringAction G k]
/-
**SkewMonoidAlgebra.isScalarTower_self** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlge
bra`。
形式化陈述：isScalarTower_self [IsScalarTower k k k] : IsScalarTower k (SkewMonoidAlge
bra k G) (SkewMonoidAlgebra k G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SkewMonoidAlgebra.sum_smul_index'`：sum_smul_index' {N R : Type*} [AddCom
mMonoid k] [DistribSMul R k] [AddCommMonoid N] {g : SkewMonoidAlgebra k G} {b : 
R} {h : G -> k -> N} (h…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `SkewMonoidAlgebra.single_zero`：single_zero (a : G) : (single a 0 : SkewM
onoidAlgebra k G) = 0
· 使用定理 `SkewMonoidAlgebra.sum_zero`：sum_zero {N : Type*} [AddCommMonoid N] {f : 
SkewMonoidAlgebra k G} : (f.sum fun _ _ => (0 : N)) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
-/
instance isScalarTower_self [IsScalarTower k k k] :
    IsScalarTower k (SkewMonoidAlgebra k G) (SkewMonoidAlgebra k G) :=
  ⟨fun t a b ↦ by
    simp only [smul_eq_mul]
    refine Eq.trans (sum_smul_index' (g := a) (b := t) ?_) ?_ <;>
      simp only [← smul_sum, smul_mul_assoc, ← smul_single,
        zero_mul, imp_true_iff, sum_zero, single_zero]; rfl⟩

end NonUnitalNonAssocAlgebra

end Semiring

section DistribMulActionHom

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N]

/-- `single` as a `DistribMulActionSemiHom`.

See also `lsingle` for the version as a linear map. -/
@[simps]
/-
**SkewMonoidAlgebra.DistribMulActionHom.single** 是 Mathlib 中的一个定义，位于命名空间 `SkewMo
noidAlgebra.DistribMulActionHom`。
形式化陈述：{R : Type u_3} →   {M : Type u_4} →     [inst : Semiring R] →       [inst_
1 : AddCommMonoid M] → [inst_2 : DistribMulAction R M] → {α : Type u_6} → α → M 
→+[R] SkewMonoidAlgebra M α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`single` as a `DistribMulActionSemiHom`.

See also `lsingle` for the version as a linear map.
-/
def DistribMulActionHom.single [DistribMulAction R M] {α : Type*} (a : α) :
    M →+[R] SkewMonoidAlgebra M α where
  __ := singleAddHom a
  map_smul' k m := by simp [singleAddHom, smul_single, MonoidHom.id_apply]
/-
**SkewMonoidAlgebra.distribMulActionHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoi
dAlgebra`。
形式化陈述：distribMulActionHom_ext [DistribMulAction R M] [DistribMulAction R N] {α :
 Type*} {f g : SkewMonoidAlgebra M α ->+[R] N} (h : forall (a : α) (m : M), f (s
ingle a m) = g (single a m)) : f = g
参数：h : forall (a : α) (m : M), f (single a m) = g (single a m)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionHom.toAddMonoidHom_injective`：∀ {M : Type u_1} [inst : M
onoid M] {N : Type u_2} [inst_1 : Monoid N] {φ : M →* N} {A : Type u_4} [inst_2 
: AddMonoid A]   [inst_3 : Distrib…
· 使用定理 `SkewMonoidAlgebra.addHom_ext`：addHom_ext {M : Type*} [AddZeroClass M] {f
 g : SkewMonoidAlgebra k G ->+ M} (h : forall a b, f (single a b) = g (single a 
b)) : f = g
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `DistribMulActionHom.instAddDistribAddActionSemiHomClassCoeAddMonoidHom`：
∀ {M : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] (φ : M →* 
N) (A : Type u_4) [inst_2 : AddMonoid A]   [inst_3 : Distrib…
-/
theorem distribMulActionHom_ext [DistribMulAction R M] [DistribMulAction R N] {α : Type*}
    {f g : SkewMonoidAlgebra M α →+[R] N}
    (h : ∀ (a : α) (m : M), f (single a m) = g (single a m)) : f = g :=
  DistribMulActionHom.toAddMonoidHom_injective <| addHom_ext h

/-- See note [partially-applied ext lemmas]. -/
@[ext]
/-
**SkewMonoidAlgebra.distribMulActionHom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `SkewMono
idAlgebra`。
形式化陈述：distribMulActionHom_ext' [DistribMulAction R M] [DistribMulAction R N] {α 
: Type*} {f g : SkewMonoidAlgebra M α ->+[R] N} (h : forall a : α, f.comp (Distr
ibMulActionHom.single a) = g.comp (DistribMulActionHom.single a)) : f = g
参数：h : forall a : α, f.comp (DistribMulActionHom.single a) = g.comp (DistribMulA
ctionHom.single a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.distribMulActionHom_ext`：distribMulActionHom_ext [Dist
ribMulAction R M] [DistribMulAction R N] {α : Type*} {f g : SkewMonoidAlgebra M 
α ->+[R] N} (h : forall (a : α)…
· 使用定理 `DistribMulActionHom.congr_fun`：∀ {M : Type u_1} [inst : Monoid M] {N : T
ype u_2} [inst_1 : Monoid N] {φ : M →* N} {A : Type u_4} [inst_2 : AddMonoid A] 
  [inst_3 : Distrib…

--- 原说明 ---
See note [partially-applied ext lemmas].
-/
theorem distribMulActionHom_ext' [DistribMulAction R M] [DistribMulAction R N] {α : Type*}
    {f g : SkewMonoidAlgebra M α →+[R] N}
    (h : ∀ a : α, f.comp (DistribMulActionHom.single a) = g.comp (DistribMulActionHom.single a)) :
    f = g :=
  distribMulActionHom_ext fun a ↦ DistribMulActionHom.congr_fun (h a)

variable (R) in
/-- Interpret `single a` as a linear map. -/
/-
**SkewMonoidAlgebra.lsingle** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：lsingle {α : Type*} (a : α) [Module R M] : M ->ₗ[R] (SkewMonoidAlgebra M α
) where __
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret `single a` as a linear map.
-/
def lsingle {α : Type*} (a : α) [Module R M] : M →ₗ[R] (SkewMonoidAlgebra M α) where
  __ := singleAddHom a
  map_smul' _ _ := (smul_single _ _ _).symm
/-
**SkewMonoidAlgebra.lsingle_apply** 是 Mathlib 中的一个引理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：lsingle_apply {α : Type*} (a : α) [Module R M] (m : M) : lsingle R a m = s
ingle a m
参数：a : α；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lsingle_apply {α : Type*} (a : α) [Module R M] (m : M) :
  lsingle R a m = single a m := rfl

/-- Two `R`-linear maps from `SkewMonoidAlgebra M α` which agree on each `single x y`
  agree everywhere. -/
/-
**SkewMonoidAlgebra.lhom_ext** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：lhom_ext {α : Type*} [Module R M] [Module R N] ⦃φ ψ : SkewMonoidAlgebra M 
α ->ₗ[R] N⦄ (h : forall a b, φ (single a b) = ψ (single a b)) : φ = ψ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toAddMonoidHom_injective`：toAddMonoidHom_injective : Function.
Injective (toAddMonoidHom : (M ->ₛₗ[σ] M₃) -> M ->+ M₃)
· 使用定理 `SkewMonoidAlgebra.addHom_ext`：addHom_ext {M : Type*} [AddZeroClass M] {f
 g : SkewMonoidAlgebra k G ->+ M} (h : forall a b, f (single a b) = g (single a 
b)) : f = g

--- 原说明 ---
Two `R`-linear maps from `SkewMonoidAlgebra M α` which agree on each `single x y
`
  agree everywhere.
-/
theorem lhom_ext {α : Type*} [Module R M] [Module R N] ⦃φ ψ : SkewMonoidAlgebra M α →ₗ[R] N⦄
    (h : ∀ a b, φ (single a b) = ψ (single a b)) : φ = ψ :=
  LinearMap.toAddMonoidHom_injective <| addHom_ext h

@[ext high]
/-
**SkewMonoidAlgebra.lhom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：lhom_ext' {α : Type*} [Module R M] [Module R N] ⦃φ ψ : SkewMonoidAlgebra M
 α ->ₗ[R] N⦄ (h : forall a, φ.comp (lsingle R a) = ψ.comp (lsingle R a)) : φ = ψ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.lhom_ext`：lhom_ext {α : Type*} [Module R M] [Module R 
N] ⦃φ ψ : SkewMonoidAlgebra M α ->ₗ[R] N⦄ (h : forall a b, φ (single a b) = ψ (s
ingle a b)) : φ …
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
theorem lhom_ext' {α : Type*} [Module R M] [Module R N] ⦃φ ψ : SkewMonoidAlgebra M α →ₗ[R] N⦄
    (h : ∀ a, φ.comp (lsingle R a) = ψ.comp (lsingle R a)) : φ = ψ :=
  lhom_ext fun a ↦ LinearMap.congr_fun (h a)

variable {A : Type*} [NonUnitalNonAssocSemiring A] [Monoid G] [Semiring k] [MulSemiringAction G k]
open NonUnitalAlgHom

/-- A non-unital `k`-algebra homomorphism from `SkewMonoidAlgebra k G` is uniquely defined by its
values on the functions `single a 1`. -/
/-
**SkewMonoidAlgebra.nonUnitalAlgHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlg
ebra`。
形式化陈述：nonUnitalAlgHom_ext [DistribMulAction k A] {φ₁ φ₂ : SkewMonoidAlgebra k G 
->ₙₐ[k] A} (h : forall x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂
参数：h : forall x, φ₁ (single x 1) = φ₂ (single x 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHom.to_distribMulActionHom_injective`：to_distribMulActionHom
_injective {f g : A ->ₛₙₐ[φ] B} (h : (f : A ->ₑ+[φ] B) = (g : A ->ₑ+[φ] B)) : f 
= g
· 使用定理 `SkewMonoidAlgebra.distribMulActionHom_ext'`：distribMulActionHom_ext' [Di
stribMulAction R M] [DistribMulAction R N] {α : Type*} {f g : SkewMonoidAlgebra 
M α ->+[R] N} (h : forall a : α,…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `NonUnitalAlgHom.instNonUnitalAlgSemiHomClass`：∀ {R : Type u} {S : Type u
₁} [inst : Monoid R] [inst_1 : Monoid S] {φ : R →* S} {A : Type v} {B : Type w} 
  [inst_2 : NonUnitalNonAssocSemir…
· 使用定理 `DistribMulActionHom.ext_ring`：DistribMulActionHom.ext_ring {f g : R ->ₑ+
[σ] N'} (h : f 1 = g 1) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.DistribMulActionHom.single_toFun`：∀ {R : Type u_3} {M 
: Type u_4} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : DistribMulA
ction R M]   {α : Type u_6} (a : α) (a_1…
· 使用定理 `SkewMonoidAlgebra.singleAddHom_apply`：∀ {k : Type u_1} {G : Type u_2} [i
nst : AddCommMonoid k] (a : G) (b : k),   (SkewMonoidAlgebra.singleAddHom a) b =
 SkewMonoidAlgebra.single …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A non-unital `k`-algebra homomorphism from `SkewMonoidAlgebra k G` is uniquely d
efined by its
values on the functions `single a 1`.
-/
theorem nonUnitalAlgHom_ext [DistribMulAction k A] {φ₁ φ₂ : SkewMonoidAlgebra k G →ₙₐ[k] A}
    (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ := by
  apply NonUnitalAlgHom.to_distribMulActionHom_injective
  apply distribMulActionHom_ext'
  intro a
  ext
  simp [singleAddHom_apply, h]

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
/-
**SkewMonoidAlgebra.nonUnitalAlgHom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAl
gebra`。
形式化陈述：nonUnitalAlgHom_ext' [DistribMulAction k A] {φ₁ φ₂ : SkewMonoidAlgebra k G
 ->ₙₐ[k] A} (h : φ₁.toMulHom.comp (of k G).toMulHom = φ₂.toMulHom.comp (of k G).
toMulHom) : φ₁ = φ₂
参数：h : φ₁.toMulHom.comp (of k G).toMulHom = φ₂.toMulHom.comp (of k G).toMulHom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.nonUnitalAlgHom_ext`：nonUnitalAlgHom_ext [DistribMulAc
tion k A] {φ₁ φ₂ : SkewMonoidAlgebra k G ->ₙₐ[k] A} (h : forall x, φ₁ (single x 
1) = φ₂ (single x 1)) : φ₁ …
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
See note [partially-applied ext lemmas].
-/
theorem nonUnitalAlgHom_ext' [DistribMulAction k A] {φ₁ φ₂ : SkewMonoidAlgebra k G →ₙₐ[k] A}
    (h : φ₁.toMulHom.comp (of k G).toMulHom = φ₂.toMulHom.comp (of k G).toMulHom) : φ₁ = φ₂ :=
  nonUnitalAlgHom_ext <| DFunLike.congr_fun h

end DistribMulActionHom

section CommSemiring

variable [Monoid G] [CommSemiring k]
variable {A : Type*} [Semiring A] [Algebra k A]

/-- The instance `Algebra k (SkewMonoidAlgebra A G)` whenever we have `Algebra k A`.
  In particular this provides the instance `Algebra k (SkewMonoidAlgebra k G)`. -/
/-
**SkewMonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SkewMonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The instance `Algebra k (SkewMonoidAlgebra A G)` whenever we have `Algebra k A`.
  In particular this provides the instance `Algebra k (SkewMonoidAlgebra k G)`.
-/
instance [MulSemiringAction G A]
    [SMulCommClass G k A] : Algebra k (SkewMonoidAlgebra A G) where
  algebraMap := singleOneRingHom.comp (algebraMap k A)
  smul_def' r a := by ext; simp [Algebra.smul_def, singleOneRingHom, coeff_single_one_mul]
  commutes' r f := by
    ext
    simp only [singleOneRingHom, singleAddHom, ZeroHom.toFun_eq_coe, ZeroHom.coe_mk, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, coeff_single_one_mul, Algebra.commutes, coeff_mul_single_one,
      smul_algebraMap, RingHom.coe_comp, comp_apply]

@[simp]
/-
**SkewMonoidAlgebra.coe_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`
。
形式化陈述：coe_algebraMap [MulSemiringAction G A] [SMulCommClass G k A] : ⇑(algebraMa
p k (SkewMonoidAlgebra A G)) = single 1 ∘ algebraMap k A
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_algebraMap [MulSemiringAction G A] [SMulCommClass G k A] :
    ⇑(algebraMap k (SkewMonoidAlgebra A G)) = single 1 ∘ algebraMap k A :=
  rfl
/-
**SkewMonoidAlgebra.single_eq_algebraMap_mul_of** 是 Mathlib 中的一个定理，位于命名空间 `SkewM
onoidAlgebra`。
形式化陈述：single_eq_algebraMap_mul_of [MulSemiringAction G k] [SMulCommClass G k k] 
(a : G) (b : k) : single a b = algebraMap k (SkewMonoidAlgebra k G) b * of k G a
参数：a : G；b : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewMonoidAlgebra.of_apply`：of_apply (a : G) : (of k G) a = single a 1
· 使用定理 `SkewMonoidAlgebra.single_mul_single`：single_mul_single {a₁ a₂ : G} {b₁ b
₂ : k} : (single a₁ b₁) * (single a₂ b₂) = single (a₁ * a₂) (b₁ * a₁ • b₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulDistribMulAction.smul_one`：∀ {M : Type u_9} {N : Type u_10} {inst : M
onoid M} {inst_1 : Monoid N} [self : MulDistribMulAction M N] (r : M),   r • 1 =
 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_eq_algebraMap_mul_of [MulSemiringAction G k] [SMulCommClass G k k] (a : G) (b : k) :
    single a b = algebraMap k (SkewMonoidAlgebra k G) b * of k G a := by
  simp [coe_algebraMap, comp_apply, of_apply, single_mul_single, one_mul, smul_one, mul_one]
/-
**SkewMonoidAlgebra.single_algebraMap_eq_algebraMap_mul_of** 是 Mathlib 中的一个定理，位于
命名空间 `SkewMonoidAlgebra`。
形式化陈述：single_algebraMap_eq_algebraMap_mul_of (a : G) (b : k) [MulSemiringAction 
G A] [SMulCommClass G k A] : single a (algebraMap k A b) = algebraMap k (SkewMon
oidAlgebra A G) b * of A G a
参数：a : G；b : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewMonoidAlgebra.of_apply`：of_apply (a : G) : (of k G) a = single a 1
· 使用定理 `SkewMonoidAlgebra.single_mul_single`：single_mul_single {a₁ a₂ : G} {b₁ b
₂ : k} : (single a₁ b₁) * (single a₂ b₂) = single (a₁ * a₂) (b₁ * a₁ • b₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulDistribMulAction.smul_one`：∀ {M : Type u_9} {N : Type u_10} {inst : M
onoid M} {inst_1 : Monoid N} [self : MulDistribMulAction M N] (r : M),   r • 1 =
 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_algebraMap_eq_algebraMap_mul_of (a : G) (b : k) [MulSemiringAction G A]
    [SMulCommClass G k A] :
    single a (algebraMap k A b) = algebraMap k (SkewMonoidAlgebra A G) b * of A G a := by
  simp [coe_algebraMap, comp_apply, of_apply, single_mul_single, one_mul, smul_one, mul_one]

/- Hypotheses needed for `k`-algebra homomorphism from `SkewMonoidAlgebra k G`-/
variable [MulSemiringAction G k] [SMulCommClass G k k]

/-- A `k`-algebra homomorphism from `SkewMonoidAlgebra k G` is uniquely defined by its
values on the functions `single a 1`. -/
/-
**SkewMonoidAlgebra.algHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：algHom_ext ⦃φ₁ φ₂ : AlgHom k (SkewMonoidAlgebra k G) A⦄ (h : forall x, φ₁ 
(single x 1) = φ₂ (single x 1)) : φ₁ = φ₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.toLinearMap_injective`：toLinearMap_injective : Function.Injective
 (toLinearMap : _ -> A ->ₗ[R] B)
· 使用定理 `SkewMonoidAlgebra.lhom_ext'`：lhom_ext' {α : Type*} [Module R M] [Module 
R N] ⦃φ ψ : SkewMonoidAlgebra M α ->ₗ[R] N⦄ (h : forall a, φ.comp (lsingle R a) 
= ψ.comp (lsingle…
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g

--- 原说明 ---
A `k`-algebra homomorphism from `SkewMonoidAlgebra k G` is uniquely defined by i
ts
values on the functions `single a 1`.
-/
theorem algHom_ext ⦃φ₁ φ₂ : AlgHom k (SkewMonoidAlgebra k G) A⦄
    (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
    AlgHom.toLinearMap_injective (lhom_ext' fun a ↦ (LinearMap.ext_ring (h a)))

@[ext high]
/-
**SkewMonoidAlgebra.algHom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：algHom_ext' ⦃φ₁ φ₂ : AlgHom k (SkewMonoidAlgebra k G) A⦄ (h : (φ₁ : SkewMo
noidAlgebra k G ->* A).comp (of k G) = (φ₂ : SkewMonoidAlgebra k G ->* A).comp (
of k G)) : φ₁ = φ₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `SkewMonoidAlgebra.algHom_ext`：algHom_ext ⦃φ₁ φ₂ : AlgHom k (SkewMonoidAl
gebra k G) A⦄ (h : forall x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem algHom_ext' ⦃φ₁ φ₂ : AlgHom k (SkewMonoidAlgebra k G) A⦄
    (h : (φ₁ : SkewMonoidAlgebra k G →* A).comp (of k G) =
      (φ₂ : SkewMonoidAlgebra k G →* A).comp (of k G)) :
    φ₁ = φ₂ := algHom_ext <| DFunLike.congr_fun h

end CommSemiring

end SkewMonoidAlgebra

