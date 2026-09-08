/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.AdaptationNote

/-!
# Slash actions

This file defines a class of slash actions, which are families of right actions of a group on an a
additive monoid, parametrized by some index type. This is modeled on the slash action of
`GL (Fin 2) ℝ` on the space of modular forms.

## Notation

Scoped in the `ModularForm` namespace, this file defines

* `f ∣[k] A`: the `k`th slash action by `A` on `f`
-/

@[expose] public section


open Complex UpperHalfPlane ModularGroup

open scoped MatrixGroups

/-- A general version of the slash action of the space of modular forms. This is the same data as a
family of `DistribMulAction Gᵒᵖ α` indexed by `k`. -/
/-
**SlashAction** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → (G : Type u_2) → (α : Type u_3) → [Monoid G] → [AddMonoid α] → 
Type (max (max u_1 u_2) u_3)
参数：G : Type u_2；α : Type u_3；max (max u_1 u_2) u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A general version of the slash action of the space of modular forms. This is the
 same data as a
family of `DistribMulAction Gᵒᵖ α` indexed by `k`.
-/
class SlashAction (β G α : Type*) [Monoid G] [AddMonoid α] where
  map : β → G → α → α
  zero_slash : ∀ (k : β) (g : G), map k g 0 = 0
  slash_one : ∀ (k : β) (a : α), map k 1 a = a
  slash_mul : ∀ (k : β) (g h : G) (a : α), map k (g * h) a = map k h (map k g a)
  add_slash : ∀ (k : β) (g : G) (a b : α), map k g (a + b) = map k g a + map k g b

scoped[ModularForm] notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

open scoped ModularForm

@[simp]
/-
**SlashAction.neg_slash** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SlashAction.neg_slash {β G α : Type*} [Monoid G] [AddGroup α] [SlashAction
 β G α] (k : β) (g : G) (a : α) : (-a) ∣[k] g = -a ∣[k] g
参数：k : β；g : G；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_neg_of_add_eq_zero_left`：∀ {G : Type u_1} [inst : SubtractionMonoid G
] {a b : G}, a + b = 0 → a = -b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SlashAction.add_slash`：∀ {β : Type u_1} {G : Type u_2} {α : Type u_3} {i
nst : Monoid G} {inst_1 : AddMonoid α} [self : SlashAction β G α]   (k : β) (g :
 G) (a b : …
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `SlashAction.zero_slash`：∀ {β : Type u_1} {G : Type u_2} {α : Type u_3} {
inst : Monoid G} {inst_1 : AddMonoid α} [self : SlashAction β G α]   (k : β) (g 
: G), SlashA…
-/
theorem SlashAction.neg_slash {β G α : Type*} [Monoid G] [AddGroup α]
    [SlashAction β G α] (k : β) (g : G) (a : α) : (-a) ∣[k] g = -a ∣[k] g :=
  eq_neg_of_add_eq_zero_left <| by
    rw [← add_slash, neg_add_cancel, zero_slash]

attribute [simp] SlashAction.zero_slash SlashAction.slash_one SlashAction.add_slash
/-
**SlashAction.sum_slash** 是 Mathlib 中的一个定理，位于命名空间 `SlashAction`。
形式化陈述：∀ {β : Type u_1} {G : Type u_2} {α : Type u_3} {ι : Type u_4} [inst : Mono
id G] [inst_1 : AddCommGroup α]   [inst_2 : SlashAction β G α] (k : β) (g : G) {
a : ι → α} {s : Finset ι},   SlashAction.map k g (∑ i ∈ s, a i) = ∑ i ∈ s, Slash
Action.map k g (a i)
参数：k : β；g : G；∑ i ∈ s, a i；a i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SlashAction.zero_slash`：∀ {β : Type u_1} {G : Type u_2} {α : Type u_3} {
inst : Monoid G} {inst_1 : AddMonoid α} [self : SlashAction β G α]   (k : β) (g 
: G), SlashA…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `SlashAction.add_slash`：∀ {β : Type u_1} {G : Type u_2} {α : Type u_3} {i
nst : Monoid G} {inst_1 : AddMonoid α} [self : SlashAction β G α]   (k : β) (g :
 G) (a b : …
-/
@[simp] lemma SlashAction.sum_slash {β G α ι : Type*} [Monoid G] [AddCommGroup α]
    [SlashAction β G α] (k : β) (g : G) {a : ι → α} {s : Finset ι} :
    (∑ i ∈ s, a i) ∣[k] g = ∑ i ∈ s, a i ∣[k] g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i t hi IH => simp [hi, IH]

/-- `SlashAction` induced by a monoid homomorphism. -/
@[instance_reducible]
/-
**monoidHomSlashAction** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：monoidHomSlashAction {β G H α : Type*} [Monoid G] [AddMonoid α] [Monoid H]
 [SlashAction β G α] (h : H ->* G) : SlashAction β H α where map k g
参数：h : H ->* G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SlashAction` induced by a monoid homomorphism.
-/
def monoidHomSlashAction {β G H α : Type*} [Monoid G] [AddMonoid α] [Monoid H]
    [SlashAction β G α] (h : H →* G) : SlashAction β H α where
  map k g := SlashAction.map k (h g)
  zero_slash k g := SlashAction.zero_slash k (h g)
  slash_one k a := by simp only [map_one, SlashAction.slash_one]
  slash_mul k g gg a := by simp only [map_mul, SlashAction.slash_mul]
  add_slash _ g _ _ := SlashAction.add_slash _ (h g) _ _

@[simp]
/-
**SlashAction.slash_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SlashAction.slash_eq_zero_iff {β G α : Type*} [Group G] [AddGroup α] [Slas
hAction β G α] (k : β) (g : G) (a : α) : a ∣[k] g = 0 ↔ a = 0
参数：k : β；g : G；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `SlashAction.slash_one`：∀ {β : Type u_1} {G : Type u_2} {α : Type u_3} {i
nst : Monoid G} {inst_1 : AddMonoid α} [self : SlashAction β G α]   (k : β) (a :
 α), SlashA…
· 使用定理 `SlashAction.zero_slash`：∀ {β : Type u_1} {G : Type u_2} {α : Type u_3} {
inst : Monoid G} {inst_1 : AddMonoid α} [self : SlashAction β G α]   (k : β) (g 
: G), SlashA…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma SlashAction.slash_eq_zero_iff {β G α : Type*} [Group G] [AddGroup α] [SlashAction β G α]
    (k : β) (g : G) (a : α) : a ∣[k] g = 0 ↔ a = 0 := by
  refine ⟨fun h ↦ ?_, by simp +contextual⟩
  apply_fun (· ∣[k] g⁻¹) at h
  simpa [← SlashAction.slash_mul] using h

namespace ModularForm

noncomputable section

variable {k : ℤ} (f : ℍ → ℂ)

section privateSlash

set_option backward.privateInPublic true in
/-- The weight `k` action of `GL (Fin 2) ℝ` on functions `f : ℍ → ℂ`. Invoking this directly is
deprecated; it should always be used via the `SlashAction` instance. -/
/-
**ModularForm.privateSlash** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weight `k` action of `GL (Fin 2) ℝ` on functions `f : ℍ → ℂ`. Invoking this 
directly is
deprecated; it should always be used via the `SlashAction` instance.
-/
private def privateSlash (k : ℤ) (γ : GL (Fin 2) ℝ) (f : ℍ → ℂ) (x : ℍ) : ℂ :=
  σ γ (f (γ • x)) * |γ.det.val| ^ (k - 1) * UpperHalfPlane.denom γ x ^ (-k)

-- Why is `noncomputable` flag needed here, when we're in a noncomputable section already?
-- temporary notation until the instance is built
local notation:100 f " ∣[" k "] " γ:100 => ModularForm.privateSlash k γ f

set_option backward.privateInPublic true in
/-
**ModularForm.slash_mul** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem slash_mul (k : ℤ) (A B : GL (Fin 2) ℝ) (f : ℍ → ℂ) :
    f ∣[k] (A * B) = (f ∣[k] A) ∣[k] B := by
  ext1 τ
  calc σ (A * B) (f ((A * B) • τ)) * |(A * B).det.val| ^ (k - 1) * denom (A * B) τ ^ (-k)
  _ = σ B (σ A (f (A • B • τ))) * (|A.det.val| ^ (k - 1) * |B.det.val| ^ (k - 1)) *
      (((σ B) (denom A ↑(B • τ) ^ (-k))) * denom B τ ^ (-k)) := by
    rw [σ_mul_comm, σ_mul, denom_cocycle_σ, mul_zpow, mul_smul, map_mul, Units.val_mul,
      abs_mul, ofReal_mul, mul_zpow, map_zpow₀]
  _ = σ B (σ A (f (A • B • τ)) * |A.det.val| ^ (k - 1) * (denom A ↑(B • τ) ^ (-k)))
        * |B.det.val| ^ (k - 1) * denom B τ ^ (-k) := by
     rw [map_mul, map_zpow₀, map_mul, map_zpow₀, σ_ofReal]
     ring
  _ = ((f ∣[k] A) ∣[k] B) τ := rfl

set_option backward.privateInPublic true in
/-
**ModularForm.add_slash** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem add_slash (k : ℤ) (A : GL (Fin 2) ℝ) (f g : ℍ → ℂ) :
    (f + g) ∣[k] A = f ∣[k] A + g ∣[k] A := by
  ext1 τ
  simp [privateSlash, add_mul]

set_option backward.privateInPublic true in
/-
**ModularForm.slash_one** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem slash_one (k : ℤ) (f : ℍ → ℂ) : f ∣[k] 1 = f :=
  funext <| by simp [privateSlash, σ, denom]

set_option backward.privateInPublic true in
/-
**ModularForm.zero_slash** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem zero_slash (k : ℤ) (A : GL (Fin 2) ℝ) : (0 : ℍ → ℂ) ∣[k] A = 0 :=
  funext fun _ => by simp [privateSlash]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The weight `k` action of `GL (Fin 2) ℝ` on functions `f : ℍ → ℂ`. -/
/-
**ModularForm.** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weight `k` action of `GL (Fin 2) ℝ` on functions `f : ℍ → ℂ`.
-/
instance : SlashAction ℤ (GL (Fin 2) ℝ) (ℍ → ℂ) where
  map := privateSlash
  zero_slash := zero_slash
  slash_one := slash_one
  slash_mul := slash_mul
  add_slash := add_slash

end privateSlash

/-
**ModularForm.slash_def** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：slash_def (g : GL (Fin 2) Real) : f ∣[k] g = fun τ => σ g (f (g • τ)) * |g
.det.val| ^ (k - 1) * denom g τ ^ (-k)
参数：g : GL (Fin 2) Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem slash_def (g : GL (Fin 2) ℝ) :
    f ∣[k] g = fun τ ↦ σ g (f (g • τ)) * |g.det.val| ^ (k - 1) * denom g τ ^ (-k) :=
  rfl
/-
**ModularForm.slash_apply** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：slash_apply (g : GL (Fin 2) Real) (τ : ℍ) : (f ∣[k] g) τ = σ g (f (g • τ))
 * |g.det.val| ^ (k - 1) * denom g τ ^ (-k)
参数：g : GL (Fin 2) Real；τ : ℍ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem slash_apply (g : GL (Fin 2) ℝ) (τ : ℍ) :
    (f ∣[k] g) τ = σ g (f (g • τ)) * |g.det.val| ^ (k - 1) * denom g τ ^ (-k) :=
  rfl
/-
**ModularForm.smul_slash** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：smul_slash (k : Int) (A : GL (Fin 2) Real) (f : ℍ -> Complex) (c : Complex
) : (c • f) ∣[k] A = σ A c • f ∣[k] A
参数：k : Int；A : GL (Fin 2) Real；f : ℍ -> Complex；c : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `ContinuousAlgEquivClass.toAlgEquivClass`：∀ {F : Type u_1} {R : outParam 
(Type u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemi
ring R}   {inst_1 : Semiring …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_slash (k : ℤ) (A : GL (Fin 2) ℝ) (f : ℍ → ℂ) (c : ℂ) :
    (c • f) ∣[k] A = σ A c • f ∣[k] A := by
  ext τ : 1
  simp only [slash_apply, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
/-
**ModularForm.SLAction** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
形式化陈述：SLAction : SlashAction Int SL(2, Int) (ℍ -> Complex)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance SLAction : SlashAction ℤ SL(2, ℤ) (ℍ → ℂ) :=
  monoidHomSlashAction (Matrix.SpecialLinearGroup.mapGL ℝ)
/-
**ModularForm.SL_slash** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：SL_slash (γ : SL(2, Int)) : f ∣[k] γ = f ∣[k] (γ : GL (Fin 2) Real)
参数：γ : SL(2, Int)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SL_slash (γ : SL(2, ℤ)) : f ∣[k] γ = f ∣[k] (γ : GL (Fin 2) ℝ) :=
  rfl
/-
**ModularForm.SL_slash_def** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：SL_slash_def (γ : SL(2, Int)) : f ∣[k] γ = fun τ => f (γ • τ) * denom γ τ 
^ (-k)
参数：γ : SL(2, Int)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Matrix.SpecialLinearGroup.coeToGL_det`：coeToGL_det (g : SpecialLinearGro
up n R) : Matrix.GeneralLinearGroup.det (g : GL n R) = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem SL_slash_def (γ : SL(2, ℤ)) :
    f ∣[k] γ = fun τ ↦ f (γ • τ) * denom γ τ ^ (-k) := by
  simp [SL_slash, slash_def, σ]
/-
**ModularForm.SL_slash_apply** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：SL_slash_apply (γ : SL(2, Int)) (τ : ℍ) : (f ∣[k] γ) τ = f (γ • τ) * denom
 γ τ ^ (-k)
参数：γ : SL(2, Int)；τ : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Matrix.SpecialLinearGroup.coeToGL_det`：coeToGL_det (g : SpecialLinearGro
up n R) : Matrix.GeneralLinearGroup.det (g : GL n R) = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem SL_slash_apply (γ : SL(2, ℤ)) (τ : ℍ) :
    (f ∣[k] γ) τ = f (γ • τ) * denom γ τ ^ (-k) := by
  simp [SL_slash, slash_def, σ]

@[simp]
/-
**ModularForm.SL_smul_slash** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：SL_smul_slash {α : Type*} [SMul α Complex] [IsScalarTower α Complex Comple
x] (k : Int) (A : SL(2, Int)) (f : ℍ -> Complex) (c : α) : (c • f) ∣[k] A = c • 
f ∣[k] A
参数：k : Int；A : SL(2, Int)；f : ℍ -> Complex；c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModularForm.SL_slash_apply`：SL_slash_apply (γ : SL(2, Int)) (τ : ℍ) : (f
 ∣[k] γ) τ = f (γ • τ) * denom γ τ ^ (-k)
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem SL_smul_slash {α : Type*} [SMul α ℂ] [IsScalarTower α ℂ ℂ]
    (k : ℤ) (A : SL(2, ℤ)) (f : ℍ → ℂ) (c : α) :
    (c • f) ∣[k] A = c • f ∣[k] A := by
  ext τ : 1
  simp [SL_slash_apply, Pi.smul_apply, smul_mul_assoc]
/-
**ModularForm.is_invariant_const** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：is_invariant_const (A : SL(2, Int)) (x : Complex) : Function.const ℍ x ∣[(
0 : Int)] A = Function.const ℍ x
参数：A : SL(2, Int)；x : Complex。
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Matrix.SpecialLinearGroup.coeToGL_det`：coeToGL_det (g : SpecialLinearGro
up n R) : Matrix.GeneralLinearGroup.det (g : GL n R) = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem is_invariant_const (A : SL(2, ℤ)) (x : ℂ) :
    Function.const ℍ x ∣[(0 : ℤ)] A = Function.const ℍ x := by
  funext
  simp [SL_slash, slash_def, σ, zero_lt_one]

/-- The constant function 1 is invariant under any element of `SL(2, ℤ)`. -/
/-
**ModularForm.is_invariant_one** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：is_invariant_one (A : SL(2, Int)) : (1 : ℍ -> Complex) ∣[(0 : Int)] A = (1
 : ℍ -> Complex)
参数：A : SL(2, Int)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModularForm.is_invariant_const`：is_invariant_const (A : SL(2, Int)) (x :
 Complex) : Function.const ℍ x ∣[(0 : Int)] A = Function.const ℍ x

--- 原说明 ---
The constant function 1 is invariant under any element of `SL(2, ℤ)`.
-/
theorem is_invariant_one (A : SL(2, ℤ)) : (1 : ℍ → ℂ) ∣[(0 : ℤ)] A = (1 : ℍ → ℂ) :=
  is_invariant_const _ _

/-- Variant of `is_invariant_one` with the left-hand side in simp normal form. -/
@[simp]
/-
**ModularForm.is_invariant_one'** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：is_invariant_one' (A : SL(2, Int)) : (1 : ℍ -> Complex) ∣[(0 : Int)] (A : 
GL (Fin 2) Real) = 1
参数：A : SL(2, Int)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModularForm.is_invariant_one`：is_invariant_one (A : SL(2, Int)) : (1 : ℍ
 -> Complex) ∣[(0 : Int)] A = (1 : ℍ -> Complex)

--- 原说明 ---
Variant of `is_invariant_one` with the left-hand side in simp normal form.
-/
theorem is_invariant_one' (A : SL(2, ℤ)) : (1 : ℍ → ℂ) ∣[(0 : ℤ)] (A : GL (Fin 2) ℝ) = 1 := by
  simpa using! is_invariant_one A

/-- A function `f : ℍ → ℂ` is slash-invariant, of weight `k ∈ ℤ` and level `Γ`,
  if for every matrix `γ ∈ Γ` we have `f(γ • z)= (c*z+d)^k f(z)` where `γ= ![![a, b], ![c, d]]`,
  and it acts on `ℍ` via Möbius transformations. -/
/-
**ModularForm.slash_action_eq'_iff** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：∀ (k : ℤ) (f : UpperHalfPlane → ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) 
ℤ) (z : UpperHalfPlane),   SlashAction.map k γ f z = f z ↔ f (γ • z) = (↑(↑γ 1 0
) * ↑z + ↑(↑γ 1 1)) ^ k * f z
参数：k : ℤ；f : UpperHalfPlane → ℂ；γ : Matrix.SpecialLinearGroup (Fin 2) ℤ；z : Uppe
rHalfPlane；γ • z；↑(↑γ 1 0) * ↑z + ↑(↑γ 1 1)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModularForm.SL_slash_apply`：SL_slash_apply (γ : SL(2, Int)) (τ : ℍ) : (f
 ∣[k] γ) τ = f (γ • τ) * denom γ τ ^ (-k)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `inv_mul_eq_iff_eq_mul₀`：inv_mul_eq_iff_eq_mul₀ (ha : a != 0) : a⁻¹ * b =
 c ↔ b = a * c
· 使用定理 `zpow_ne_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : 
ℤ), a ≠ 0 → a ^ n ≠ 0
· 使用定理 `UpperHalfPlane.denom_ne_zero`：denom_ne_zero (g : GL (Fin 2) Real) (z : ℍ
) : denom g z != 0

--- 原说明 ---
A function `f : ℍ → ℂ` is slash-invariant, of weight `k ∈ ℤ` and level `Γ`,
  if for every matrix `γ ∈ Γ` we have `f(γ • z)= (c*z+d)^k f(z)` where `γ= ![![a
, b], ![c, d]]`,
  and it acts on `ℍ` via Möbius transformations.
-/
theorem slash_action_eq'_iff (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) (z : ℍ) :
    (f ∣[k] γ) z = f z ↔ f (γ • z) = ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) ^ k * f z := by
  simp only [SL_slash_apply]
  convert! inv_mul_eq_iff_eq_mul₀ (G₀ := ℂ) _ using 2
  · simp only [mul_comm (f _), denom, zpow_neg]
    rfl
  · exact zpow_ne_zero k (denom_ne_zero γ z)
/-
**ModularForm.mul_slash** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：mul_slash (k1 k2 : Int) (A : GL (Fin 2) Real) (f g : ℍ -> Complex) : (f * 
g) ∣[k1 + k2] A = |(A.det : Real)| • (f ∣[k1] A * g ∣[k2] A)
参数：k1 k2 : Int；A : GL (Fin 2) Real；f g : ℍ -> Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `ContinuousAlgEquivClass.toAlgEquivClass`：∀ {F : Type u_1} {R : outParam 
(Type u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemi
ring R}   {inst_1 : Semiring …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用引理 `zpow_add₀`：zpow_add₀ (ha : a != 0) (m n : Int) : a ^ (m + n) = a ^ m * a
 ^ n
· 使用定理 `UpperHalfPlane.denom_ne_zero`：denom_ne_zero (g : GL (Fin 2) Real) (z : ℍ
) : denom g z != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ofReal_ne_zero`：ofReal_ne_zero {z : Real} : (z : Complex) != 0 ↔
 z != 0
· 使用定理 `abs_ne_zero`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder 
α] [AddLeftMono α] {a : α} [AddRightMono α], |a| ≠ 0 ↔ a ≠ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Invertible.toNeZero`：∀ {α : Type u} [inst : MulZeroOneClass α] [Nontrivi
al α] (a : α) [Invertible a], NeZero a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `zpow_one_add₀`：zpow_one_add₀ (h : a != 0) (i : Int) : a ^ (1 + i) = a * 
a ^ i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf'`：∀ {R : Type u_1} [inst : CommSemiri
ng R] {a a' b : R},   a = a' → ∀ {e : ℕ}, Nat.rawCast 1 = e → a' ^ e * Nat.rawCa
st 1 = b → a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
（共 61 条，此处仅展示前 30 条）
-/
theorem mul_slash (k1 k2 : ℤ) (A : GL (Fin 2) ℝ) (f g : ℍ → ℂ) :
    (f * g) ∣[k1 + k2] A = |(A.det : ℝ)| • (f ∣[k1] A * g ∣[k2] A) := by
  ext1 x
  simp only [slash_apply, Pi.mul_apply, Pi.smul_apply, real_smul, map_mul, neg_add,
    zpow_add₀ (denom_ne_zero _ x)]
  set d := (↑|A.det.val| : ℂ)
  have h1 : d ^ (k1 + k2 - 1) = d * d ^ (k1 - 1) * d ^ (k2 - 1) := by
    have : d ≠ 0 := ofReal_ne_zero.mpr <| abs_ne_zero.mpr <| NeZero.ne _
    rw [← zpow_one_add₀ this, ← zpow_add₀ this]
    ring_nf
  rw [h1]
  ring
/-
**ModularForm.mul_slash_SL2** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：mul_slash_SL2 (k1 k2 : Int) (A : SL(2, Int)) (f g : ℍ -> Complex) : (f * g
) ∣[k1 + k2] A = f ∣[k1] A * g ∣[k2] A
参数：k1 k2 : Int；A : SL(2, Int)；f g : ℍ -> Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModularForm.mul_slash`：mul_slash (k1 k2 : Int) (A : GL (Fin 2) Real) (f 
g : ℍ -> Complex) : (f * g) ∣[k1 + k2] A = |(A.det : Real)| • (f ∣[k1] A * g ∣[k
2] A)
· 使用定理 `Matrix.SpecialLinearGroup.coeToGL_det`：coeToGL_det (g : SpecialLinearGro
up n R) : Matrix.GeneralLinearGroup.det (g : GL n R) = 1
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_slash_SL2 (k1 k2 : ℤ) (A : SL(2, ℤ)) (f g : ℍ → ℂ) :
    (f * g) ∣[k1 + k2] A = f ∣[k1] A * g ∣[k2] A := by
  simp [SL_slash, mul_slash]
/-
**ModularForm.div_slash_SL2** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：div_slash_SL2 (k1 k2 : Int) (A : SL(2, Int)) (f g : ℍ -> Complex) : (f / g
) ∣[k1 - k2] A = f ∣[k1] A / g ∣[k2] A
参数：k1 k2 : Int；A : SL(2, Int)；f g : ℍ -> Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ModularForm.SL_slash_apply`：SL_slash_apply (γ : SL(2, Int)) (τ : ℍ) : (f
 ∣[k] γ) τ = f (γ • τ) * denom γ τ ^ (-k)
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用引理 `zpow_sub₀`：zpow_sub₀ (ha : a != 0) (m n : Int) : a ^ (m - n) = a ^ m / a
 ^ n
· 使用定理 `UpperHalfPlane.denom_ne_zero`：denom_ne_zero (g : GL (Fin 2) Real) (z : ℍ
) : denom g z != 0
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
-/
theorem div_slash_SL2 (k1 k2 : ℤ) (A : SL(2, ℤ)) (f g : ℍ → ℂ) :
    (f / g) ∣[k1 - k2] A = f ∣[k1] A / g ∣[k2] A := by
  ext τ
  simp [SL_slash_apply, zpow_sub₀ (denom_ne_zero A τ)]
  grind

open Finset
/-
**ModularForm.prod_slash_sum_weights** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：prod_slash_sum_weights {ι : Type*} {k : ι -> Int} {g : GL (Fin 2) Real} {f
 : ι -> ℍ -> Complex} {s : Finset ι} : (∏ i in s, f i) ∣[∑ i in s, k i] g = |g.d
et.val| ^ (#s - 1 : Int) • (∏ i in s, f i ∣[k i] g)
参数：Fin 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `ContinuousAlgEquivClass.toAlgEquivClass`：∀ {F : Type u_1} {R : outParam 
(Type u_2)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemi
ring R}   {inst_1 : Semiring …
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
（共 52 条，此处仅展示前 30 条）
-/
lemma prod_slash_sum_weights {ι : Type*} {k : ι → ℤ} {g : GL (Fin 2) ℝ} {f : ι → ℍ → ℂ}
    {s : Finset ι} :
    (∏ i ∈ s, f i) ∣[∑ i ∈ s, k i] g = |g.det.val| ^ (#s - 1 : ℤ) • (∏ i ∈ s, f i ∣[k i] g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty, prod_empty, Matrix.GeneralLinearGroup.val_det_apply, card_empty,
      CharP.cast_eq_zero, zero_sub, Int.reduceNeg, zpow_neg, zpow_one]
    ext _
    simp [slash_apply]
  | insert i t hi IH =>
    rcases t.eq_empty_or_nonempty with rfl | ht
    · simp
    simp only [prod_insert hi, card_insert_of_notMem hi, Nat.cast_succ, add_sub_cancel_right,
    show ∑ i ∈ insert i t, k i = (k i) + ∑ i ∈ t, k i by grind, mul_slash, IH, mul_smul_comm,
      ← mul_smul]
    congr 1
    nth_rw 2 [show (#t : ℤ) = 1 + (#t - 1) by grind]
    rw [zpow_add', zpow_one]
    left
    exact abs_ne_zero.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)
/-
**ModularForm.prod_slash** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：prod_slash {ι : Type*} {k : Int} {g : GL (Fin 2) Real} {f : ι -> ℍ -> Comp
lex} {s : Finset ι} : (∏ i in s, f i) ∣[k * #s] g = |g.det.val| ^ (#s - 1 : Int)
 • (∏ i in s, f i ∣[k] g)
参数：Fin 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul'`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (a : α) (n :
 ℕ), n • a = a * ↑n
· 使用引理 `ModularForm.prod_slash_sum_weights`：prod_slash_sum_weights {ι : Type*} {
k : ι -> Int} {g : GL (Fin 2) Real} {f : ι -> ℍ -> Complex} {s : Finset ι} : (∏ 
i in s, f i) ∣[∑ i in s,…
-/
lemma prod_slash {ι : Type*} {k : ℤ} {g : GL (Fin 2) ℝ} {f : ι → ℍ → ℂ}
    {s : Finset ι} :
    (∏ i ∈ s, f i) ∣[k * #s] g = |g.det.val| ^ (#s - 1 : ℤ) • (∏ i ∈ s, f i ∣[k] g) := by
  have : k * (#s) = ∑ i ∈ s, k := by
    rw [Finset.sum_const, nsmul_eq_mul']
  rw [this]
  exact prod_slash_sum_weights

@[deprecated prod_slash (since := "2026-01-22")]
/-
**ModularForm.prod_fintype_slash** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：prod_fintype_slash {ι : Type*} [Fintype ι] [Nonempty ι] {k : Int} {g : GL 
(Fin 2) Real} {f : ι -> ℍ -> Complex} : (∏ i, f i) ∣[k * Fintype.card ι] g = |g.
det.val| ^ (Fintype.card ι - 1) • (∏ i, f i ∣[k] g)
参数：Fin 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `Nat.cast_pred`：∀ {R : Type u} [inst : AddGroupWithOne R] {n : ℕ}, 0 < n 
→ ↑(n - 1) = ↑n - 1
· 使用引理 `ModularForm.prod_slash`：prod_slash {ι : Type*} {k : Int} {g : GL (Fin 2)
 Real} {f : ι -> ℍ -> Complex} {s : Finset ι} : (∏ i in s, f i) ∣[k * #s] g = |g
.det.val| ^ …
-/
lemma prod_fintype_slash {ι : Type*} [Fintype ι] [Nonempty ι] {k : ℤ} {g : GL (Fin 2) ℝ}
    {f : ι → ℍ → ℂ} : (∏ i, f i) ∣[k * Fintype.card ι] g =
      |g.det.val| ^ (Fintype.card ι - 1) • (∏ i, f i ∣[k] g) := by
  have : 0 < Fintype.card ι := Fintype.card_pos
  simpa [← zpow_natCast, this] using ModularForm.prod_slash (s := (.univ : Finset ι))

end

end ModularForm

