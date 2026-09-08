/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Data.Finset.SMulAntidiagonal

/-!
# Scalar multiplication by (additive) monoid rings on formal functions.

Given sets `G` and `P`, with a left-cancellative scalar-multiplication (or vector-addition) of `G`
on `P`, together with a module `V` over a semiring `R`, we define a convolution action of the monoid
algebra `R[G]` on the set of functions `P → V`.

-/

@[expose] public section

noncomputable section

variable {G P R V : Type*}

namespace MonoidAlgebra

set_option backward.isDefEq.respectTransparency.types false in
@[to_additive]
/-
**MonoidAlgebra.mem_smulAntidiagonal_of_group** 是 Mathlib 中的一个定理，位于命名空间 `MonoidA
lgebra`。
形式化陈述：mem_smulAntidiagonal_of_group [Group G] [MulAction G P] [Semiring R] [Zero
 V] (f : R[G]) (x : P -> V) (p : P) (gh : G × P) : gh in Finset.SMulAntidiagonal
 p (Set.SMulAntidiagonal.finite_of_finite_fst f.coeff.support.finite_toSet x.sup
port p) ↔ f.coeff gh.1 != 0 ∧ x gh.2 != 0 ∧ gh.2 = gh.1⁻¹ • p
参数：f : R[G]；x : P -> V；p : P；gh : G × P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.SMulAntidiagonal.finite_of_finite_fst`：finite_of_finite_fst [IsLeftC
ancelSMul G P] (hs : s.Finite) (t) (p : P) : (s.smulAntidiagonal t p).Finite
· 使用定理 `instIsLeftCancelSMul`：∀ (G : Type u_9) (P : Type u_10) [inst : Group G] 
[inst_1 : MulAction G P], IsLeftCancelSMul G P
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_smulAntidiagonal`：mem_smulAntidiagonal {s : Set G} {t : Set P
} (a : P) (h : (s.smulAntidiagonal t a).Finite) {x : G × P} : x in SMulAntidiago
nal a h ↔ x.1 in …
· 使用定理 `eq_inv_smul_iff`：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_
1 : MulAction G α] {g : G} {a b : α}, a = g⁻¹ • b ↔ g • a = b
· 使用定理 `Function.mem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] {f
 : ι → M} {x : ι}, x ∈ Function.support f ↔ f x ≠ 0
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_smulAntidiagonal_of_group [Group G] [MulAction G P] [Semiring R] [Zero V]
    (f : R[G]) (x : P → V) (p : P) (gh : G × P) :
    gh ∈ Finset.SMulAntidiagonal p
      (Set.SMulAntidiagonal.finite_of_finite_fst f.coeff.support.finite_toSet x.support p) ↔
      f.coeff gh.1 ≠ 0 ∧ x gh.2 ≠ 0 ∧ gh.2 = gh.1⁻¹ • p := by
  rw [Finset.mem_smulAntidiagonal, eq_inv_smul_iff, Function.mem_support, Finset.mem_coe,
    Finsupp.mem_support_iff]

/-- A convolution-type scalar multiplication of the monoid algebra on the set of formal
functions. -/
@[to_additive (dont_translate := R) /-- A convolution-type scalar multiplication of the additive
monoid algebra on the set of formal functions. -/]
/-
**MonoidAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `MonoidAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance [SMul G P] [IsLeftCancelSMul G P] [Semiring R] [AddCommMonoid V]
    [SMulWithZero R V] :
    SMul (R[G]) (P → V) where
  smul f x p := ∑ gh ∈ Finset.SMulAntidiagonal p
    (Set.SMulAntidiagonal.finite_of_finite_fst f.coeff.support.finite_toSet x.support p),
      f.coeff gh.1 • x gh.2

@[to_additive (dont_translate := R) smul_eq]
/-
**MonoidAlgebra.smul_eq** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：smul_eq [SMul G P] [IsLeftCancelSMul G P] [Semiring R] [AddCommMonoid V] [
SMulWithZero R V] (f : R[G]) (x : P -> V) (p : P) (hp : ((f.coeff.support : Set 
G).smulAntidiagonal (Function.support x) p).Finite
参数：f : R[G]；x : P -> V；p : P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_eq [SMul G P] [IsLeftCancelSMul G P] [Semiring R] [AddCommMonoid V] [SMulWithZero R V]
    (f : R[G]) (x : P → V) (p : P)
    (hp : ((f.coeff.support : Set G).smulAntidiagonal (Function.support x) p).Finite :=
      Set.SMulAntidiagonal.finite_of_finite_fst f.coeff.support.finite_toSet x.support p) :
    (f • x) p = ∑ gh ∈ Finset.SMulAntidiagonal p hp, f.coeff gh.1 • x gh.2 :=
  rfl

@[to_additive (dont_translate := R) smul_apply_addAction]
/-
**MonoidAlgebra.smul_apply_mulAction** 是 Mathlib 中的一个定理，位于命名空间 `MonoidAlgebra`。
形式化陈述：smul_apply_mulAction [Group G] [MulAction G P] [Semiring R] [AddCommMonoid
 V] [SMulWithZero R V] (f : MonoidAlgebra R G) (x : P -> V) (p : P) : (f • x) p 
= ∑ i in f.coeff.support, (f.coeff i) • x (i⁻¹ • p)
参数：f : MonoidAlgebra R G；x : P -> V；p : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.SMulAntidiagonal.finite_of_finite_fst`：finite_of_finite_fst [IsLeftC
ancelSMul G P] (hs : s.Finite) (t) (p : P) : (s.smulAntidiagonal t p).Finite
· 使用定理 `instIsLeftCancelSMul`：∀ (G : Type u_9) (P : Type u_10) [inst : Group G] 
[inst_1 : MulAction G P], IsLeftCancelSMul G P
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MonoidAlgebra.mem_smulAntidiagonal_of_group`：mem_smulAntidiagonal_of_gro
up [Group G] [MulAction G P] [Semiring R] [Zero V] (f : R[G]) (x : P -> V) (p : 
P) (gh : G × P) : gh in Finset.SM…
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `MonoidAlgebra.smul_eq`：smul_eq [SMul G P] [IsLeftCancelSMul G P] [Semiri
ng R] [AddCommMonoid V] [SMulWithZero R V] (f : R[G]) (x : P -> V) (p : P) (hp :
 ((f.coeff.…
· 使用定理 `Finset.sum_of_injOn`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [ins
t : AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (e 
: ι → κ),…
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem smul_apply_mulAction [Group G] [MulAction G P] [Semiring R] [AddCommMonoid V]
    [SMulWithZero R V] (f : MonoidAlgebra R G) (x : P → V) (p : P) :
    (f • x) p = ∑ i ∈ f.coeff.support, (f.coeff i) • x (i⁻¹ • p) := by
  have hp : ((f.coeff.support : Set G).smulAntidiagonal (Function.support x) p).Finite :=
    Set.SMulAntidiagonal.finite_of_finite_fst f.coeff.support.finite_toSet x.support p
  set s : Set (G × P) := ↑(Finset.SMulAntidiagonal p hp)
  have h₁ : s.InjOn Prod.fst := fun _ h₁ _ h₂ h ↦ by
    rw [Finset.mem_coe, mem_smulAntidiagonal_of_group] at h₁ h₂
    aesop
  have h₂ : s.MapsTo Prod.fst ↑f.coeff.support := fun g hg ↦ by aesop
  have h₃ (g : G) (hg : g ∈ f.coeff.support) (hgn : g ∉ Prod.fst '' s) :
      f.coeff g • x (g⁻¹ • p) = 0 := by
    obtain (h | h) : f.coeff g = 0 ∨ ∀ q, ¬ x q = 0 → ¬g • q = p := by aesop
    · simp [h]
    · have := h (g⁻¹ • p)
      aesop
  rw [smul_eq, Finset.sum_of_injOn Prod.fst h₁ h₂ h₃]
  aesop

end MonoidAlgebra

