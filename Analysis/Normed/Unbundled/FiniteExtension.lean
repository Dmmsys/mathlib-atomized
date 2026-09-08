/-
Copyright (c) 2025 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Analysis.Normed.Unbundled.AlgebraNorm
public import Mathlib.Analysis.Normed.Unbundled.SeminormFromBounded
public import Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace


/-!
# Basis.norm

In this file, we prove [BGR, Lemma 3.2.1./3][bosch-guntzer-remmert] : if `K` is a normed field
with a nonarchimedean power-multiplicative norm and `L/K` is a finite extension, then there exists
at least one power-multiplicative `K`-algebra norm on `L` extending the norm on `K`.

## Main Definitions
* `Basis.norm` : the function sending an element `x : L` to the maximum of the norms of its
  coefficients with respect to the `K`-basis `B` of `L`.

## Main Results
* `norm_mul_le_const_mul_norm` : For any `K`-basis of `L`, `B.norm` is bounded with respect to
  multiplication. That is, `∃ (c : ℝ), c > 0` such that
  ` ∀ (x y : L), B.norm (x * y) ≤ c * B.norm x * B.norm y`.
* `exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional` : if `K` is a normed field with a
  nonarchimedean power-multiplicative norm and `L/K` is a finite extension, then there exists at
  least one power-multiplicative `K`-algebra norm on `L` extending the norm on `K`. This is
  [BGR, Lemma 3.2.1./3].

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

Basis.norm, nonarchimedean
-/

@[expose] public section

noncomputable section

open Finset Module

section Ring

variable {K L : Type*} [NormedField K] [Ring L] [Algebra K L]

namespace Module.Basis

variable {ι : Type*} [Fintype ι] [Nonempty ι] (B : Basis ι K L)

/-- The function sending an element `x : L` to the maximum of the norms of its coefficients
with respect to the `K`-basis `B` of `L`. -/
/-
**Module.Basis.norm** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：norm (x : L) : Real
参数：x : L。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty

--- 原说明 ---
The function sending an element `x : L` to the maximum of the norms of its coeff
icients
with respect to the `K`-basis `B` of `L`.
-/
def norm (x : L) : ℝ :=
  Finset.sup' univ univ_nonempty (fun i : ι ↦ ‖B.repr x i‖)

/-- The norm of a coefficient `x_i` is less than or equal to the norm of `x`. -/
/-
**Module.Basis.norm_repr_le_norm** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：norm_repr_le_norm {x : L} (i : ι) : ‖B.repr x i‖ <= B.norm x
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_sup'`：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
The norm of a coefficient `x_i` is less than or equal to the norm of `x`.
-/
theorem norm_repr_le_norm {x : L} (i : ι) : ‖B.repr x i‖ ≤ B.norm x :=
  Finset.le_sup' (fun i : ι ↦ ‖B.repr x i‖) (mem_univ i)

/-- For any `K`-basis of `L`, we have `B.norm 0 = 0`. -/
/-
**Module.Basis.norm_zero** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : NormedField K] [inst_1 : Ring L] [
inst_2 : Algebra K L] {ι : Type u_3}   [inst_3 : Fintype ι] [inst_4 : Nonempty ι
] (B : Module.Basis ι K L), B.norm 0 = 0
参数：B : Module.Basis ι K L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
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
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Finset.sup'_const`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) (a : α),   (s.sup' H fun x => a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For any `K`-basis of `L`, we have `B.norm 0 = 0`.
-/
protected theorem norm_zero : B.norm 0 = 0 := by
  simp [norm, map_zero, norm_zero]

/-- For any `K`-basis of `L`, and any `x : L`, we have `B.norm (-x) = B.norm x`. -/
/-
**Module.Basis.norm_neg** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : NormedField K] [inst_1 : Ring L] [
inst_2 : Algebra K L] {ι : Type u_3}   [inst_3 : Fintype ι] [inst_4 : Nonempty ι
] (B : Module.Basis ι K L) (x : L), B.norm (-x) = B.norm x
参数：B : Module.Basis ι K L；x : L；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
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
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For any `K`-basis of `L`, and any `x : L`, we have `B.norm (-x) = B.norm x`.
-/
protected theorem norm_neg (x : L) : B.norm (-x) = B.norm x := by
  simp [norm, map_neg, Pi.neg_apply, _root_.norm_neg]

/-- For any `K`-basis of `L`, and any `x : L`, we have `0 ≤ B.norm x`. -/
/-
**Module.Basis.norm_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : NormedField K] [inst_1 : Ring L] [
inst_2 : Algebra K L] {ι : Type u_3}   [inst_3 : Fintype ι] [inst_4 : Nonempty ι
] (B : Module.Basis ι K L) (x : L), 0 ≤ B.norm x
参数：B : Module.Basis ι K L；x : L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
For any `K`-basis of `L`, and any `x : L`, we have `0 ≤ B.norm x`.
-/
protected theorem norm_nonneg (x : L) : 0 ≤ B.norm x := by
  simp only [norm, le_sup'_iff, mem_univ, norm_nonneg, and_self, exists_const]

variable {B}

/-- For any `K`-basis `B` of `L` containing `1`, `B.norm` extends the norm on `K`. -/
/-
**Module.Basis.norm_extends** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：norm_extends {i : ι} (hBi : B i = (1 : L)) (x : K) : B.norm ((algebraMap K
 L) x) = ‖x‖
参数：hBi : B i = (1 : L)；x : K。
该定理/引理给出了一组等式。
继承自：{i : ι} (hBi : B i = (1 : L)) (x : K) : B.norm ((algebraMap K L) x) = ‖x‖。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.repr_algebraMap`：repr_algebraMap {ι : Type*} {B : Basis ι R
 S} {i : ι} (hBi : B i = 1) (r : R) : B.repr (algebraMap R S r) = Finsupp.single
 i r
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.le_sup'_of_le`：∀ {α : Type u_2} {β : Type u_3} [inst : Semilattic
eSup α] {s : Finset β} (f : β → α) {a : α} {b : β} (hb : b ∈ s),   a ≤ f b → a ≤
 s.sup' ⋯ …
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For any `K`-basis `B` of `L` containing `1`, `B.norm` extends the norm on `K`.
-/
theorem norm_extends {i : ι} (hBi : B i = (1 : L)) (x : K) :
    B.norm ((algebraMap K L) x) = ‖x‖ := by
  classical
  simp only [norm, repr_algebraMap hBi, Finsupp.single_apply]
  apply le_antisymm
  · aesop
  · exact le_sup'_of_le _ (mem_univ i) (by simp)

/-- For any `K`-basis of `L`, if the norm on `K` is nonarchimedean, then so is `B.norm`. -/
/-
**Module.Basis.norm_isNonarchimedean** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：norm_isNonarchimedean (hna : IsNonarchimedean (Norm.norm : K -> Real)) : I
sNonarchimedean B.norm
参数：hna : IsNonarchimedean (Norm.norm : K -> Real)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `Finset.exists_mem_eq_sup'`：exists_mem_eq_sup' (f : ι -> α) : exists i, i
 in s ∧ s.sup' H f = f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Finsupp.coe_add`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZeroClass M]
 (f g : ι →₀ M), ⇑(f + g) = ⇑f + ⇑g
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `Module.Basis.norm.eq_1`：∀ {K : Type u_1} {L : Type u_2} [inst : NormedFi
eld K] [inst_1 : Ring L] [inst_2 : Algebra K L] {ι : Type u_3}   [inst_3 : Finty
pe ι] [inst_…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_max_iff`：le_max_iff : a <= max b c ↔ a <= b ∨ a <= c
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Module.Basis.norm_repr_le_norm`：norm_repr_le_norm {x : L} (i : ι) : ‖B.r
epr x i‖ <= B.norm x
· 使用定理 `le_max_of_le_right`：le_max_of_le_right : a <= c -> a <= max b c

--- 原说明 ---
For any `K`-basis of `L`, if the norm on `K` is nonarchimedean, then so is `B.no
rm`.
-/
theorem norm_isNonarchimedean (hna : IsNonarchimedean (Norm.norm : K → ℝ)) :
    IsNonarchimedean B.norm := fun x y ↦ by
  obtain ⟨ixy, _, hixy⟩ := exists_mem_eq_sup' univ_nonempty (fun i ↦ ‖(B.repr (x + y)) i‖)
  have hxy : ‖B.repr (x + y) ixy‖ ≤ max ‖B.repr x ixy‖ ‖B.repr y ixy‖ := by
    rw [map_add, Finsupp.coe_add, Pi.add_apply]; exact hna _ _
  rw [Basis.norm, hixy]
  rcases le_max_iff.mp hxy with (hx | hy)
  · exact le_max_of_le_left (le_trans hx (norm_repr_le_norm B ixy))
  · exact le_max_of_le_right (le_trans hy (norm_repr_le_norm B ixy))

set_option backward.isDefEq.respectTransparency false in
/-- For any `K`-basis of `L`, `B.norm` is bounded with respect to multiplication. That is,
  `∃ (c : ℝ), c > 0` such that ` ∀ (x y : L), B.norm (x * y) ≤ c * B.norm x * B.norm y`. -/
/-
**Module.Basis.norm_mul_le_const_mul_norm** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basi
s`。
形式化陈述：norm_mul_le_const_mul_norm {i : ι} (hBi : B i = (1 : L)) (hna : IsNonarchi
medean (Norm.norm : K -> Real)) : exists (c : Real) (_ : 0 < c), forall x y : L,
 B.norm (x * y) <= c * B.norm x * B.norm y
参数：hBi : B i = (1 : L)；hna : IsNonarchimedean (Norm.norm : K -> Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `instNonemptyProd`：∀ {α : Type u_1} {β : Type u_2} [h1 : Nonempty α] [h2 
: Nonempty β], Nonempty (α × β)
· 使用定理 `Finset.exists_mem_eq_sup'`：exists_mem_eq_sup' (f : ι -> α) : exists i, i
 in s ∧ s.sup' H f = f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Module.Basis.norm_extends`：norm_extends {i : ι} (hBi : B i = (1 : L)) (x
 : K) : B.norm ((algebraMap K L) x) = ‖x‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Finset.le_sup'`：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `map_finsetSum`：∀ {M : Type u_5} {N : Type u_6} [inst : AddCommMonoid M] 
[inst_1 : AddCommMonoid N] {α : Type u_7} {F : Type u_8}   [inst_2 : Fintype α] 
[in…
· 使用定理 `SemilinearEquivClass.toAddEquivClass`：∀ {F : Type u_14} {R : outParam (T
ype u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S} 
  {σ : outParam (R →+* S)}…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
For any `K`-basis of `L`, `B.norm` is bounded with respect to multiplication. Th
at is,
  `∃ (c : ℝ), c > 0` such that ` ∀ (x y : L), B.norm (x * y) ≤ c * B.norm x * B.
norm y`.
-/
theorem norm_mul_le_const_mul_norm {i : ι} (hBi : B i = (1 : L))
    (hna : IsNonarchimedean (Norm.norm : K → ℝ)) :
    ∃ (c : ℝ) (_ : 0 < c), ∀ x y : L, B.norm (x * y) ≤ c * B.norm x * B.norm y := by
  -- The bounding constant `c` will be the maximum of the products `B.norm (B i * B j)`.
  obtain ⟨c, _, hc⟩ := exists_mem_eq_sup' univ_nonempty (fun i : ι × ι ↦ B.norm (B i.1 * B i.2))
  use B.norm (B c.1 * B c.2)
  constructor
  -- ∀ (x y : L), B.norm (x * y) ≤ B.norm (⇑B c.fst * ⇑B c.snd) * B.norm x * B.norm y
  · intro x y
    -- `ixy` is an index for which `‖B.repr (x*y) i‖` is maximum.
    obtain ⟨ixy, _, hixy_def⟩ := exists_mem_eq_sup' univ_nonempty (fun i ↦ ‖(B.repr (x * y)) i‖)
    -- We rewrite the LHS using `ixy`.
    conv_lhs => simp only [Basis.norm]; rw [hixy_def, ← Basis.sum_repr B x, ← Basis.sum_repr B y]
    rw [sum_mul, map_finsetSum]
    simp_rw [smul_mul_assoc, map_smul, mul_sum, map_finsetSum, mul_smul_comm, map_smul]
    have hna' : IsNonarchimedean (NormedField.toMulRingNorm K) := hna
    /- Since the norm is nonarchimedean, the norm of a finite sum is bounded by the maximum of the
          norms of the summands. -/
    obtain ⟨k, -, (hk : ‖∑ i : ι, (B.repr x i • ∑ i_1 : ι,
      B.repr y i_1 • B.repr (B i * B i_1)) ixy‖ ≤
      ‖(B.repr x k • ∑ j : ι, B.repr y j • B.repr (B k * B j)) ixy‖)⟩ :=
      IsNonarchimedean.finset_image_add (map_zero _) (apply_nonneg _) hna'
        (fun i ↦ (B.repr x i • ∑ i_1 : ι, B.repr y i_1 • B.repr (B i * B i_1)) ixy)
        (univ : Finset ι)
    simp only [Finsupp.coe_smul, Finsupp.coe_finsetSum, Pi.smul_apply, Finset.sum_apply,
      smul_eq_mul, norm_mul] at hk ⊢
    apply le_trans hk
    -- We use the above property again.
    obtain ⟨k', hk'⟩ : ∃ (k' : ι),
        ‖∑ j : ι, B.repr y j • B.repr (B k * B j) ixy‖ ≤
          ‖B.repr y k' • B.repr (B k * B k') ixy‖ := by
      obtain ⟨k, hk0, hk⟩ := IsNonarchimedean.finset_image_add (map_zero _) (apply_nonneg _) hna'
        (fun i ↦ B.repr y i • B.repr (B k * B i) ixy) (univ : Finset ι)
      exact ⟨k, hk⟩
    apply le_trans (mul_le_mul_of_nonneg_left hk' (norm_nonneg _))
    -- Now an easy computation leads to the desired conclusion.
    rw [norm_smul, mul_assoc, mul_comm (B.norm (B c.fst * B c.snd)), ← mul_assoc]
    exact mul_le_mul (mul_le_mul (B.norm_repr_le_norm _) (B.norm_repr_le_norm _)
      (norm_nonneg _) (B.norm_nonneg _)) (le_trans (B.norm_repr_le_norm _)
        (hc ▸ Finset.le_sup' (fun i : ι × ι ↦ B.norm (B i.1 * B i.2)) (mem_univ (k, k'))))
      (norm_nonneg _) (mul_nonneg (B.norm_nonneg _) (B.norm_nonneg _))
    -- `B c.1 * B c.2` is positive.
  · have h_pos : (0 : ℝ) < B.norm (B i * B i) := by
      have h1 : (1 : L) = (algebraMap K L) 1 := by rw [map_one]
      rw [hBi, mul_one, h1, Basis.norm_extends hBi]
      simp [norm_one, zero_lt_one]
    exact lt_of_lt_of_le h_pos
      (hc ▸ Finset.le_sup' (fun i : ι × ι ↦ B.norm (B i.1 * B i.2)) (mem_univ (i, i)))

/-- For any `k : K`, `y : L`, we have
  `B.norm ((algebra_map K L) k * y) = B.norm ((algebra_map K L) k) * B.norm y`. -/
/-
**Module.Basis.norm_smul** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：norm_smul {ι : Type*} [Fintype ι] [Nonempty ι] {B : Basis ι K L} {i : ι} (
hBi : B i = (1 : L)) (k : K) (y : L) : B.norm ((algebraMap K L) k * y) = B.norm 
((algebraMap K L) k) * B.norm y
参数：hBi : B i = (1 : L)；k : K；y : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.norm_extends`：norm_extends {i : ι} (hBi : B i = (1 : L)) (x
 : K) : B.norm ((algebraMap K L) x) = ‖x‖
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `Module.Basis.norm.eq_1`：∀ {K : Type u_1} {L : Type u_2} [inst : NormedFi
eld K] [inst_1 : Ring L] [inst_2 : Algebra K L] {ι : Type u_3}   [inst_3 : Finty
pe ι] [inst_…
· 使用引理 `Finset.mul₀_sup'`：mul₀_sup' [PosMulReflectLT G₀] (ha : 0 <= a) (f : ι ->
 G₀) (s : Finset ι) (hs) : a * s.sup' hs f = s.sup' hs fun i => a * f i
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.repr_smul'`：Module.Basis.repr_smul' (i : ι) (r : R) (s : S)
 : B.repr (algebraMap R S r * s) i = r * B.repr s i
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α

--- 原说明 ---
For any `k : K`, `y : L`, we have
  `B.norm ((algebra_map K L) k * y) = B.norm ((algebra_map K L) k) * B.norm y`.
-/
theorem norm_smul {ι : Type*} [Fintype ι] [Nonempty ι] {B : Basis ι K L} {i : ι}
    (hBi : B i = (1 : L)) (k : K) (y : L) :
    B.norm ((algebraMap K L) k * y) = B.norm ((algebraMap K L) k) * B.norm y := by
  rw [norm_extends hBi, Basis.norm, Basis.norm,
    Finset.mul₀_sup' (norm_nonneg _) (fun j : ι ↦ ‖B.repr y j‖) univ univ_nonempty]
  congr with j
  rw [repr_smul', norm_mul]

end Module.Basis

end Ring

section Field

variable {K L : Type*} [NormedField K] [Field L] [Algebra K L]

/-- If `K` is a nonarchimedean normed field `L/K` is a finite extension, then there exists a
power-multiplicative nonarchimedean `K`-algebra norm on `L` extending the norm on `K`. -/
/-
**exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional (hfd : FiniteD
imensional K L) (hna : IsNonarchimedean (norm : K -> Real)) : exists f : Algebra
Norm K L, IsPowMul f ∧ (forall (x : K), f ((algebraMap K L) x) = ‖x‖) ∧ IsNonarc
himedean f
参数：hfd : FiniteDimensional K L；hna : IsNonarchimedean (norm : K -> Real)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearIndepOn.singleton`：LinearIndepOn.singleton (hi : v i != 0) : Linea
rIndepOn R v {i}
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Module.Basis.index_nonempty`：index_nonempty (b : Basis ι R M) [Nontrivia
l M] : Nonempty ι
· 使用定理 `Module.Basis.subset_extend`：subset_extend {s : Set V} (hs : LinearIndepO
n K id s) : s subseteq hs.extend (Set.subset_univ _)
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.coe_extend`：coe_extend (hs : LinearIndepOn K id s) : ⇑(Basi
s.extend hs) = ((↑) : _ -> _)
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Module.Basis.norm_zero`：∀ {K : Type u_1} {L : Type u_2} [inst : NormedFi
eld K] [inst_1 : Ring L] [inst_2 : Algebra K L] {ι : Type u_3}   [inst_3 : Finty
pe ι] [inst_…
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `Module.Basis.norm.eq_1`：∀ {K : Type u_1} {L : Type u_2} [inst : NormedFi
eld K] [inst_1 : Ring L] [inst_2 : Algebra K L] {ι : Type u_3}   [inst_3 : Finty
pe ι] [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Module.Basis.norm_extends`：norm_extends {i : ι} (hBi : B i = (1 : L)) (x
 : K) : B.norm ((algebraMap K L) x) = ‖x‖
· 使用定理 `Module.Basis.norm_isNonarchimedean`：norm_isNonarchimedean (hna : IsNonar
chimedean (Norm.norm : K -> Real)) : IsNonarchimedean B.norm
· 使用定理 `IsNonarchimedean.add_le`：add_le [IsStrictOrderedRing R] {α : Type*} [Add
 α] {f : α -> R} (hf : forall x : α, 0 <= f x) (hna : IsNonarchimedean f) {a b :
 α} : f (a + …
· 使用定理 `Module.Basis.norm_neg`：∀ {K : Type u_1} {L : Type u_2} [inst : NormedFie
ld K] [inst_1 : Ring L] [inst_2 : Algebra K L] {ι : Type u_3}   [inst_3 : Fintyp
e ι] [inst_…
· 使用定理 `Module.Basis.norm_mul_le_const_mul_norm`：norm_mul_le_const_mul_norm {i :
 ι} (hBi : B i = (1 : L)) (hna : IsNonarchimedean (Norm.norm : K -> Real)) : exi
sts (c : Real) (_ : 0 < c), f…
· 使用定理 `Module.Basis.norm_smul`：norm_smul {ι : Type*} [Fintype ι] [Nonempty ι] {
B : Basis ι K L} {i : ι} (hBi : B i = (1 : L)) (k : K) (y : L) : B.norm ((algebr
aMap K L) k …
· 使用定理 `seminormFromBounded_isNonarchimedean`：seminormFromBounded_isNonarchimede
an (f_nonneg : 0 <= f) (f_mul : forall x y : R, f (x * y) <= c * f x * f y) (hna
 : IsNonarchimedean f) : I…
· 使用定理 `seminormFromBounded_one_le`：seminormFromBounded_one_le (f_nonneg : 0 <= 
f) (f_mul : forall x y : R, f (x * y) <= c * f x * f y) : seminormFromBounded' f
 1 <= 1
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
If `K` is a nonarchimedean normed field `L/K` is a finite extension, then there 
exists a
power-multiplicative nonarchimedean `K`-algebra norm on `L` extending the norm o
n `K`.
-/
theorem exists_nonarchimedean_pow_mul_seminorm_of_finiteDimensional (hfd : FiniteDimensional K L)
    (hna : IsNonarchimedean (norm : K → ℝ)) :
    ∃ f : AlgebraNorm K L, IsPowMul f ∧ (∀ (x : K), f ((algebraMap K L) x) = ‖x‖) ∧
      IsNonarchimedean f := by
  -- Choose a basis B = {1, e2,..., en} of the K-vector space L
  have h1 : LinearIndepOn K id ({1} : Set L) := .singleton one_ne_zero
  set ι := { x // x ∈ LinearIndepOn.extend h1 (Set.subset_univ ({1} : Set L)) }
  set B : Basis ι K L := Basis.extend h1
  let hfin : Fintype ι := FiniteDimensional.fintypeBasisIndex B
  have hem : Nonempty ι := B.index_nonempty
  have h1L : (1 : L) ∈ LinearIndepOn.extend h1 _ :=
    Basis.subset_extend _ (Set.mem_singleton (1 : L))
  have hB1 : B ⟨1, h1L⟩ = (1 : L) := by rw [Basis.coe_extend, Subtype.coe_mk]
  -- Define a function g : L → ℝ by setting g (∑ki • ei) = maxᵢ ‖ ki ‖
  set g : L → ℝ := B.norm
  -- g 0 = 0seminormFromBounded
  have hg0 : g 0 = 0 := B.norm_zero
  -- g takes nonnegative values
  have hg_nonneg : ∀ x : L, 0 ≤ g x := fun x ↦ by simp only [g, Basis.norm]; simp
  -- g extends the norm on K
  have hg_ext : ∀ (x : K), g ((algebraMap K L) x) = ‖x‖ := Basis.norm_extends hB1
  -- g is nonarchimedean
  have hg_na : IsNonarchimedean g := Basis.norm_isNonarchimedean hna
  -- g satisfies the triangle inequality
  have hg_add : ∀ a b : L, g (a + b) ≤ g a + g b :=
    fun _ _ ↦ IsNonarchimedean.add_le hg_nonneg hg_na
  -- g (-a) = g a
  have hg_neg : ∀ a : L, g (-a) = g a := B.norm_neg
  -- g is multiplicatively bounded
  obtain ⟨_, _, hg_bdd⟩ := Basis.norm_mul_le_const_mul_norm hB1 hna
  -- g is a K-module norm
  have hg_mul : ∀ (k : K) (y : L), g ((algebraMap K L) k * y) = g ((algebraMap K L) k) * g y :=
    fun k y ↦ Basis.norm_smul hB1 k y
  -- Using BGR Prop. 1.2.1/2, we can smooth g to a ring norm f on L that extends the norm on K.
  set f := seminormFromBounded hg0 hg_nonneg hg_bdd hg_add hg_neg
  have hf_na : IsNonarchimedean f := seminormFromBounded_isNonarchimedean hg_nonneg hg_bdd hg_na
  have hf_1 : f 1 ≤ 1 := seminormFromBounded_one_le hg_nonneg hg_bdd
  have hf_ext : ∀ (x : K), f ((algebraMap K L) x) = ‖x‖ :=
    fun k ↦ hg_ext k ▸ seminormFromBounded_of_mul_apply hg_nonneg hg_bdd (hg_mul k)
  -- Using BGR Prop. 1.3.2/1, we obtain from f a power multiplicative K-algebra norm on L
  -- extending the norm on K.
  set F' := smoothingSeminorm f hf_1 hf_na with hF'
  have hF'_ext : ∀ k : K, F' ((algebraMap K L) k) = ‖k‖ := by
    intro k
    rw [← hf_ext _]
    exact smoothingSeminorm_apply_of_map_mul_eq_mul f hf_1 hf_na
      (seminormFromBounded_of_mul_is_mul hg_nonneg hg_bdd (hg_mul k))
  have hF'_1 : F' 1 = 1 := by
    have h1 : (1 : L) = (algebraMap K L) 1 := by rw [map_one]
    simp only [h1, hF'_ext (1 : K), norm_one]
  have hF'_0 : F' ≠ 0 := DFunLike.ne_iff.mpr ⟨(1 : L), by rw [hF'_1]; exact one_ne_zero⟩
  set F : AlgebraNorm K L :=
    { RingSeminorm.toRingNorm F' hF'_0 with
      smul' := fun k y ↦ by
        have hk : ∀ y : L, f (algebraMap K L k * y) = f (algebraMap K L k) * f y :=
          seminormFromBounded_of_mul_is_mul hg_nonneg hg_bdd (hg_mul k)
        have hfk : ‖k‖ = (smoothingSeminorm f hf_1 hf_na) ((algebraMap K L) k) := by
          rw [← hf_ext k, eq_comm, smoothingSeminorm_apply_of_map_mul_eq_mul f hf_1 hf_na hk]
        simp only [hfk, hF']
        -- TODO: There are missing `simp` lemmas here, that should be able to convert
        -- `((smoothingSeminorm f hf_1 hf_na).toRingNorm ⋯).toRingSeminorm y` to
        -- `(smoothingSeminorm f hf_1 hf_na y)`, after which the `erw` would work as a `rw`.
        erw [← smoothingSeminorm_of_mul f hf_1 hf_na hk y]
        rw [Algebra.smul_def]
        rfl }
  have hF_ext (k : K) : F ((algebraMap K L) k) = ‖k‖ := by
    rw [← hf_ext]
    exact smoothingSeminorm_apply_of_map_mul_eq_mul f hf_1 hf_na
      (seminormFromBounded_of_mul_is_mul hg_nonneg hg_bdd (hg_mul k))
  exact ⟨F, isPowMul_smoothingFun f hf_1, hF_ext, isNonarchimedean_smoothingFun f hf_1 hf_na⟩

end Field

