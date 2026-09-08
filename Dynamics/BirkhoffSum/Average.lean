/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Lua Viana Reis, Oliver Butterley
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Basic
public import Mathlib.Algebra.Module.Basic

/-!
# Birkhoff average

In this file we define `birkhoffAverage f g n x` to be
$$
\frac{1}{n}\sum_{k=0}^{n-1}g(f^{[k]}(x)),
$$
where `f : α → α` is a self-map on some type `α`,
`g : α → M` is a function from `α` to a module over a division semiring `R`,
and `R` is used to formalize division by `n` as `(n : R)⁻¹ • _`.

While we need an auxiliary division semiring `R` to define `birkhoffAverage`,
the definition does not depend on the choice of `R`,
see `birkhoffAverage_congr_ring`.

-/

@[expose] public section

open Finset

section birkhoffAverage

variable (R : Type*) {α M : Type*} [DivisionSemiring R] [AddCommMonoid M] [Module R M]

/-- The average value of `g` on the first `n` points of the orbit of `x` under `f`,
i.e. the Birkhoff sum `∑ k ∈ Finset.range n, g (f^[k] x)` divided by `n`.

This average appears in many ergodic theorems
which say that `(birkhoffAverage R f g · x)`
converges to the "space average" `⨍ x, g x ∂μ` as `n → ∞`.

We use an auxiliary `[DivisionSemiring R]` to define division by `n`.
However, the definition does not depend on the choice of `R`,
see `birkhoffAverage_congr_ring`. -/
/-
**birkhoffAverage** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：birkhoffAverage (f : α -> α) (g : α -> M) (n : Nat) (x : α) : M
参数：f : α -> α；g : α -> M；n : Nat；x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The average value of `g` on the first `n` points of the orbit of `x` under `f`,
i.e. the Birkhoff sum `∑ k ∈ Finset.range n, g (f^[k] x)` divided by `n`.

This average appears in many ergodic theorems
which say that `(birkhoffAverage R f g · x)`
converges to the "space average" `⨍ x, g x ∂μ` as `n → ∞`.

We use an auxiliary `[DivisionSemiring R]` to define division by `n`.
However, the definition does not depend on the choice of `R`,
see `birkhoffAverage_congr_ring`.
-/
def birkhoffAverage (f : α → α) (g : α → M) (n : ℕ) (x : α) : M := (n : R)⁻¹ • birkhoffSum f g n x
/-
**birkhoffAverage_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：birkhoffAverage_zero (f : α -> α) (g : α -> M) (x : α) : birkhoffAverage R
 f g 0 x = 0
参数：f : α -> α；g : α -> M；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `birkhoffSum_zero'`：birkhoffSum_zero' (f : α -> α) (g : α -> M) : birkhof
fSum f g 0 = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem birkhoffAverage_zero (f : α → α) (g : α → M) (x : α) :
    birkhoffAverage R f g 0 x = 0 := by simp [birkhoffAverage]
/-
**birkhoffAverage_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (R : Type u_1) {α : Type u_2} {M : Type u_3} [inst : DivisionSemiring R]
 [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (f : α → α) (g : α → 
M), birkhoffAverage R f g 0 = 0
参数：R : Type u_1；f : α → α；g : α → M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `birkhoffAverage_zero`：birkhoffAverage_zero (f : α -> α) (g : α -> M) (x 
: α) : birkhoffAverage R f g 0 x = 0
-/
@[simp] theorem birkhoffAverage_zero' (f : α → α) (g : α → M) : birkhoffAverage R f g 0 = 0 :=
  funext <| birkhoffAverage_zero _ _ _
/-
**birkhoffAverage_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：birkhoffAverage_one (f : α -> α) (g : α -> M) (x : α) : birkhoffAverage R 
f g 1 x = g x
参数：f : α -> α；g : α -> M；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `birkhoffSum_one'`：birkhoffSum_one' (f : α -> α) (g : α -> M) : birkhoffS
um f g 1 = g
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem birkhoffAverage_one (f : α → α) (g : α → M) (x : α) :
    birkhoffAverage R f g 1 x = g x := by simp [birkhoffAverage]

@[simp]
/-
**birkhoffAverage_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：birkhoffAverage_one' (f : α -> α) (g : α -> M) : birkhoffAverage R f g 1 =
 g
参数：f : α -> α；g : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `birkhoffAverage_one`：birkhoffAverage_one (f : α -> α) (g : α -> M) (x : 
α) : birkhoffAverage R f g 1 x = g x
-/
theorem birkhoffAverage_one' (f : α → α) (g : α → M) : birkhoffAverage R f g 1 = g :=
  funext <| birkhoffAverage_one R f g
/-
**map_birkhoffAverage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_birkhoffAverage (S : Type*) {F N : Type*} [DivisionSemiring S] [AddCom
mMonoid N] [Module S N] [FunLike F M N] [AddMonoidHomClass F M N] (g' : F) (f : 
α -> α) (g : α -> M) (n : Nat) (x : α) : g' (birkhoffAverage R f g n x) = birkho
ffAverage S f (g' ∘ g) n x
参数：S : Type*；g' : F；f : α -> α；g : α -> M；n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv_natCast_smul`：map_inv_natCast_smul [AddCommMonoid M] [AddCommMon
oid M₂] {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : T
ype*) [Div…
· 使用定理 `map_birkhoffSum`：map_birkhoffSum {F N : Type*} [AddCommMonoid N] [FunLik
e F M N] [AddMonoidHomClass F M N] (g' : F) (f : α -> α) (g : α -> M) (n : Nat) 
(x : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_birkhoffAverage (S : Type*) {F N : Type*}
    [DivisionSemiring S] [AddCommMonoid N] [Module S N] [FunLike F M N]
    [AddMonoidHomClass F M N] (g' : F) (f : α → α) (g : α → M) (n : ℕ) (x : α) :
    g' (birkhoffAverage R f g n x) = birkhoffAverage S f (g' ∘ g) n x := by
  simp only [birkhoffAverage, map_inv_natCast_smul g' R S, map_birkhoffSum]
/-
**birkhoffAverage_congr_ring** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：birkhoffAverage_congr_ring (S : Type*) [DivisionSemiring S] [Module S M] (
f : α -> α) (g : α -> M) (n : Nat) (x : α) : birkhoffAverage R f g n x = birkhof
fAverage S f g n x
参数：S : Type*；f : α -> α；g : α -> M；n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_birkhoffAverage`：map_birkhoffAverage (S : Type*) {F N : Type*} [Divi
sionSemiring S] [AddCommMonoid N] [Module S N] [FunLike F M N] [AddMonoidHomClas
s F M N] …
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem birkhoffAverage_congr_ring (S : Type*) [DivisionSemiring S] [Module S M]
    (f : α → α) (g : α → M) (n : ℕ) (x : α) :
    birkhoffAverage R f g n x = birkhoffAverage S f g n x :=
  map_birkhoffAverage R S (AddMonoidHom.id M) f g n x
/-
**birkhoffAverage_congr_ring'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：birkhoffAverage_congr_ring' (S : Type*) [DivisionSemiring S] [Module S M] 
: birkhoffAverage (α
参数：S : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `birkhoffAverage_congr_ring`：birkhoffAverage_congr_ring (S : Type*) [Divi
sionSemiring S] [Module S M] (f : α -> α) (g : α -> M) (n : Nat) (x : α) : birkh
offAverage R f g…
-/
theorem birkhoffAverage_congr_ring' (S : Type*) [DivisionSemiring S] [Module S M] :
    birkhoffAverage (α := α) (M := M) R = birkhoffAverage S := by
  ext; apply birkhoffAverage_congr_ring
/-
**Function.IsFixedPt.birkhoffAverage_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.IsFixedPt.birkhoffAverage_eq {f : α -> α} {x : α} (h : IsFixedPt 
f x) (g : α -> M) {n : Nat} (hn : (n : R) != 0) : birkhoffAverage R f g n x = g 
x
参数：h : IsFixedPt f x；g : α -> M；hn : (n : R) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `birkhoffAverage.eq_1`：∀ (R : Type u_1) {α : Type u_2} {M : Type u_3} [in
st : DivisionSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R 
M] (f : α …
· 使用定理 `Function.IsFixedPt.birkhoffSum_eq`：Function.IsFixedPt.birkhoffSum_eq {f 
: α -> α} {x : α} (h : IsFixedPt f x) (g : α -> M) (n : Nat) : birkhoffSum f g n
 x = n • g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
-/
theorem Function.IsFixedPt.birkhoffAverage_eq {f : α → α} {x : α} (h : IsFixedPt f x)
    (g : α → M) {n : ℕ} (hn : (n : R) ≠ 0) : birkhoffAverage R f g n x = g x := by
  rw [birkhoffAverage, h.birkhoffSum_eq, ← Nat.cast_smul_eq_nsmul R, inv_smul_smul₀ hn]
/-
**birkhoffAverage_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：birkhoffAverage_add {f : α -> α} {g g' : α -> M} : birkhoffAverage R f (g 
+ g') = birkhoffAverage R f g + birkhoffAverage R f g'
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
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma birkhoffAverage_add {f : α → α} {g g' : α → M} :
    birkhoffAverage R f (g + g') = birkhoffAverage R f g + birkhoffAverage R f g' := by
  funext _ x
  simp [birkhoffAverage, birkhoffSum, sum_add_distrib, smul_add]

/-- If a function `g` is invariant under a function `f` (i.e., `g ∘ f = g`), then the Birkhoff
average of `g` over `f` for `n` iterations is equal to `g`. Requires that `0 < n`. -/
/-
**birkhoffAverage_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：birkhoffAverage_of_comp_eq {f : α -> α} {g : α -> M} (h : g ∘ f = g) {n : 
Nat} (hn : (n : R) != 0) : birkhoffAverage R f g n = g
参数：h : g ∘ f = g；hn : (n : R) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `birkhoffSum_of_comp_eq`：birkhoffSum_of_comp_eq {f : α -> α} {φ : α -> M}
 (h : φ ∘ f = φ) (n : Nat) : birkhoffSum f φ n = n • φ

--- 原说明 ---
If a function `g` is invariant under a function `f` (i.e., `g ∘ f = g`), then th
e Birkhoff
average of `g` over `f` for `n` iterations is equal to `g`. Requires that `0 < n
`.
-/
theorem birkhoffAverage_of_comp_eq {f : α → α} {g : α → M} (h : g ∘ f = g)
    {n : ℕ} (hn : (n : R) ≠ 0) : birkhoffAverage R f g n = g := by
  funext x
  suffices (n : R)⁻¹ • n • g x = g x by simpa [birkhoffAverage, birkhoffSum_of_comp_eq h]
  rw [← Nat.cast_smul_eq_nsmul (R := R), ← mul_smul, inv_mul_cancel₀ hn, one_smul]

end birkhoffAverage

section AddCommGroup

variable {R : Type*} {α M : Type*} [DivisionSemiring R] [AddCommGroup M] [Module R M]

/-
**birkhoffAverage_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：birkhoffAverage_neg {f : α -> α} {g : α -> M} : birkhoffAverage R f (-g) =
 -birkhoffAverage R f g
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
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma birkhoffAverage_neg {f : α → α} {g : α → M} :
    birkhoffAverage R f (-g) = -birkhoffAverage R f g := by
  funext _ x
  simp [birkhoffAverage, birkhoffSum]
/-
**birkhoffAverage_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：birkhoffAverage_sub {f : α -> α} {g g' : α -> M} : birkhoffAverage R f (g 
- g') = birkhoffAverage R f g - birkhoffAverage R f g'
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
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma birkhoffAverage_sub {f : α → α} {g g' : α → M} :
    birkhoffAverage R f (g - g') = birkhoffAverage R f g - birkhoffAverage R f g' := by
  funext _ x
  simp [birkhoffAverage, birkhoffSum, smul_sub]

/-- Birkhoff average is "almost invariant" under `f`:
the difference between `birkhoffAverage R f g n (f x)` and `birkhoffAverage R f g n x`
is equal to `(n : R)⁻¹ • (g (f^[n] x) - g x)`. -/
/-
**birkhoffAverage_apply_sub_birkhoffAverage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：birkhoffAverage_apply_sub_birkhoffAverage (f : α -> α) (g : α -> M) (n : N
at) (x : α) : birkhoffAverage R f g n (f x) - birkhoffAverage R f g n x = (n : R
)⁻¹ • (g (f^[n] x) - g x)
参数：f : α -> α；g : α -> M；n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `birkhoffSum_apply_sub_birkhoffSum`：birkhoffSum_apply_sub_birkhoffSum (f 
: α -> α) (g : α -> G) (n : Nat) (x : α) : birkhoffSum f g n (f x) - birkhoffSum
 f g n x = g (f^[n] x) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Birkhoff average is "almost invariant" under `f`:
the difference between `birkhoffAverage R f g n (f x)` and `birkhoffAverage R f 
g n x`
is equal to `(n : R)⁻¹ • (g (f^[n] x) - g x)`.
-/
theorem birkhoffAverage_apply_sub_birkhoffAverage (f : α → α) (g : α → M) (n : ℕ) (x : α) :
    birkhoffAverage R f g n (f x) - birkhoffAverage R f g n x =
      (n : R)⁻¹ • (g (f^[n] x) - g x) := by
  simp only [birkhoffAverage, birkhoffSum_apply_sub_birkhoffSum, ← smul_sub]

end AddCommGroup

