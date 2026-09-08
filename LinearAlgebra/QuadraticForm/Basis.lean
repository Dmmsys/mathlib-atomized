/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.BigOperators.Sym
public import Mathlib.Data.Finsupp.Pointwise
public import Mathlib.Data.Sym.Sym2.Finsupp
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Constructing a bilinear map from a quadratic map, given a basis

This file provides an alternative to `QuadraticMap.associated`; unlike that definition, this one
does not require `Invertible (2 : R)`. Unlike that definition, this only works in the presence of
a basis.
-/

@[expose] public section

open LinearMap (BilinMap)
open Module

namespace QuadraticMap
variable {ι R M N : Type*}

section Finsupp
variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

open Finsupp

/-
**QuadraticMap.map_finsuppSum'** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：map_finsuppSum' (Q : QuadraticMap R M N) (f : ι ->₀ R) (g : ι -> R -> M) :
 Q (f.sum g) = ∑ p in f.support.sym2, polarSym2 Q (p.map fun i => g i (f i)) - f
.sum fun i a => Q (g i a)
参数：Q : QuadraticMap R M N；f : ι ->₀ R；g : ι -> R -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticMap.map_sum'`：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [i
nst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup N]   [inst_3 
: _root_.Mo…
-/
theorem map_finsuppSum' (Q : QuadraticMap R M N) (f : ι →₀ R) (g : ι → R → M) :
    Q (f.sum g) =
      ∑ p ∈ f.support.sym2, polarSym2 Q (p.map fun i ↦ g i (f i)) - f.sum fun i a ↦ Q (g i a) :=
  Q.map_sum' ..
/-
**QuadraticMap.apply_linearCombination'** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`
。
形式化陈述：apply_linearCombination' (Q : QuadraticMap R M N) {g : ι -> M} (l : ι ->₀ 
R) : Q (linearCombination R g l) = linearCombination R (polarSym2 Q ∘ Sym2.map g
) l.sym2Mul - linearCombination R (Q ∘ g) (l * l)
参数：Q : QuadraticMap R M N；l : ι ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.map_finsuppSum'`：map_finsuppSum' (Q : QuadraticMap R M N) (
f : ι ->₀ R) (g : ι -> R -> M) : Q (f.sum g) = ∑ p in f.support.sym2, polarSym2 
Q (p.map fun i => …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `QuadraticMap.map_smul`：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [i
nst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] 
[inst_3 : A…
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Finsupp.sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_8} {N : Type
 u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) {s : Finset α},  
 f.support ⊆ s → ∀ …
· 使用引理 `Finsupp.support_mul_subset_left`：support_mul_subset_left {g₁ g₂ : α ->₀ 
β} : (g₁ * g₂).support subseteq g₁.support
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Finsupp.support_sym2Mul_subset`：support_sym2Mul_subset : f.sym2Mul.suppo
rt subseteq f.support.sym2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Sym2.map_congr`：map_congr {f g : α -> β} {s : Sym2 α} (h : forall x in s
, f x = g x) : map f s = map g s
-/
theorem apply_linearCombination' (Q : QuadraticMap R M N) {g : ι → M} (l : ι →₀ R) :
    Q (linearCombination R g l) =
      linearCombination R (polarSym2 Q ∘ Sym2.map g) l.sym2Mul -
        linearCombination R (Q ∘ g) (l * l) := by
  simp_rw [linearCombination_apply, map_finsuppSum', Q.map_smul, mul_smul]
  rw [(l * l).sum_of_support_subset support_mul_subset_left _ <| by simp,
    l.sym2Mul.sum_of_support_subset support_sym2Mul_subset _ <| by simp]
  simp [Finsupp.sum, ← polarSym2_map_smul, mul_smul]
/-
**QuadraticMap.sum_polar_sub_repr_sq** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：sum_polar_sub_repr_sq (Q : QuadraticMap R M N) (bm : Basis ι R M) (x : M) 
: linearCombination R (polarSym2 Q ∘ Sym2.map bm) (bm.repr x).sym2Mul - linearCo
mbination R (Q ∘ bm) (bm.repr x * bm.repr x) = Q x
参数：Q : QuadraticMap R M N；bm : Basis ι R M；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuadraticMap.apply_linearCombination'`：apply_linearCombination' (Q : Qua
draticMap R M N) {g : ι -> M} (l : ι ->₀ R) : Q (linearCombination R g l) = line
arCombination R (polarSym2 …
· 使用定理 `Module.Basis.linearCombination_repr`：linearCombination_repr : Finsupp.li
nearCombination _ b (b.repr x) = x
-/
theorem sum_polar_sub_repr_sq (Q : QuadraticMap R M N) (bm : Basis ι R M) (x : M) :
    linearCombination R (polarSym2 Q ∘ Sym2.map bm) (bm.repr x).sym2Mul -
      linearCombination R (Q ∘ bm) (bm.repr x * bm.repr x) = Q x := by
  rw [← apply_linearCombination', Basis.linearCombination_repr]

variable [DecidableEq ι]

/-- The quadratic version of `_root_.map_finsupp_sum`. -/
/-
**QuadraticMap.map_finsuppSum** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：map_finsuppSum (Q : QuadraticMap R M N) (f : ι ->₀ R) (g : ι -> R -> M) : 
Q (f.sum g) = f.sum (fun i r => Q (g i r)) + ∑ p in f.support.sym2 with ¬ p.IsDi
ag, polarSym2 Q (p.map fun i => g i (f i))
参数：Q : QuadraticMap R M N；f : ι ->₀ R；g : ι -> R -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticMap.map_sum`：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [in
st : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup N]   [inst_3 :
 _root_.Mo…

--- 原说明 ---
The quadratic version of `_root_.map_finsupp_sum`.
-/
theorem map_finsuppSum (Q : QuadraticMap R M N) (f : ι →₀ R) (g : ι → R → M) :
    Q (f.sum g) = f.sum (fun i r ↦ Q (g i r)) +
      ∑ p ∈ f.support.sym2 with ¬ p.IsDiag, polarSym2 Q (p.map fun i ↦ g i (f i)) := Q.map_sum _ _

/-- The quadratic version of `Finsupp.apply_linearCombination`. -/
/-
**QuadraticMap.apply_linearCombination** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：apply_linearCombination (Q : QuadraticMap R M N) {g : ι -> M} (l : ι ->₀ R
) : Q (linearCombination R g l) = linearCombination R (Q ∘ g) (l * l) + ∑ p in l
.support.sym2 with ¬ p.IsDiag, (p.map l).mul • polarSym2 Q (p.map g)
参数：Q : QuadraticMap R M N；l : ι ->₀ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.map_finsuppSum`：map_finsuppSum (Q : QuadraticMap R M N) (f 
: ι ->₀ R) (g : ι -> R -> M) : Q (f.sum g) = f.sum (fun i r => Q (g i r)) + ∑ p 
in f.support.sym2…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `QuadraticMap.map_smul`：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [i
nst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] 
[inst_3 : A…
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Finsupp.sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_8} {N : Type
 u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) {s : Finset α},  
 f.support ⊆ s → ∀ …
· 使用引理 `Finsupp.support_mul_subset_left`：support_mul_subset_left {g₁ g₂ : α ->₀ 
β} : (g₁ * g₂).support subseteq g₁.support
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Sym2.map_congr`：map_congr {f g : α -> β} {s : Sym2 α} (h : forall x in s
, f x = g x) : map f s = map g s

--- 原说明 ---
The quadratic version of `Finsupp.apply_linearCombination`.
-/
theorem apply_linearCombination (Q : QuadraticMap R M N) {g : ι → M} (l : ι →₀ R) :
    Q (linearCombination R g l) = linearCombination R (Q ∘ g) (l * l) +
      ∑ p ∈ l.support.sym2 with ¬ p.IsDiag, (p.map l).mul • polarSym2 Q (p.map g) := by
  simp_rw [linearCombination_apply, map_finsuppSum, Q.map_smul, mul_smul]
  rw [(l * l).sum_of_support_subset support_mul_subset_left _ <| by simp]
  simp [Finsupp.sum, ← polarSym2_map_smul, mul_smul]

/-- The quadratic version of `LinearMap.sum_repr_mul_repr_mul`. -/
/-
**QuadraticMap.sum_repr_sq_add_sum_repr_mul_polar** 是 Mathlib 中的一个定理，位于命名空间 `Qua
draticMap`。
形式化陈述：sum_repr_sq_add_sum_repr_mul_polar (Q : QuadraticMap R M N) (bm : Basis ι 
R M) (x : M) : linearCombination R (Q ∘ bm) (bm.repr x * bm.repr x) + ∑ p in (bm
.repr x).support.sym2 with ¬ p.IsDiag, Sym2.mul (p.map (bm.repr x)) • polarSym2 
Q (p.map bm) = Q x
参数：Q : QuadraticMap R M N；bm : Basis ι R M；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuadraticMap.apply_linearCombination`：apply_linearCombination (Q : Quadr
aticMap R M N) {g : ι -> M} (l : ι ->₀ R) : Q (linearCombination R g l) = linear
Combination R (Q ∘ g) (l *…
· 使用定理 `Module.Basis.linearCombination_repr`：linearCombination_repr : Finsupp.li
nearCombination _ b (b.repr x) = x

--- 原说明 ---
The quadratic version of `LinearMap.sum_repr_mul_repr_mul`.
-/
theorem sum_repr_sq_add_sum_repr_mul_polar (Q : QuadraticMap R M N) (bm : Basis ι R M) (x : M) :
    linearCombination R (Q ∘ bm) (bm.repr x * bm.repr x) +
      ∑ p ∈ (bm.repr x).support.sym2 with ¬ p.IsDiag,
        Sym2.mul (p.map (bm.repr x)) • polarSym2 Q (p.map bm) = Q x := by
  rw [← apply_linearCombination, Basis.linearCombination_repr]

end Finsupp

variable [LinearOrder ι]
variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-- Given an ordered basis, produce a bilinear form associated with the quadratic form.

Unlike `QuadraticMap.associated`, this is not symmetric; however, as a result it can be used even
in characteristic two. When considered as a matrix, the form is triangular. -/
/-
**QuadraticMap.toBilin** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：toBilin (Q : QuadraticMap R M N) (bm : Basis ι R M) : LinearMap.BilinMap R
 M N
参数：Q : QuadraticMap R M N；bm : Basis ι R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an ordered basis, produce a bilinear form associated with the quadratic fo
rm.

Unlike `QuadraticMap.associated`, this is not symmetric; however, as a result it
 can be used even
in characteristic two. When considered as a matrix, the form is triangular.
-/
noncomputable def toBilin (Q : QuadraticMap R M N) (bm : Basis ι R M) : LinearMap.BilinMap R M N :=
  bm.constr (S := R) fun i =>
    bm.constr (S := R) fun j =>
      if i = j then Q (bm i) else if i < j then polar Q (bm i) (bm j) else 0
/-
**QuadraticMap.toBilin_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：toBilin_apply (Q : QuadraticMap R M N) (bm : Basis ι R M) (i j : ι) : Q.to
Bilin bm (bm i) (bm j) = if i = j then Q (bm i) else if i < j then polar Q (bm i
) (bm j) else 0
参数：Q : QuadraticMap R M N；bm : Basis ι R M；i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.constr_basis`：constr_basis (f : ι -> M') (i : ι) : (constr 
(M'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toBilin_apply (Q : QuadraticMap R M N) (bm : Basis ι R M) (i j : ι) :
    Q.toBilin bm (bm i) (bm j) =
      if i = j then Q (bm i) else if i < j then polar Q (bm i) (bm j) else 0 := by
  simp [toBilin]

set_option backward.isDefEq.respectTransparency false in
/-
**QuadraticMap.toQuadraticMap_toBilin** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：toQuadraticMap_toBilin (Q : QuadraticMap R M N) (bm : Basis ι R M) : (Q.to
Bilin bm).toQuadraticMap = Q
参数：Q : QuadraticMap R M N；bm : Basis ι R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticMap.ext`：ext (H : forall x : M, Q x = Q' x) : Q = Q'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.linearCombination_repr`：linearCombination_repr : Finsupp.li
nearCombination _ b (b.repr x) = x
· 使用定理 `LinearMap.BilinMap.toQuadraticMap_apply`：toQuadraticMap_apply (B : Bilin
Map R M N) (x : M) : B.toQuadraticMap x = B x x
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `Finsupp.sum.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst 
: Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (g : α → M → N),   f.sum g = ∑
 a ∈ f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.map_sum₂`：map_sum₂ {ι : Type*} (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P)
 (t : Finset ι) (x : ι -> M) (y) : f (∑ i in t, x i) y = ∑ i in t, f (x i) y
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LinearMap.map_smul₂`：map_smul₂ (f : M₂ ->ₗ[R] N₂ ->ₛₗ[σ₁₂] P₂) (r : R) (
x y) : f (r • x) y = r • f x y
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `QuadraticMap.toBilin_apply`：toBilin_apply (Q : QuadraticMap R M N) (bm :
 Basis ι R M) (i j : ι) : Q.toBilin bm (bm i) (bm j) = if i = j then Q (bm i) el
se if i < j then…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_ite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a b : α) (c : β),   (c • if p then a else b) = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Finset.sum_union`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   Disjoint s₁ s₂ → ∑
 x ∈ s…
· 使用定理 `Finset.disjoint_diag_offDiag`：disjoint_diag_offDiag : Disjoint s.diag s.
offDiag
· 使用定理 `Finset.sum_diag`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M
] (s : Finset ι) (f : ι × ι → M),   ∑ i ∈ s.diag, f i = ∑ i ∈ s, f (i, i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `Finset.sum_ite_of_false`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} 
[inst : AddCommMonoid M] {p : ι → Prop} [inst_1 : DecidablePred p],   (∀ x ∈ s, 
¬p x) → ∀ (f …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.mem_offDiag`：mem_offDiag : x in s.offDiag ↔ x.1 in s ∧ x.2 in s ∧
 x.1 != x.2
· 使用定理 `QuadraticMap.map_sum`：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [in
st : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup N]   [inst_3 :
 _root_.Mo…
（共 36 条，此处仅展示前 30 条）
-/
theorem toQuadraticMap_toBilin (Q : QuadraticMap R M N) (bm : Basis ι R M) :
    (Q.toBilin bm).toQuadraticMap = Q := by
  ext x
  rw [← bm.linearCombination_repr x, LinearMap.BilinMap.toQuadraticMap_apply,
      Finsupp.linearCombination_apply, Finsupp.sum]
  simp_rw [LinearMap.map_sum₂, map_sum, LinearMap.map_smul₂, map_smul, toBilin_apply,
    smul_ite, smul_zero, ← Finset.sum_product', ← Finset.diag_union_offDiag,
    Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag, if_true]
  rw [Finset.sum_ite_of_false, QuadraticMap.map_sum, ← Finset.sum_filter]
  · simp_rw [← polar_smul_right _ (bm.repr x <| Prod.snd _),
      ← polar_smul_left _ (bm.repr x <| Prod.fst _)]
    simp_rw [QuadraticMap.map_smul, mul_smul, Finset.sum_sym2_filter_not_isDiag]
    rfl
  · intro x hx
    rw [Finset.mem_offDiag] at hx
    simpa using hx.2.2

/-- From a free module, every quadratic map can be built from a bilinear form.

See `BilinMap.not_forall_toQuadraticMap_surjective` for a counterexample when the module is
not free. -/
/-
**QuadraticMap._root_.LinearMap.BilinMap.toQuadraticMap_surjective** 是 Mathlib 中
的一个定理，位于命名空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
From a free module, every quadratic map can be built from a bilinear form.

See `BilinMap.not_forall_toQuadraticMap_surjective` for a counterexample when th
e module is
not free.
-/
theorem _root_.LinearMap.BilinMap.toQuadraticMap_surjective [Module.Free R M] :
    Function.Surjective (LinearMap.BilinMap.toQuadraticMap : LinearMap.BilinMap R M N → _) := by
  intro Q
  obtain ⟨ι, b⟩ := Module.Free.exists_basis (R := R) (M := M)
  let : LinearOrder ι := IsWellOrder.linearOrder WellOrderingRel
  exact ⟨_, toQuadraticMap_toBilin _ b⟩

@[simp]
/-
**QuadraticMap.add_toBilin** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticMap`。
形式化陈述：add_toBilin (bm : Basis ι R M) (Q₁ Q₂ : QuadraticMap R M N) : (Q₁ + Q₂).to
Bilin bm = Q₁.toBilin bm + Q₂.toBilin bm
参数：bm : Basis ι R M；Q₁ Q₂ : QuadraticMap R M N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.toBilin_apply`：toBilin_apply (Q : QuadraticMap R M N) (bm :
 Basis ι R M) (i j : ι) : Q.toBilin bm (bm i) (bm j) = if i = j then Q (bm i) el
se if i < j then…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FunLike.coe_add`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst : 
FunLike F α β] [inst_1 : Add F] [inst_2 : Add β]   [IsAddApply F α β] (f g : F),
 ⇑(f …
· 使用定理 `QuadraticMap.instIsAddApply`：∀ {R : Type u_3} {M : Type u_4} {N : Type u
_5} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module
 R M] [inst_3 : A…
· 使用定理 `QuadraticMap.polar_add`：polar_add (f g : M -> N) (x y : M) : polar (f + 
g) x y = polar f x y + polar g x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma add_toBilin (bm : Basis ι R M) (Q₁ Q₂ : QuadraticMap R M N) :
    (Q₁ + Q₂).toBilin bm = Q₁.toBilin bm + Q₂.toBilin bm := by
  refine bm.ext fun i => bm.ext fun j => ?_
  obtain h | rfl | h := lt_trichotomy i j
  · simp [h.ne, h, toBilin_apply, polar_add]
  · simp [toBilin_apply]
  · simp [h.ne', h.not_gt, toBilin_apply]

variable (S) [CommSemiring S] [Algebra S R]
variable [Module S N] [IsScalarTower S R N]

@[simp]
/-
**QuadraticMap.smul_toBilin** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticMap`。
形式化陈述：smul_toBilin (bm : Basis ι R M) (s : S) (Q : QuadraticMap R M N) : (s • Q)
.toBilin bm = s • Q.toBilin bm
参数：bm : Basis ι R M；s : S；Q : QuadraticMap R M N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.toBilin_apply`：toBilin_apply (Q : QuadraticMap R M N) (bm :
 Basis ι R M) (i j : ι) : Q.toBilin bm (bm i) (bm j) = if i = j then Q (bm i) el
se if i < j then…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FunLike.coe_smul`：coe_smul [SMul M F] [SMul M β] [IsSMulApply M F α β] (
n : M) (f : F) : ↑(n • f) = n • (f : α -> β)
· 使用定理 `QuadraticMap.instIsSMulApply`：∀ {S : Type u_1} {R : Type u_3} {M : Type 
u_4} {N : Type u_5} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2
 : _root_.Module R…
· 使用定理 `QuadraticMap.polar_smul`：polar_smul [Monoid S] [DistribMulAction S N] (f
 : M -> N) (s : S) (x y : M) : polar (s • f) x y = s • polar f x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
lemma smul_toBilin (bm : Basis ι R M) (s : S) (Q : QuadraticMap R M N) :
    (s • Q).toBilin bm = s • Q.toBilin bm := by
  refine bm.ext fun i => bm.ext fun j => ?_
  obtain h | rfl | h := lt_trichotomy i j
  · simp [h.ne, h, toBilin_apply, polar_smul]
  · simp [toBilin_apply]
  · simp [h.ne', h.not_gt, toBilin_apply]

/-- `QuadraticMap.toBilin` as an S-linear map -/
@[simps]
/-
**QuadraticMap.toBilinHom** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：toBilinHom (bm : Basis ι R M) : QuadraticMap R M N ->ₗ[S] BilinMap R M N w
here toFun Q
参数：bm : Basis ι R M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `QuadraticMap.add_toBilin`：add_toBilin (bm : Basis ι R M) (Q₁ Q₂ : Quadra
ticMap R M N) : (Q₁ + Q₂).toBilin bm = Q₁.toBilin bm + Q₂.toBilin bm
· 使用引理 `QuadraticMap.smul_toBilin`：smul_toBilin (bm : Basis ι R M) (s : S) (Q : 
QuadraticMap R M N) : (s • Q).toBilin bm = s • Q.toBilin bm

--- 原说明 ---
`QuadraticMap.toBilin` as an S-linear map
-/
noncomputable def toBilinHom (bm : Basis ι R M) : QuadraticMap R M N →ₗ[S] BilinMap R M N where
  toFun Q := Q.toBilin bm
  map_add' := add_toBilin bm
  map_smul' := smul_toBilin S bm

end QuadraticMap

