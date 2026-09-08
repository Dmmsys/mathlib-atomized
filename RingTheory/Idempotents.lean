/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.LinearCombination

/-!

# Idempotents in rings

The predicate `IsIdempotentElem` is defined for general monoids in
`Mathlib/Algebra/Group/Idempotent.lean`; ring-specific lemmas are in
`Mathlib/Algebra/Ring/Idempotent.lean`.
In this file we provide various results regarding idempotent elements in rings.

## Main definitions

- `OrthogonalIdempotents`:
  A family `{ eᵢ }` of idempotent elements is orthogonal if `eᵢ * eⱼ = 0` for all `i ≠ j`.
- `CompleteOrthogonalIdempotents`:
  A family `{ eᵢ }` of orthogonal idempotent elements is complete if `∑ eᵢ = 1`.

## Main results

- `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker`:
  If the kernel of `f : R →+* S` consists of nilpotent elements, and `{ eᵢ }` is a family of
  complete orthogonal idempotents in the range of `f`, then `{ eᵢ }` is the image of some
  complete orthogonal idempotents in `R`.
- `existsUnique_isIdempotentElem_eq_of_ker_isNilpotent`:
  If `R` is commutative and the kernel of `f : R →+* S` consists of nilpotent elements,
  then every idempotent in the range of `f` lifts to a unique idempotent in `R`.
- `CompleteOrthogonalIdempotents.bijective_pi`:
  If `R` is commutative, then a family `{ eᵢ }` of complete orthogonal idempotent elements induces
  a ring isomorphism `R ≃ ∏ R ⧸ ⟨1 - eᵢ⟩`.
-/

@[expose] public section

section Semiring

variable {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
variable {I : Type*} (e : I → R)

/-- A family `{ eᵢ }` of idempotent elements is orthogonal if `eᵢ * eⱼ = 0` for all `i ≠ j`. -/
@[mk_iff]
/-
**OrthogonalIdempotents** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_1} → [Semiring R] → {I : Type u_3} → (I → R) → Prop
参数：I → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family `{ eᵢ }` of idempotent elements is orthogonal if `eᵢ * eⱼ = 0` for all 
`i ≠ j`.
-/
structure OrthogonalIdempotents : Prop where
  idem : ∀ i, IsIdempotentElem (e i)
  ortho : Pairwise (e · * e · = 0)

variable {e}
/-
**OrthogonalIdempotents.mul_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OrthogonalIdempotents.mul_eq [DecidableEq I] (he : OrthogonalIdempotents e
) (i j) : e i * e j = if i = j then e i else 0
参数：he : OrthogonalIdempotents e；i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `OrthogonalIdempotents.ortho`：∀ {R : Type u_1} [inst : Semiring R] {I : T
ype u_3} {e : I → R},   OrthogonalIdempotents e → Pairwise fun x1 x2 => e x1 * e
 x2 = 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `OrthogonalIdempotents.idem`：∀ {R : Type u_1} [inst : Semiring R] {I : Ty
pe u_3} {e : I → R},   OrthogonalIdempotents e → ∀ (i : I), IsIdempotentElem (e 
i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma OrthogonalIdempotents.mul_eq [DecidableEq I] (he : OrthogonalIdempotents e) (i j) :
    e i * e j = if i = j then e i else 0 := by
  split
  · simp [*, (he.idem j).eq]
  · exact he.ortho ‹_›
/-
**OrthogonalIdempotents.iff_mul_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OrthogonalIdempotents.iff_mul_eq [DecidableEq I] : OrthogonalIdempotents e
 ↔ forall i j, e i * e j = if i = j then e i else 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `OrthogonalIdempotents.mul_eq`：OrthogonalIdempotents.mul_eq [DecidableEq 
I] (he : OrthogonalIdempotents e) (i j) : e i * e j = if i = j then e i else 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
lemma OrthogonalIdempotents.iff_mul_eq [DecidableEq I] :
    OrthogonalIdempotents e ↔ ∀ i j, e i * e j = if i = j then e i else 0 :=
  ⟨mul_eq, fun H ↦ ⟨fun i ↦ by simpa using! H i i, fun i j e ↦ by simpa [e] using! H i j⟩⟩
/-
**OrthogonalIdempotents.isIdempotentElem_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OrthogonalIdempotents.isIdempotentElem_sum (he : OrthogonalIdempotents e) 
{s : Finset I} : IsIdempotentElem (∑ i in s, e i)
参数：he : OrthogonalIdempotents e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用引理 `OrthogonalIdempotents.mul_eq`：OrthogonalIdempotents.mul_eq [DecidableEq 
I] (he : OrthogonalIdempotents e) (i j) : e i * e j = if i = j then e i else 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `Finset.sum_ite_mem`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s t : Finset ι) (f : ι → M),   (∑ i ∈ s, if i ∈ t
 then f …
· 使用定理 `Finset.inter_self`：inter_self (s : Finset α) : s inter s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma OrthogonalIdempotents.isIdempotentElem_sum (he : OrthogonalIdempotents e) {s : Finset I} :
    IsIdempotentElem (∑ i ∈ s, e i) := by
  classical
  simp [IsIdempotentElem, Finset.sum_mul, Finset.mul_sum, he.mul_eq]
/-
**OrthogonalIdempotents.mul_sum_of_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OrthogonalIdempotents.mul_sum_of_mem (he : OrthogonalIdempotents e) {i : I
} {s : Finset I} (h : i in s) : e i * ∑ j in s, e j = e i
参数：he : OrthogonalIdempotents e；h : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `OrthogonalIdempotents.mul_eq`：OrthogonalIdempotents.mul_eq [DecidableEq 
I] (he : OrthogonalIdempotents e) (i j) : e i * e j = if i = j then e i else 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma OrthogonalIdempotents.mul_sum_of_mem (he : OrthogonalIdempotents e)
    {i : I} {s : Finset I} (h : i ∈ s) : e i * ∑ j ∈ s, e j = e i := by
  classical
  simp [Finset.mul_sum, he.mul_eq, h]
/-
**OrthogonalIdempotents.mul_sum_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OrthogonalIdempotents.mul_sum_of_notMem (he : OrthogonalIdempotents e) {i 
: I} {s : Finset I} (h : i ∉ s) : e i * ∑ j in s, e j = 0
参数：he : OrthogonalIdempotents e；h : i ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `OrthogonalIdempotents.mul_eq`：OrthogonalIdempotents.mul_eq [DecidableEq 
I] (he : OrthogonalIdempotents e) (i j) : e i * e j = if i = j then e i else 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma OrthogonalIdempotents.mul_sum_of_notMem (he : OrthogonalIdempotents e)
    {i : I} {s : Finset I} (h : i ∉ s) : e i * ∑ j ∈ s, e j = 0 := by
  classical
  simp [Finset.mul_sum, he.mul_eq, h]
/-
**OrthogonalIdempotents.map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OrthogonalIdempotents.map (he : OrthogonalIdempotents e) : OrthogonalIdemp
otents (f ∘ e)
参数：he : OrthogonalIdempotents e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用引理 `OrthogonalIdempotents.mul_eq`：OrthogonalIdempotents.mul_eq [DecidableEq 
I] (he : OrthogonalIdempotents e) (i j) : e i * e j = if i = j then e i else 0
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma OrthogonalIdempotents.map (he : OrthogonalIdempotents e) :
    OrthogonalIdempotents (f ∘ e) := by
  classical
  simp [iff_mul_eq, he.mul_eq, ← map_mul f, apply_ite f]
/-
**OrthogonalIdempotents.map_injective_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OrthogonalIdempotents.map_injective_iff (hf : Function.Injective f) : Orth
ogonalIdempotents (f ∘ e) ↔ OrthogonalIdempotents e
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
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
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma OrthogonalIdempotents.map_injective_iff (hf : Function.Injective f) :
    OrthogonalIdempotents (f ∘ e) ↔ OrthogonalIdempotents e := by
  classical
  simp [iff_mul_eq, ← hf.eq_iff, apply_ite]
/-
**OrthogonalIdempotents.embedding** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OrthogonalIdempotents.embedding (he : OrthogonalIdempotents e) {J} (i : J 
↪ I) : OrthogonalIdempotents (e ∘ i)
参数：he : OrthogonalIdempotents e；i : J ↪ I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `OrthogonalIdempotents.mul_eq`：OrthogonalIdempotents.mul_eq [DecidableEq 
I] (he : OrthogonalIdempotents e) (i j) : e i * e j = if i = j then e i else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma OrthogonalIdempotents.embedding (he : OrthogonalIdempotents e) {J} (i : J ↪ I) :
    OrthogonalIdempotents (e ∘ i) := by
  classical
  simp [iff_mul_eq, he.mul_eq]
/-
**OrthogonalIdempotents.equiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OrthogonalIdempotents.equiv {J} (i : J ≃ I) : OrthogonalIdempotents (e ∘ i
) ↔ OrthogonalIdempotents e
参数：i : J ≃ I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma OrthogonalIdempotents.equiv {J} (i : J ≃ I) :
    OrthogonalIdempotents (e ∘ i) ↔ OrthogonalIdempotents e := by
  classical
  simp [iff_mul_eq, i.forall_congr_left]
/-
**OrthogonalIdempotents.unique** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OrthogonalIdempotents.unique [Unique I] : OrthogonalIdempotents e ↔ IsIdem
potentElem (e default)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma OrthogonalIdempotents.unique [Unique I] :
    OrthogonalIdempotents e ↔ IsIdempotentElem (e default) := by
  simp only [orthogonalIdempotents_iff, Unique.forall_iff, Subsingleton.pairwise, and_true]
/-
**OrthogonalIdempotents.option** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OrthogonalIdempotents.option (he : OrthogonalIdempotents e) [Fintype I] (x
) (hx : IsIdempotentElem x) (hx₁ : x * ∑ i, e i = 0) (hx₂ : (∑ i, e i) * x = 0) 
: OrthogonalIdempotents (Option.elim · x e) where idem i
参数：he : OrthogonalIdempotents e；x；hx : IsIdempotentElem x；hx₁ : x * ∑ i, e i = 0
；hx₂ : (∑ i, e i) * x = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrthogonalIdempotents.idem`：∀ {R : Type u_1} [inst : Semiring R] {I : Ty
pe u_3} {e : I → R},   OrthogonalIdempotents e → ∀ (i : I), IsIdempotentElem (e 
i)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `OrthogonalIdempotents.mul_eq`：OrthogonalIdempotents.mul_eq [DecidableEq 
I] (he : OrthogonalIdempotents e) (i j) : e i * e j = if i = j then e i else 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `OrthogonalIdempotents.ortho`：∀ {R : Type u_1} [inst : Semiring R] {I : T
ype u_3} {e : I → R},   OrthogonalIdempotents e → Pairwise fun x1 x2 => e x1 * e
 x2 = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `Option.some_inj`：∀ {α : Type u_1} {a b : α}, some a = some b ↔ a = b
-/
lemma OrthogonalIdempotents.option (he : OrthogonalIdempotents e) [Fintype I] (x)
    (hx : IsIdempotentElem x) (hx₁ : x * ∑ i, e i = 0) (hx₂ : (∑ i, e i) * x = 0) :
    OrthogonalIdempotents (Option.elim · x e) where
  idem i := i.rec hx he.idem
  ortho i j ne := by
    classical
    rcases i with - | i <;> rcases j with - | j
    · cases ne rfl
    · simpa only [mul_assoc, Finset.sum_mul, he.mul_eq, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, zero_mul] using! congr_arg (· * e j) hx₁
    · simpa only [Option.elim_some, Option.elim_none, ← mul_assoc, Finset.mul_sum, he.mul_eq,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, mul_zero] using! congr_arg (e i * ·) hx₂
    · exact he.ortho (Option.some_inj.ne.mp ne)

variable [Fintype I]

/--
A family `{ eᵢ }` of idempotent elements is complete orthogonal if
1. (orthogonal) `eᵢ * eⱼ = 0` for all `i ≠ j`.
2. (complete) `∑ eᵢ = 1`
-/
@[mk_iff]
/-
**CompleteOrthogonalIdempotents** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_1} → [Semiring R] → {I : Type u_3} → [Fintype I] → (I → R) → P
rop
参数：I → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family `{ eᵢ }` of idempotent elements is complete orthogonal if
1. (orthogonal) `eᵢ * eⱼ = 0` for all `i ≠ j`.
2. (complete) `∑ eᵢ = 1`
-/
structure CompleteOrthogonalIdempotents (e : I → R) : Prop extends OrthogonalIdempotents e where
  complete : ∑ i, e i = 1

/-- If a family is complete orthogonal, it consists of idempotents. -/
/-
**CompleteOrthogonalIdempotents.iff_ortho_complete** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompleteOrthogonalIdempotents.iff_ortho_complete : CompleteOrthogonalIdemp
otents e ↔ Pairwise (e · * e · = 0) ∧ ∑ i, e i = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `completeOrthogonalIdempotents_iff`：∀ {R : Type u_1} [inst : Semiring R] 
{I : Type u_3} [inst_1 : Fintype I] (e : I → R),   CompleteOrthogonalIdempotents
 e ↔ OrthogonalIdempote…
· 使用定理 `orthogonalIdempotents_iff`：∀ {R : Type u_1} [inst : Semiring R] {I : Typ
e u_3} (e : I → R),   OrthogonalIdempotents e ↔ (∀ (i : I), IsIdempotentElem (e 
i)) ∧ Pairwise …
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If a family is complete orthogonal, it consists of idempotents.
-/
lemma CompleteOrthogonalIdempotents.iff_ortho_complete :
    CompleteOrthogonalIdempotents e ↔ Pairwise (e · * e · = 0) ∧ ∑ i, e i = 1 := by
  rw [completeOrthogonalIdempotents_iff, orthogonalIdempotents_iff, and_assoc, and_iff_right_of_imp]
  intro ⟨ortho, complete⟩ i
  apply_fun (e i * ·) at complete
  rwa [Finset.mul_sum, Finset.sum_eq_single i (fun _ _ ne ↦ ortho ne.symm) (by simp at ·), mul_one]
    at complete
/-
**CompleteOrthogonalIdempotents.pair_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompleteOrthogonalIdempotents.pair_iff'ₛ {x y : R} : CompleteOrthogonalIde
mpotents ![x, y] ↔ x * y = 0 ∧ y * x = 0 ∧ x + y = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma CompleteOrthogonalIdempotents.pair_iff'ₛ {x y : R} :
    CompleteOrthogonalIdempotents ![x, y] ↔ x * y = 0 ∧ y * x = 0 ∧ x + y = 1 := by
  simp [iff_ortho_complete, Pairwise, Fin.forall_fin_two, and_assoc]
/-
**CompleteOrthogonalIdempotents.pair_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompleteOrthogonalIdempotents.pair_iff {x y : R} : CompleteOrthogonalIdemp
otents ![x, y] ↔ IsIdempotentElem x ∧ y = 1 - x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompleteOrthogonalIdempotents.pair_iff'ₛ`：∀ {R : Type u_1} [inst : Semir
ing R] {x y : R},   CompleteOrthogonalIdempotents ![x, y] ↔ x * y = 0 ∧ y * x = 
0 ∧ x + y = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_sub_iff_add_eq'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a = b - c ↔ c + a = b
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `and_congr_left_iff`：∀ {a c b : Prop}, (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma CompleteOrthogonalIdempotents.pair_iffₛ {R} [CommSemiring R] {x y : R} :
    CompleteOrthogonalIdempotents ![x, y] ↔ x * y = 0 ∧ x + y = 1 := by
  rw [pair_iff'ₛ, and_left_comm, and_iff_right_of_imp]; exact (mul_comm x y ▸ ·.1)
/-
**CompleteOrthogonalIdempotents.unique_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompleteOrthogonalIdempotents.unique_iff [Unique I] : CompleteOrthogonalId
empotents e ↔ e default = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `completeOrthogonalIdempotents_iff`：∀ {R : Type u_1} [inst : Semiring R] 
{I : Type u_3} [inst_1 : Fintype I] (e : I → R),   CompleteOrthogonalIdempotents
 e ↔ OrthogonalIdempote…
· 使用引理 `OrthogonalIdempotents.unique`：OrthogonalIdempotents.unique [Unique I] : 
OrthogonalIdempotents e ↔ IsIdempotentElem (e default)
· 使用定理 `Fintype.sum_unique`：∀ {M : Type u_4} {ι : Type u_7} [inst : Fintype ι] [
inst_1 : AddCommMonoid M] [inst_2 : Unique ι] (f : ι → M),   ∑ x, f x = f defaul
t
· 使用定理 `and_iff_right_iff_imp`：∀ {a b : Prop}, (a ∧ b ↔ b) ↔ b → a
· 使用引理 `IsIdempotentElem.one`：one : IsIdempotentElem (1 : M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma CompleteOrthogonalIdempotents.unique_iff [Unique I] :
    CompleteOrthogonalIdempotents e ↔ e default = 1 := by
  rw [completeOrthogonalIdempotents_iff, OrthogonalIdempotents.unique, Fintype.sum_unique,
    and_iff_right_iff_imp]
  exact (· ▸ IsIdempotentElem.one)
/-
**CompleteOrthogonalIdempotents.single** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompleteOrthogonalIdempotents.single {I : Type*} [Fintype I] [DecidableEq 
I] (R : I -> Type*) [forall i, Semiring (R i)] : CompleteOrthogonalIdempotents (
Pi.single (M
参数：R : I -> Type*；R i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.univ_sum_single`：∀ {I : Type u_7} [inst : DecidableEq I] {M : I →
 Type u_8} [inst_1 : (i : I) → AddCommMonoid (M i)] [inst_2 : Fintype I]   (f : 
(i : I) → M …
-/
lemma CompleteOrthogonalIdempotents.single {I : Type*} [Fintype I] [DecidableEq I]
    (R : I → Type*) [∀ i, Semiring (R i)] :
    CompleteOrthogonalIdempotents (Pi.single (M := R) · 1) := by
  refine ⟨⟨by simp [IsIdempotentElem, ← Pi.single_mul], ?_⟩, Finset.univ_sum_single 1⟩
  intro i j hij
  ext k
  by_cases hi : i = k
  · subst hi; simp [hij]
  · simp [hi]
/-
**CompleteOrthogonalIdempotents.map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompleteOrthogonalIdempotents.map (he : CompleteOrthogonalIdempotents e) :
 CompleteOrthogonalIdempotents (f ∘ e) where __
参数：he : CompleteOrthogonalIdempotents e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `OrthogonalIdempotents.map`：OrthogonalIdempotents.map (he : OrthogonalIde
mpotents e) : OrthogonalIdempotents (f ∘ e)
· 使用定理 `CompleteOrthogonalIdempotents.toOrthogonalIdempotents`：∀ {R : Type u_1} 
[inst : Semiring R] {I : Type u_3} [inst_1 : Fintype I] {e : I → R},   CompleteO
rthogonalIdempotents e → OrthogonalIdempote…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `CompleteOrthogonalIdempotents.complete`：∀ {R : Type u_1} [inst : Semirin
g R] {I : Type u_3} [inst_1 : Fintype I] {e : I → R},   CompleteOrthogonalIdempo
tents e → ∑ i, e i = 1
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma CompleteOrthogonalIdempotents.map (he : CompleteOrthogonalIdempotents e) :
    CompleteOrthogonalIdempotents (f ∘ e) where
  __ := he.toOrthogonalIdempotents.map f
  complete := by simp only [Function.comp_apply, ← map_sum, he.complete, map_one]
/-
**CompleteOrthogonalIdempotents.map_injective_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompleteOrthogonalIdempotents.map_injective_iff (hf : Function.Injective f
) : CompleteOrthogonalIdempotents (f ∘ e) ↔ CompleteOrthogonalIdempotents e
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `OrthogonalIdempotents.map_injective_iff`：OrthogonalIdempotents.map_injec
tive_iff (hf : Function.Injective f) : OrthogonalIdempotents (f ∘ e) ↔ Orthogona
lIdempotents e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma CompleteOrthogonalIdempotents.map_injective_iff (hf : Function.Injective f) :
    CompleteOrthogonalIdempotents (f ∘ e) ↔ CompleteOrthogonalIdempotents e := by
  simp [completeOrthogonalIdempotents_iff, ← hf.eq_iff,
    OrthogonalIdempotents.map_injective_iff f hf]
/-
**CompleteOrthogonalIdempotents.equiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompleteOrthogonalIdempotents.equiv {J} [Fintype J] (i : J ≃ I) : Complete
OrthogonalIdempotents (e ∘ i) ↔ CompleteOrthogonalIdempotents e
参数：i : J ≃ I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fintype.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst 
: Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (f : 
ι → M) …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma CompleteOrthogonalIdempotents.equiv {J} [Fintype J] (i : J ≃ I) :
    CompleteOrthogonalIdempotents (e ∘ i) ↔ CompleteOrthogonalIdempotents e := by
  simp only [completeOrthogonalIdempotents_iff, OrthogonalIdempotents.equiv, Function.comp_apply,
    Fintype.sum_equiv i _ e (fun _ ↦ rfl)]

@[nontriviality]
/-
**CompleteOrthogonalIdempotents.of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompleteOrthogonalIdempotents.of_subsingleton [Subsingleton R] : CompleteO
rthogonalIdempotents e
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma CompleteOrthogonalIdempotents.of_subsingleton [Subsingleton R] :
    CompleteOrthogonalIdempotents e :=
  ⟨⟨fun _ ↦ Subsingleton.elim _ _, fun _ _ _ ↦ Subsingleton.elim _ _⟩, Subsingleton.elim _ _⟩

end Semiring

section Ring

variable {R S : Type*} [Ring R] [Ring S] (f : R →+* S)

/-
**isIdempotentElem_one_sub_one_sub_pow_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIdempotentElem_one_sub_one_sub_pow_pow (x : R) (n : Nat) (hx : (x - x ^ 
2) ^ n = 0) : IsIdempotentElem (1 - (1 - x ^ n) ^ n)
参数：x : R；n : Nat；hx : (x - x ^ 2) ^ n = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one_sub`：mul_one_sub (a b : α) : a * (1 - b) = a - a * b
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `Commute.mul_geom_sum₂`：Commute.mul_geom_sum₂ (h : Commute x y) (n : Nat)
 : ((x - y) * ∑ i in range n, x ^ i * y ^ (n - 1 - i)) = x ^ n - y ^ n
· 使用定理 `Commute.one_left`：one_left (a : M) : Commute 1 a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Commute.mul_pow`：∀ {M : Type u_2} [inst : Monoid M] {a b : M}, Commute a
 b → ∀ (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `Commute.sub_left`：sub_left : Commute a c -> Commute b c -> Commute (a - 
b) c
· 使用定理 `Commute.sum_right`：∀ {ι : Type u_1} {R : Type u_4} [inst : NonUnitalNonA
ssocSemiring R] (s : Finset ι) (f : ι → R) (b : R),   (∀ i ∈ s, Commute b (f i))
 → Comm…
· 使用定理 `Commute.pow_right`：pow_right (h : Commute a b) (n : Nat) : Commute a (b 
^ n)
· 使用定理 `Commute.mul_mul_mul_comm`：∀ {S : Type u_3} [inst : Semigroup S] {b c : S
}, Commute b c → ∀ (a d : S), a * b * (c * d) = a * c * (b * d)
· 使用定理 `Commute.sub_right`：sub_right : Commute a b -> Commute a c -> Commute a (
b - c)
· 使用定理 `Commute.one_right`：one_right (a : M) : Commute a 1
· 使用定理 `Commute.sum_left`：∀ {ι : Type u_1} {R : Type u_4} [inst : NonUnitalNonAs
socSemiring R] (s : Finset ι) (f : ι → R) (b : R),   (∀ i ∈ s, Commute (f i) b) 
→ Comm…
· 使用定理 `Commute.pow_left`：pow_left (h : Commute a b) (n : Nat) : Commute (a ^ n)
 b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
-/
theorem isIdempotentElem_one_sub_one_sub_pow_pow
    (x : R) (n : ℕ) (hx : (x - x ^ 2) ^ n = 0) :
    IsIdempotentElem (1 - (1 - x ^ n) ^ n) := by
  have : (x - x ^ 2) ^ n ∣ (1 - (1 - x ^ n) ^ n) - (1 - (1 - x ^ n) ^ n) ^ 2 := by
    conv_rhs => rw [pow_two, ← mul_one_sub, sub_sub_cancel]
    nth_rw 1 3 [← one_pow n]
    rw [← (Commute.one_left x).mul_geom_sum₂, ← (Commute.one_left (1 - x ^ n)).mul_geom_sum₂]
    simp only [sub_sub_cancel, one_pow, one_mul]
    rw [Commute.mul_pow, Commute.mul_mul_mul_comm, ← Commute.mul_pow, mul_one_sub, ← pow_two]
    · exact ⟨_, rfl⟩
    · simp
    · refine .pow_right (.sub_right (.one_right _) (.sum_left _ _ _ fun _ _ ↦ .pow_left ?_ _)) _
      simp
    · exact .sub_left (.one_left _) (.sum_right _ _ _ fun _ _ ↦ .pow_right rfl _)
  rwa [hx, zero_dvd_iff, sub_eq_zero, eq_comm, pow_two] at this
/-
**exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent_aux** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent_aux (h : forall x i
n RingHom.ker f, IsNilpotent x) (e₁ : S) (he : e₁ in f.range) (he₁ : IsIdempoten
tElem e₁) (e₂ : R) (he₂ : IsIdempotentElem e₂) (he₁e₂ : e₁ * f e₂ = 0) : exists 
e' : R, IsIdempotentElem e' ∧ f e' = e₁ ∧ e' * e₂ = 0
参数：h : forall x in RingHom.ker f, IsNilpotent x；e₁ : S；he : e₁ in f.range；he₁ : 
IsIdempotentElem e₁；e₂ : R；he₂ : IsIdempotentElem e₂；he₁e₂ : e₁ * f e₂ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `isIdempotentElem_one_sub_one_sub_pow_pow`：isIdempotentElem_one_sub_one_s
ub_pow_pow (x : R) (n : Nat) (hx : (x - x ^ 2) ^ n = 0) : IsIdempotentElem (1 - 
(1 - x ^ n) ^ n)
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
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
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用引理 `IsIdempotentElem.pow_succ_eq`：pow_succ_eq (n : Nat) (h : IsIdempotentEle
m a) : a ^ (n + 1) = a
· 使用引理 `IsIdempotentElem.one_sub`：one_sub (h : IsIdempotentElem a) : IsIdempoten
tElem (1 - a)
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用引理 `Commute.sub_dvd_pow_sub_pow`：Commute.sub_dvd_pow_sub_pow (h : Commute x 
y) (n : Nat) : x - y ∣ x ^ n - y ^ n
（共 36 条，此处仅展示前 30 条）
-/
theorem exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent_aux
    (h : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    (e₁ : S) (he : e₁ ∈ f.range) (he₁ : IsIdempotentElem e₁)
    (e₂ : R) (he₂ : IsIdempotentElem e₂) (he₁e₂ : e₁ * f e₂ = 0) :
    ∃ e' : R, IsIdempotentElem e' ∧ f e' = e₁ ∧ e' * e₂ = 0 := by
  obtain ⟨e₁, rfl⟩ := he
  cases subsingleton_or_nontrivial R
  · exact ⟨_, Subsingleton.elim _ _, rfl, Subsingleton.elim _ _⟩
  let a := e₁ - e₁ * e₂
  have ha : f a = f e₁ := by rw [map_sub, map_mul, he₁e₂, sub_zero]
  have ha' : a * e₂ = 0 := by rw [sub_mul, mul_assoc, he₂.eq, sub_self]
  have hx' : a - a ^ 2 ∈ RingHom.ker f := by
    simp [RingHom.mem_ker, pow_two, ha, he₁.eq]
  obtain ⟨n, hn⟩ := h _ hx'
  refine ⟨_, isIdempotentElem_one_sub_one_sub_pow_pow _ _ hn, ?_, ?_⟩
  · rcases n with - | n
    · simp at hn
    simp only [map_sub, map_one, map_pow, ha, he₁.pow_succ_eq,
      he₁.one_sub.pow_succ_eq, sub_sub_cancel]
  · obtain ⟨k, hk⟩ := (Commute.one_left (MulOpposite.op <| 1 - a ^ n)).sub_dvd_pow_sub_pow n
    apply_fun MulOpposite.unop at hk
    have : 1 - (1 - a ^ n) ^ n = MulOpposite.unop k * a ^ n := by simpa using hk
    rw [this, mul_assoc]
    rcases n with - | n
    · simp at hn
    rw [pow_succ, mul_assoc, ha', mul_zero, mul_zero]

/-- Orthogonal idempotents lift along nil ideals. -/
/-
**exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent (h : forall x in Ri
ngHom.ker f, IsNilpotent x) (e₁ : S) (he : e₁ in f.range) (he₁ : IsIdempotentEle
m e₁) (e₂ : R) (he₂ : IsIdempotentElem e₂) (he₁e₂ : e₁ * f e₂ = 0) (he₂e₁ : f e₂
 * e₁ = 0) : exists e' : R, IsIdempotentElem e' ∧ f e' = e₁ ∧ e' * e₂ = 0 ∧ e₂ *
 e' = 0
参数：h : forall x in RingHom.ker f, IsNilpotent x；e₁ : S；he : e₁ in f.range；he₁ : 
IsIdempotentElem e₁；e₂ : R；he₂ : IsIdempotentElem e₂；he₁e₂ : e₁ * f e₂ = 0；he₂e₁
 : f e₂ * e₁ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent_aux`：exists_isIde
mpotentElem_mul_eq_zero_of_ker_isNilpotent_aux (h : forall x in RingHom.ker f, I
sNilpotent x) (e₁ : S) (he : e₁ in f.range) (he₁…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsIdempotentElem.eq_1`：∀ {M : Type u_1} [inst : Mul M] (a : M), IsIdempo
tentElem a = (a * a = a)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
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
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0

--- 原说明 ---
Orthogonal idempotents lift along nil ideals.
-/
theorem exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent
    (h : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    (e₁ : S) (he : e₁ ∈ f.range) (he₁ : IsIdempotentElem e₁)
    (e₂ : R) (he₂ : IsIdempotentElem e₂) (he₁e₂ : e₁ * f e₂ = 0) (he₂e₁ : f e₂ * e₁ = 0) :
    ∃ e' : R, IsIdempotentElem e' ∧ f e' = e₁ ∧ e' * e₂ = 0 ∧ e₂ * e' = 0 := by
  obtain ⟨e', h₁, rfl, h₂⟩ := exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent_aux
    f h e₁ he he₁ e₂ he₂ he₁e₂
  refine ⟨(1 - e₂) * e', ?_, ?_, ?_, ?_⟩
  · rw [IsIdempotentElem, mul_assoc, ← mul_assoc e', mul_sub, mul_one, h₂, sub_zero, h₁.eq]
  · rw [map_mul, map_sub, map_one, sub_mul, one_mul, he₂e₁, sub_zero]
  · rw [mul_assoc, h₂, mul_zero]
  · rw [← mul_assoc, mul_sub, mul_one, he₂.eq, sub_self, zero_mul]

/-- Idempotents lift along nil ideals. -/
/-
**exists_isIdempotentElem_eq_of_ker_isNilpotent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_isIdempotentElem_eq_of_ker_isNilpotent (h : forall x in RingHom.ker
 f, IsNilpotent x) (e : S) (he : e in f.range) (he' : IsIdempotentElem e) : exis
ts e' : R, IsIdempotentElem e' ∧ f e' = e
参数：h : forall x in RingHom.ker f, IsNilpotent x；e : S；he : e in f.range；he' : Is
IdempotentElem e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent`：exists_isIdempot
entElem_mul_eq_zero_of_ker_isNilpotent (h : forall x in RingHom.ker f, IsNilpote
nt x) (e₁ : S) (he : e₁ in f.range) (he₁ : I…
· 使用引理 `IsIdempotentElem.zero`：zero : IsIdempotentElem (0 : M₀)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
Idempotents lift along nil ideals.
-/
theorem exists_isIdempotentElem_eq_of_ker_isNilpotent (h : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    (e : S) (he : e ∈ f.range) (he' : IsIdempotentElem e) :
    ∃ e' : R, IsIdempotentElem e' ∧ f e' = e := by
  simpa using exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent f h e he he' 0 .zero (by simp)
/-
**OrthogonalIdempotents.lift_of_isNilpotent_ker_aux** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：OrthogonalIdempotents.lift_of_isNilpotent_ker_aux (h : forall x in RingHom
.ker f, IsNilpotent x) {n} {e : Fin n -> S} (he : OrthogonalIdempotents e) (he' 
: forall i, e i in f.range) : exists e' : Fin n -> R, OrthogonalIdempotents e' ∧
 f ∘ e' = e
参数：h : forall x in RingHom.ker f, IsNilpotent x；he : OrthogonalIdempotents e；he'
 : forall i, e i in f.range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `OrthogonalIdempotents.embedding`：OrthogonalIdempotents.embedding (he : O
rthogonalIdempotents e) {J} (i : J ↪ I) : OrthogonalIdempotents (e ∘ i)
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent`：exists_isIdempot
entElem_mul_eq_zero_of_ker_isNilpotent (h : forall x in RingHom.ker f, IsNilpote
nt x) (e₁ : S) (he : e₁ in f.range) (he₁ : I…
· 使用定理 `OrthogonalIdempotents.idem`：∀ {R : Type u_1} [inst : Semiring R] {I : Ty
pe u_3} {e : I → R},   OrthogonalIdempotents e → ∀ (i : I), IsIdempotentElem (e 
i)
· 使用引理 `OrthogonalIdempotents.isIdempotentElem_sum`：OrthogonalIdempotents.isIdem
potentElem_sum (he : OrthogonalIdempotents e) {s : Finset I} : IsIdempotentElem 
(∑ i in s, e i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用引理 `OrthogonalIdempotents.mul_eq`：OrthogonalIdempotents.mul_eq [DecidableEq 
I] (he : OrthogonalIdempotents e) (i j) : e i * e j = if i = j then e i else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用引理 `OrthogonalIdempotents.option`：OrthogonalIdempotents.option (he : Orthogo
nalIdempotents e) [Fintype I] (x) (hx : IsIdempotentElem x) (hx₁ : x * ∑ i, e i 
= 0) (hx₂ : (∑ i, …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `finSuccEquiv_symm_none`：finSuccEquiv_symm_none : (finSuccEquiv n).symm n
one = 0
· 使用定理 `finSuccEquiv_symm_some`：finSuccEquiv_symm_some (m : Fin n) : (finSuccEqu
iv n).symm (some m) = m.succ
· 使用定理 `finSuccEquiv_succ`：finSuccEquiv_succ (m : Fin n) : (finSuccEquiv n) m.su
cc = some m
-/
lemma OrthogonalIdempotents.lift_of_isNilpotent_ker_aux
    (h : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    {n} {e : Fin n → S} (he : OrthogonalIdempotents e) (he' : ∀ i, e i ∈ f.range) :
    ∃ e' : Fin n → R, OrthogonalIdempotents e' ∧ f ∘ e' = e := by
  induction n with
  | zero => refine ⟨0, ⟨finZeroElim, finZeroElim⟩, funext finZeroElim⟩
  | succ n IH =>
    obtain ⟨e', h₁, h₂⟩ := IH (he.embedding (Fin.succEmb n)) (fun i ↦ he' _)
    have h₂' (i) : f (e' i) = e i.succ := congr_fun h₂ i
    obtain ⟨e₀, h₃, h₄, h₅, h₆⟩ :=
      exists_isIdempotentElem_mul_eq_zero_of_ker_isNilpotent f h _ (he' 0) (he.idem 0) _
      h₁.isIdempotentElem_sum
      (by simp [Finset.mul_sum, h₂', he.mul_eq, eq_comm])
      (by simp [Finset.sum_mul, h₂', he.mul_eq])
    refine ⟨_, (h₁.option _ h₃ h₅ h₆).embedding (finSuccEquiv n).toEmbedding, funext fun i ↦ ?_⟩
    obtain ⟨_ | i, rfl⟩ := (finSuccEquiv n).symm.surjective i <;> simp [*]

variable {I : Type*} {e : I → R}

/-- A family of orthogonal idempotents lift along nil ideals. -/
/-
**OrthogonalIdempotents.lift_of_isNilpotent_ker** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OrthogonalIdempotents.lift_of_isNilpotent_ker [Finite I] (h : forall x in 
RingHom.ker f, IsNilpotent x) {e : I -> S} (he : OrthogonalIdempotents e) (he' :
 forall i, e i in f.range) : exists e' : I -> R, OrthogonalIdempotents e' ∧ f ∘ 
e' = e
参数：h : forall x in RingHom.ker f, IsNilpotent x；he : OrthogonalIdempotents e；he'
 : forall i, e i in f.range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `OrthogonalIdempotents.lift_of_isNilpotent_ker_aux`：OrthogonalIdempotents
.lift_of_isNilpotent_ker_aux (h : forall x in RingHom.ker f, IsNilpotent x) {n} 
{e : Fin n -> S} (he : OrthogonalIdempo…
· 使用引理 `OrthogonalIdempotents.embedding`：OrthogonalIdempotents.embedding (he : O
rthogonalIdempotents e) {J} (i : J ↪ I) : OrthogonalIdempotents (e ∘ i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a

--- 原说明 ---
A family of orthogonal idempotents lift along nil ideals.
-/
lemma OrthogonalIdempotents.lift_of_isNilpotent_ker [Finite I]
    (h : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    {e : I → S} (he : OrthogonalIdempotents e) (he' : ∀ i, e i ∈ f.range) :
    ∃ e' : I → R, OrthogonalIdempotents e' ∧ f ∘ e' = e := by
  cases nonempty_fintype I
  obtain ⟨e', h₁, h₂⟩ := lift_of_isNilpotent_ker_aux f h
    (he.embedding (Fintype.equivFin I).symm.toEmbedding) (fun _ ↦ he' _)
  refine ⟨_, h₁.embedding (Fintype.equivFin I).toEmbedding,
    by ext x; simpa using congr_fun h₂ (Fintype.equivFin I x)⟩
/-
**CompleteOrthogonalIdempotents.pair_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompleteOrthogonalIdempotents.pair_iff {x y : R} : CompleteOrthogonalIdemp
otents ![x, y] ↔ IsIdempotentElem x ∧ y = 1 - x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompleteOrthogonalIdempotents.pair_iff'ₛ`：∀ {R : Type u_1} [inst : Semir
ing R] {x y : R},   CompleteOrthogonalIdempotents ![x, y] ↔ x * y = 0 ∧ y * x = 
0 ∧ x + y = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_sub_iff_add_eq'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a = b - c ↔ c + a = b
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `and_congr_left_iff`：∀ {a c b : Prop}, (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma CompleteOrthogonalIdempotents.pair_iff {x y : R} :
    CompleteOrthogonalIdempotents ![x, y] ↔ IsIdempotentElem x ∧ y = 1 - x := by
  rw [pair_iff'ₛ, ← eq_sub_iff_add_eq', ← and_assoc, and_congr_left_iff]
  rintro rfl
  simp [mul_sub, sub_mul, IsIdempotentElem, sub_eq_zero, eq_comm]
/-
**CompleteOrthogonalIdempotents.of_isIdempotentElem** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：CompleteOrthogonalIdempotents.of_isIdempotentElem {e : R} (he : IsIdempote
ntElem e) : CompleteOrthogonalIdempotents ![e, 1 - e]
参数：he : IsIdempotentElem e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CompleteOrthogonalIdempotents.pair_iff`：CompleteOrthogonalIdempotents.pa
ir_iff {x y : R} : CompleteOrthogonalIdempotents ![x, y] ↔ IsIdempotentElem x ∧ 
y = 1 - x
-/
lemma CompleteOrthogonalIdempotents.of_isIdempotentElem {e : R} (he : IsIdempotentElem e) :
    CompleteOrthogonalIdempotents ![e, 1 - e] :=
  pair_iff.mpr ⟨he, rfl⟩

variable [Fintype I]
/-
**CompleteOrthogonalIdempotents.option** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompleteOrthogonalIdempotents.option (he : OrthogonalIdempotents e) : Comp
leteOrthogonalIdempotents (Option.elim · (1 - ∑ i, e i) e) where __
参数：he : OrthogonalIdempotents e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `OrthogonalIdempotents.option`：OrthogonalIdempotents.option (he : Orthogo
nalIdempotents e) [Fintype I] (x) (hx : IsIdempotentElem x) (hx₁ : x * ∑ i, e i 
= 0) (hx₂ : (∑ i, …
· 使用引理 `IsIdempotentElem.one_sub`：one_sub (h : IsIdempotentElem a) : IsIdempoten
tElem (1 - a)
· 使用引理 `OrthogonalIdempotents.isIdempotentElem_sum`：OrthogonalIdempotents.isIdem
potentElem_sum (he : OrthogonalIdempotents e) {s : Finset I} : IsIdempotentElem 
(∑ i in s, e i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Fintype.sum_option`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α] [
inst_1 : AddCommMonoid M] (f : Option α → M),   ∑ i, f i = f none + ∑ i, f (some
 i)
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
lemma CompleteOrthogonalIdempotents.option (he : OrthogonalIdempotents e) :
    CompleteOrthogonalIdempotents (Option.elim · (1 - ∑ i, e i) e) where
  __ := he.option _ he.isIdempotentElem_sum.one_sub
    (by simp [sub_mul, he.isIdempotentElem_sum.eq]) (by simp [mul_sub, he.isIdempotentElem_sum.eq])
  complete := by
    rw [Fintype.sum_option]
    exact sub_add_cancel _ _
/-
**CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker_aux** 是 Mathlib 中的一个引理，位
于命名空间 ``。
形式化陈述：CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker_aux (h : forall x in
 RingHom.ker f, IsNilpotent x) {n} {e : Fin n -> S} (he : CompleteOrthogonalIdem
potents e) (he' : forall i, e i in f.range) : exists e' : Fin n -> R, CompleteOr
thogonalIdempotents e' ∧ f ∘ e' = e
参数：h : forall x in RingHom.ker f, IsNilpotent x；he : CompleteOrthogonalIdempoten
ts e；he' : forall i, e i in f.range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用引理 `CompleteOrthogonalIdempotents.of_subsingleton`：CompleteOrthogonalIdempot
ents.of_subsingleton [Subsingleton R] : CompleteOrthogonalIdempotents e
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.finZeroElim_eq_zero`：∀ {α : Type u_1} [inst : Zero α], finZeroEli
m = 0
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `CompleteOrthogonalIdempotents.complete`：∀ {R : Type u_1} [inst : Semirin
g R] {I : Type u_3} [inst_1 : Fintype I] {e : I → R},   CompleteOrthogonalIdempo
tents e → ∑ i, e i = 1
· 使用引理 `OrthogonalIdempotents.lift_of_isNilpotent_ker`：OrthogonalIdempotents.lif
t_of_isNilpotent_ker [Finite I] (h : forall x in RingHom.ker f, IsNilpotent x) {
e : I -> S} (he : OrthogonalIdempot…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CompleteOrthogonalIdempotents.toOrthogonalIdempotents`：∀ {R : Type u_1} 
[inst : Semiring R] {I : Type u_3} [inst_1 : Fintype I] {e : I → R},   CompleteO
rthogonalIdempotents e → OrthogonalIdempote…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CompleteOrthogonalIdempotents.equiv`：CompleteOrthogonalIdempotents.equiv
 {J} [Fintype J] (i : J ≃ I) : CompleteOrthogonalIdempotents (e ∘ i) ↔ CompleteO
rthogonalIdempotents e
· 使用引理 `CompleteOrthogonalIdempotents.option`：CompleteOrthogonalIdempotents.opti
on (he : OrthogonalIdempotents e) : CompleteOrthogonalIdempotents (Option.elim ·
 (1 - ∑ i, e i) e) where _…
· 使用引理 `OrthogonalIdempotents.embedding`：OrthogonalIdempotents.embedding (he : O
rthogonalIdempotents e) {J} (i : J ↪ I) : OrthogonalIdempotents (e ∘ i)
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
（共 38 条，此处仅展示前 30 条）
-/
lemma CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker_aux
    (h : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    {n} {e : Fin n → S} (he : CompleteOrthogonalIdempotents e) (he' : ∀ i, e i ∈ f.range) :
    ∃ e' : Fin n → R, CompleteOrthogonalIdempotents e' ∧ f ∘ e' = e := by
  cases subsingleton_or_nontrivial R
  · choose e' he' using he'
    exact ⟨e', .of_subsingleton, funext he'⟩
  cases subsingleton_or_nontrivial S
  · obtain ⟨n, hn⟩ := h 1 (Subsingleton.elim _ _)
    simp at hn
  rcases n with - | n
  · simpa using he.complete
  obtain ⟨e', h₁, h₂⟩ := OrthogonalIdempotents.lift_of_isNilpotent_ker f h he.1 he'
  refine ⟨_, (equiv (finSuccEquiv n)).mpr
    (CompleteOrthogonalIdempotents.option (h₁.embedding (Fin.succEmb _))), funext fun i ↦ ?_⟩
  have (i : _) : f (e' i) = e i := congr_fun h₂ i
  cases i using Fin.cases with
  | zero => simp [this, Fin.sum_univ_succ, ← he.complete]
  | succ i => simp [this]

/-- A system of complete orthogonal idempotents lift along nil ideals. -/
/-
**CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker (h : forall x in Rin
gHom.ker f, IsNilpotent x) {e : I -> S} (he : CompleteOrthogonalIdempotents e) (
he' : forall i, e i in f.range) : exists e' : I -> R, CompleteOrthogonalIdempote
nts e' ∧ f ∘ e' = e
参数：h : forall x in RingHom.ker f, IsNilpotent x；he : CompleteOrthogonalIdempoten
ts e；he' : forall i, e i in f.range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker_aux`：CompleteOrtho
gonalIdempotents.lift_of_isNilpotent_ker_aux (h : forall x in RingHom.ker f, IsN
ilpotent x) {n} {e : Fin n -> S} (he : Complete…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CompleteOrthogonalIdempotents.equiv`：CompleteOrthogonalIdempotents.equiv
 {J} [Fintype J] (i : J ≃ I) : CompleteOrthogonalIdempotents (e ∘ i) ↔ CompleteO
rthogonalIdempotents e
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a

--- 原说明 ---
A system of complete orthogonal idempotents lift along nil ideals.
-/
lemma CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker
    (h : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    {e : I → S} (he : CompleteOrthogonalIdempotents e) (he' : ∀ i, e i ∈ f.range) :
    ∃ e' : I → R, CompleteOrthogonalIdempotents e' ∧ f ∘ e' = e := by
  obtain ⟨e', h₁, h₂⟩ := lift_of_isNilpotent_ker_aux f h
    ((equiv (Fintype.equivFin I).symm).mpr he) (fun _ ↦ he' _)
  refine ⟨_, ((equiv (Fintype.equivFin I)).mpr h₁),
    by ext x; simpa using congr_fun h₂ (Fintype.equivFin I x)⟩
/-
**eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute {e₁ e₂ : R} (he₁ : Is
IdempotentElem e₁) (he₂ : IsIdempotentElem e₂) (H : IsNilpotent (e₁ - e₂)) (H' :
 Commute e₁ e₂) : e₁ = e₂
参数：he₁ : IsIdempotentElem e₁；he₂ : IsIdempotentElem e₂；H : IsNilpotent (e₁ - e₂)
；H' : Commute e₁ e₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `_private.Mathlib.RingTheory.Idempotents.0.eq_of_isNilpotent_sub_of_isIde
mpotentElem_of_commute._abel_1_2`：∀ {R : Type u_1} [inst : Ring R] {e₁ e₂ : R}, 
  e₁ - e₂ * e₁ - (e₂ * e₁ - e₂ * e₁) - (e₂ * e₁ - e₂ * e₁ - (e₂ * e₁ - e₂)) = e₁
 - e₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
-/
theorem eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute {e₁ e₂ : R}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂) (H : IsNilpotent (e₁ - e₂))
    (H' : Commute e₁ e₂) :
    e₁ = e₂ := by
  have : (e₁ - e₂) ^ 3 = (e₁ - e₂) := by
    simp only [pow_succ, pow_zero, mul_sub, one_mul, sub_mul, he₁.eq, he₂.eq,
      H'.eq, mul_assoc]
    simp only [← mul_assoc, he₂.eq]
    abel
  obtain ⟨n, hn⟩ := H
  have : (e₁ - e₂) ^ (2 * n + 1) = (e₁ - e₂) := by
    clear hn; induction n <;> simp [mul_add, add_assoc, pow_add _ (2 * _) 3, ← pow_succ, *]
  rwa [pow_succ, two_mul, pow_add, hn, zero_mul, zero_mul, eq_comm, sub_eq_zero] at this
/-
**CompleteOrthogonalIdempotents.of_ker_isNilpotent_of_isMulCentral** 是 Mathlib 中
的一个定理，位于命名空间 ``。
形式化陈述：CompleteOrthogonalIdempotents.of_ker_isNilpotent_of_isMulCentral (h : fora
ll x in RingHom.ker f, IsNilpotent x) (he : forall i, IsIdempotentElem (e i)) (h
e' : forall i, IsMulCentral (e i)) (he'' : CompleteOrthogonalIdempotents (f ∘ e)
) : CompleteOrthogonalIdempotents e
参数：h : forall x in RingHom.ker f, IsNilpotent x；he : forall i, IsIdempotentElem 
(e i)；he' : forall i, IsMulCentral (e i)；he'' : CompleteOrthogonalIdempotents (f
 ∘ e)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker`：CompleteOrthogona
lIdempotents.lift_of_isNilpotent_ker (h : forall x in RingHom.ker f, IsNilpotent
 x) {e : I -> S} (he : CompleteOrthogonalId…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute`：eq_of_isNilpotent_
sub_of_isIdempotentElem_of_commute {e₁ e₂ : R} (he₁ : IsIdempotentElem e₁) (he₂ 
: IsIdempotentElem e₂) (H : IsNilpotent (e…
· 使用定理 `OrthogonalIdempotents.idem`：∀ {R : Type u_1} [inst : Semiring R] {I : Ty
pe u_3} {e : I → R},   OrthogonalIdempotents e → ∀ (i : I), IsIdempotentElem (e 
i)
· 使用定理 `CompleteOrthogonalIdempotents.toOrthogonalIdempotents`：∀ {R : Type u_1} 
[inst : Semiring R] {I : Type u_3} [inst_1 : Fintype I] {e : I → R},   CompleteO
rthogonalIdempotents e → OrthogonalIdempote…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
-/
theorem CompleteOrthogonalIdempotents.of_ker_isNilpotent_of_isMulCentral
    (h : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    (he : ∀ i, IsIdempotentElem (e i))
    (he' : ∀ i, IsMulCentral (e i))
    (he'' : CompleteOrthogonalIdempotents (f ∘ e)) :
    CompleteOrthogonalIdempotents e := by
  obtain ⟨e', h₁, h₂⟩ := lift_of_isNilpotent_ker f h he'' (fun _ ↦ ⟨_, rfl⟩)
  obtain rfl : e = e' := by
    ext i
    refine eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute
      (he _) (h₁.idem _) (h _ ?_) ((he' i).comm _)
    simpa [RingHom.mem_ker, sub_eq_zero] using congr_fun h₂.symm i
  exact h₁

end Ring

section CommRing

variable {R S : Type*} [CommRing R] [Ring S] (f : R →+* S)

/-
**eq_of_isNilpotent_sub_of_isIdempotentElem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_isNilpotent_sub_of_isIdempotentElem {e₁ e₂ : R} (he₁ : IsIdempotentE
lem e₁) (he₂ : IsIdempotentElem e₂) (H : IsNilpotent (e₁ - e₂)) : e₁ = e₂
参数：he₁ : IsIdempotentElem e₁；he₂ : IsIdempotentElem e₂；H : IsNilpotent (e₁ - e₂)
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute`：eq_of_isNilpotent_
sub_of_isIdempotentElem_of_commute {e₁ e₂ : R} (he₁ : IsIdempotentElem e₁) (he₂ 
: IsIdempotentElem e₂) (H : IsNilpotent (e…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem eq_of_isNilpotent_sub_of_isIdempotentElem {e₁ e₂ : R}
    (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂) (H : IsNilpotent (e₁ - e₂)) :
    e₁ = e₂ :=
  eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute he₁ he₂ H (.all _ _)

@[stacks 00J9]
/-
**existsUnique_isIdempotentElem_eq_of_ker_isNilpotent** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：existsUnique_isIdempotentElem_eq_of_ker_isNilpotent (h : forall x in RingH
om.ker f, IsNilpotent x) (e : S) (he : e in f.range) (he' : IsIdempotentElem e) 
: exists! e' : R, IsIdempotentElem e' ∧ f e' = e
参数：h : forall x in RingHom.ker f, IsNilpotent x；e : S；he : e in f.range；he' : Is
IdempotentElem e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_isIdempotentElem_eq_of_ker_isNilpotent`：exists_isIdempotentElem_e
q_of_ker_isNilpotent (h : forall x in RingHom.ker f, IsNilpotent x) (e : S) (he 
: e in f.range) (he' : IsIdempotent…
· 使用定理 `eq_of_isNilpotent_sub_of_isIdempotentElem`：eq_of_isNilpotent_sub_of_isId
empotentElem {e₁ e₂ : R} (he₁ : IsIdempotentElem e₁) (he₂ : IsIdempotentElem e₂)
 (H : IsNilpotent (e₁ - e₂)) : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem existsUnique_isIdempotentElem_eq_of_ker_isNilpotent (h : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    (e : S) (he : e ∈ f.range) (he' : IsIdempotentElem e) :
    ∃! e' : R, IsIdempotentElem e' ∧ f e' = e := by
  obtain ⟨e', he₂, rfl⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent f h e he he'
  exact ⟨e', ⟨he₂, rfl⟩, fun x ⟨hx, hx'⟩ ↦
    eq_of_isNilpotent_sub_of_isIdempotentElem hx he₂
      (h _ (by rw [RingHom.mem_ker, map_sub, hx', sub_self]))⟩

/-- A family of orthogonal idempotents induces a surjection `R ≃+* ∏ R ⧸ ⟨1 - eᵢ⟩` -/
/-
**OrthogonalIdempotents.surjective_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OrthogonalIdempotents.surjective_pi {I : Type*} [Finite I] {e : I -> R} (h
e : OrthogonalIdempotents e) : Function.Surjective (RingHom.pi fun i => Ideal.Qu
otient.mk (Ideal.span {1 - e i}))
参数：he : OrthogonalIdempotents e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.isCoprime_span_singleton_iff`：isCoprime_span_singleton_iff (x y : 
R) : IsCoprime (span <| singleton x) (span <| singleton y) ↔ IsCoprime x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `OrthogonalIdempotents.ortho`：∀ {R : Type u_1} [inst : Semiring R] {I : T
ype u_3} {e : I → R},   OrthogonalIdempotents e → Pairwise fun x1 x2 => e x1 * e
 x2 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ideal.instIsTwoSidedIInf`：∀ {α : Type u} [inst : Semiring α] {ι : Sort u
_1} (I : ι → Ideal α) [∀ (i : ι), (I i).IsTwoSided], (⨅ i, I i).IsTwoSided
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `Ideal.quotientInfToPiQuotient_surj`：quotientInfToPiQuotient_surj {I : ι 
-> Ideal R} (hI : Pairwise (IsCoprime on I)) : Surjective (quotientInfToPiQuotie
nt I)
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RingHom.pi_apply`：∀ {I : Type u} {f : I → Type u_1} {γ : Type u_2} [inst
 : (i : I) → NonAssocSemiring (f i)] [inst_1 : NonAssocSemiring γ]   (g : (i : I
) → γ …

--- 原说明 ---
A family of orthogonal idempotents induces a surjection `R ≃+* ∏ R ⧸ ⟨1 - eᵢ⟩`
-/
lemma OrthogonalIdempotents.surjective_pi {I : Type*} [Finite I] {e : I → R}
    (he : OrthogonalIdempotents e) :
    Function.Surjective (RingHom.pi fun i ↦ Ideal.Quotient.mk (Ideal.span {1 - e i})) := by
  suffices Pairwise fun i j ↦ IsCoprime (Ideal.span {1 - e i}) (Ideal.span {1 - e j}) by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.quotientInfToPiQuotient_surj this x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨x, by ext i; simp [Ideal.quotientInfToPiQuotient]⟩
  intro i j hij
  rw [Ideal.isCoprime_span_singleton_iff]
  exact ⟨1, e i, by simp [mul_sub, he.ortho hij]⟩
/-
**OrthogonalIdempotents.prod_one_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OrthogonalIdempotents.prod_one_sub {I : Type*} {e : I -> R} (he : Orthogon
alIdempotents e) (s : Finset I) : ∏ i in s, (1 - e i) = 1 - ∑ i in s, e i
参数：he : OrthogonalIdempotents e；s : Finset I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `OrthogonalIdempotents.mul_sum_of_notMem`：OrthogonalIdempotents.mul_sum_o
f_notMem (he : OrthogonalIdempotents e) {i : I} {s : Finset I} (h : i ∉ s) : e i
 * ∑ j in s, e j = 0
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
-/
lemma OrthogonalIdempotents.prod_one_sub {I : Type*} {e : I → R}
    (he : OrthogonalIdempotents e) (s : Finset I) :
    ∏ i ∈ s, (1 - e i) = 1 - ∑ i ∈ s, e i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    simp [ih, sub_mul, mul_sub, he.mul_sum_of_notMem has, sub_sub]

variable {I : Type*} [Fintype I] {e : I → R}
/-
**CompleteOrthogonalIdempotents.of_ker_isNilpotent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompleteOrthogonalIdempotents.of_ker_isNilpotent (h : forall x in RingHom.
ker f, IsNilpotent x) (he : forall i, IsIdempotentElem (e i)) (he' : CompleteOrt
hogonalIdempotents (f ∘ e)) : CompleteOrthogonalIdempotents e
参数：h : forall x in RingHom.ker f, IsNilpotent x；he : forall i, IsIdempotentElem 
(e i)；he' : CompleteOrthogonalIdempotents (f ∘ e)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteOrthogonalIdempotents.of_ker_isNilpotent_of_isMulCentral`：Comple
teOrthogonalIdempotents.of_ker_isNilpotent_of_isMulCentral (h : forall x in Ring
Hom.ker f, IsNilpotent x) (he : forall i, IsIdempotent…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Semigroup.mem_center_iff`：∀ {M : Type u_1} [inst : Semigroup M] {z : M},
 z ∈ Set.center M ↔ ∀ (g : M), g * z = z * g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem CompleteOrthogonalIdempotents.of_ker_isNilpotent (h : ∀ x ∈ RingHom.ker f, IsNilpotent x)
    (he : ∀ i, IsIdempotentElem (e i))
    (he' : CompleteOrthogonalIdempotents (f ∘ e)) :
    CompleteOrthogonalIdempotents e :=
  of_ker_isNilpotent_of_isMulCentral f h he
    (fun _ ↦ Semigroup.mem_center_iff.mpr (mul_comm · _)) he'
/-
**CompleteOrthogonalIdempotents.prod_one_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompleteOrthogonalIdempotents.prod_one_sub (he : CompleteOrthogonalIdempot
ents e) : ∏ i, (1 - e i) = 0
参数：he : CompleteOrthogonalIdempotents e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `OrthogonalIdempotents.prod_one_sub`：OrthogonalIdempotents.prod_one_sub {
I : Type*} {e : I -> R} (he : OrthogonalIdempotents e) (s : Finset I) : ∏ i in s
, (1 - e i) = 1 - ∑ i in…
· 使用定理 `CompleteOrthogonalIdempotents.toOrthogonalIdempotents`：∀ {R : Type u_1} 
[inst : Semiring R] {I : Type u_3} [inst_1 : Fintype I] {e : I → R},   CompleteO
rthogonalIdempotents e → OrthogonalIdempote…
· 使用定理 `CompleteOrthogonalIdempotents.complete`：∀ {R : Type u_1} [inst : Semirin
g R] {I : Type u_3} [inst_1 : Fintype I] {e : I → R},   CompleteOrthogonalIdempo
tents e → ∑ i, e i = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
lemma CompleteOrthogonalIdempotents.prod_one_sub
    (he : CompleteOrthogonalIdempotents e) :
    ∏ i, (1 - e i) = 0 := by
  rw [he.1.prod_one_sub, he.complete, sub_self]
/-
**CompleteOrthogonalIdempotents.of_prod_one_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompleteOrthogonalIdempotents.of_prod_one_sub (he : OrthogonalIdempotents 
e) (he' : ∏ i, (1 - e i) = 0) : CompleteOrthogonalIdempotents e where __
参数：he : OrthogonalIdempotents e；he' : ∏ i, (1 - e i) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用引理 `OrthogonalIdempotents.prod_one_sub`：OrthogonalIdempotents.prod_one_sub {
I : Type*} {e : I -> R} (he : OrthogonalIdempotents e) (s : Finset I) : ∏ i in s
, (1 - e i) = 1 - ∑ i in…
-/
lemma CompleteOrthogonalIdempotents.of_prod_one_sub
    (he : OrthogonalIdempotents e) (he' : ∏ i, (1 - e i) = 0) :
    CompleteOrthogonalIdempotents e where
  __ := he
  complete := by rwa [he.prod_one_sub, sub_eq_zero, eq_comm] at he'

/-- A family of complete orthogonal idempotents induces an isomorphism `R ≃+* ∏ R ⧸ ⟨1 - eᵢ⟩` -/
/-
**CompleteOrthogonalIdempotents.bijective_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompleteOrthogonalIdempotents.bijective_pi (he : CompleteOrthogonalIdempot
ents e) : Function.Bijective (RingHom.pi fun i => Ideal.Quotient.mk (Ideal.span 
{1 - e i}))
参数：he : CompleteOrthogonalIdempotents e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `RingHom.pi_apply`：∀ {I : Type u} {f : I → Type u_1} {γ : Type u_2} [inst
 : (i : I) → NonAssocSemiring (f i)] [inst_1 : NonAssocSemiring γ]   (g : (i : I
) → γ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用引理 `IsIdempotentElem.one_sub`：one_sub (h : IsIdempotentElem a) : IsIdempoten
tElem (1 - a)
· 使用定理 `OrthogonalIdempotents.idem`：∀ {R : Type u_1} [inst : Semiring R] {I : Ty
pe u_3} {e : I → R},   OrthogonalIdempotents e → ∀ (i : I), IsIdempotentElem (e 
i)
· 使用定理 `CompleteOrthogonalIdempotents.toOrthogonalIdempotents`：∀ {R : Type u_1} 
[inst : Semiring R] {I : Type u_3} [inst_1 : Fintype I] {e : I → R},   CompleteO
rthogonalIdempotents e → OrthogonalIdempote…
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `CompleteOrthogonalIdempotents.prod_one_sub`：CompleteOrthogonalIdempotent
s.prod_one_sub (he : CompleteOrthogonalIdempotents e) : ∏ i, (1 - e i) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `OrthogonalIdempotents.surjective_pi`：OrthogonalIdempotents.surjective_pi
 {I : Type*} [Finite I] {e : I -> R} (he : OrthogonalIdempotents e) : Function.S
urjective (RingHom.pi fun…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
A family of complete orthogonal idempotents induces an isomorphism `R ≃+* ∏ R ⧸ 
⟨1 - eᵢ⟩`
-/
lemma CompleteOrthogonalIdempotents.bijective_pi (he : CompleteOrthogonalIdempotents e) :
    Function.Bijective (RingHom.pi fun i ↦ Ideal.Quotient.mk (Ideal.span {1 - e i})) := by
  classical
  refine ⟨?_, he.1.surjective_pi⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  simp only [funext_iff, RingHom.pi_apply, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hx
  suffices ∀ s : Finset I, (∏ i ∈ s, (1 - e i)) * x = x by
    rw [← this Finset.univ, he.prod_one_sub, zero_mul]
  refine fun s ↦ Finset.induction_on s (by simp) ?_
  intro a s has e'
  suffices (1 - e a) * x = x by simp [has, mul_assoc, e', this]
  obtain ⟨c, rfl⟩ := hx a
  rw [← mul_assoc, (he.idem a).one_sub.eq]
/-
**CompleteOrthogonalIdempotents.bijective_pi'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompleteOrthogonalIdempotents.bijective_pi' (he : CompleteOrthogonalIdempo
tents (1 - e ·)) : Function.Bijective (RingHom.pi fun i => Ideal.Quotient.mk (Id
eal.span {e i}))
参数：he : CompleteOrthogonalIdempotents (1 - e ·)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `CompleteOrthogonalIdempotents.bijective_pi`：CompleteOrthogonalIdempotent
s.bijective_pi (he : CompleteOrthogonalIdempotents e) : Function.Bijective (Ring
Hom.pi fun i => Ideal.Quotient.m…
-/
lemma CompleteOrthogonalIdempotents.bijective_pi' (he : CompleteOrthogonalIdempotents (1 - e ·)) :
    Function.Bijective (RingHom.pi fun i ↦ Ideal.Quotient.mk (Ideal.span {e i})) := by
  obtain ⟨e', rfl, h⟩ : ∃ e' : I → R, (e' = e) ∧ Function.Bijective (RingHom.pi fun i ↦
      Ideal.Quotient.mk (Ideal.span {e' i})) := ⟨_, funext (by simp), he.bijective_pi⟩
  exact h
/-
**RingHom.pi_bijective_of_isIdempotentElem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.pi_bijective_of_isIdempotentElem (e : I -> R) (he : forall i, IsId
empotentElem (e i)) (he₁ : forall i j, i != j -> (1 - e i) * (1 - e j) = 0) (he₂
 : ∏ i, e i = 0) : Function.Bijective (RingHom.pi fun i => Ideal.Quotient.mk (Id
eal.span {e i}))
参数：e : I -> R；he : forall i, IsIdempotentElem (e i)；he₁ : forall i j, i != j -> 
(1 - e i) * (1 - e j) = 0；he₂ : ∏ i, e i = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CompleteOrthogonalIdempotents.bijective_pi'`：CompleteOrthogonalIdempoten
ts.bijective_pi' (he : CompleteOrthogonalIdempotents (1 - e ·)) : Function.Bijec
tive (RingHom.pi fun i => Ideal.Q…
· 使用引理 `CompleteOrthogonalIdempotents.of_prod_one_sub`：CompleteOrthogonalIdempot
ents.of_prod_one_sub (he : OrthogonalIdempotents e) (he' : ∏ i, (1 - e i) = 0) :
 CompleteOrthogonalIdempotents e wh…
· 使用引理 `IsIdempotentElem.one_sub`：one_sub (h : IsIdempotentElem a) : IsIdempoten
tElem (1 - a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
-/
lemma RingHom.pi_bijective_of_isIdempotentElem (e : I → R)
    (he : ∀ i, IsIdempotentElem (e i))
    (he₁ : ∀ i j, i ≠ j → (1 - e i) * (1 - e j) = 0) (he₂ : ∏ i, e i = 0) :
    Function.Bijective (RingHom.pi fun i ↦ Ideal.Quotient.mk (Ideal.span {e i})) :=
  (CompleteOrthogonalIdempotents.of_prod_one_sub
      ⟨fun i ↦ (he i).one_sub, he₁⟩ (by simpa using he₂)).bijective_pi'
/-
**RingHom.prod_bijective_of_isIdempotentElem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.prod_bijective_of_isIdempotentElem {e f : R} (he : IsIdempotentEle
m e) (hf : IsIdempotentElem f) (hef₁ : e + f = 1) (hef₂ : e * f = 0) : Function.
Bijective ((Ideal.Quotient.mk <| Ideal.span {e}).prod (Ideal.Quotient.mk <| Idea
l.span {f}))
参数：he : IsIdempotentElem e；hf : IsIdempotentElem f；hef₁ : e + f = 1；hef₂ : e * f
 = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用引理 `RingHom.pi_bijective_of_isIdempotentElem`：RingHom.pi_bijective_of_isIdem
potentElem (e : I -> R) (he : forall i, IsIdempotentElem (e i)) (he₁ : forall i 
j, i != j -> (1 - e i) * (1 - …
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Fin.prod_univ_two`：prod_univ_two (f : Fin 2 -> M) : ∏ i, f i = f 0 * f 1
-/
lemma RingHom.prod_bijective_of_isIdempotentElem {e f : R} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) (hef₁ : e + f = 1) (hef₂ : e * f = 0) :
    Function.Bijective ((Ideal.Quotient.mk <| Ideal.span {e}).prod
      (Ideal.Quotient.mk <| Ideal.span {f})) := by
  let o (i : Fin 2) : R := match i with
    | 0 => e
    | 1 => f
  change Function.Bijective
    (piFinTwoEquiv _ ∘ RingHom.pi (fun i : Fin 2 ↦ Ideal.Quotient.mk (Ideal.span {o i})))
  rw [(Equiv.bijective _).of_comp_iff']
  apply pi_bijective_of_isIdempotentElem
  · intro i
    fin_cases i <;> simpa [o]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      simp [o, mul_comm, hef₂, ← hef₁]
  · simpa

variable (R) in
/-- If `e` and `f` are idempotent elements such that `e + f = 1` and `e * f = 0`,
`S` is isomorphic as an `R`-algebra to `S ⧸ (e) × S ⧸ (f)`. -/
@[simps! -isSimp apply, simps! apply_fst apply_snd]
/-
**AlgEquiv.prodQuotientOfIsIdempotentElem** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgEquiv.prodQuotientOfIsIdempotentElem {S : Type*} [CommRing S] [Algebra 
R S] {e f : S} (he : IsIdempotentElem e) (hf : IsIdempotentElem f) (hef₁ : e + f
 = 1) (hef₂ : e * f = 0) : S ≃ₐ[R] (S ⧸ Ideal.span {e}) × S ⧸ Ideal.span {f}
参数：he : IsIdempotentElem e；hf : IsIdempotentElem f；hef₁ : e + f = 1；hef₂ : e * f
 = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.prod_bijective_of_isIdempotentElem`：RingHom.prod_bijective_of_is
IdempotentElem {e f : R} (he : IsIdempotentElem e) (hf : IsIdempotentElem f) (he
f₁ : e + f = 1) (hef₂ : e * f = …

--- 原说明 ---
If `e` and `f` are idempotent elements such that `e + f = 1` and `e * f = 0`,
`S` is isomorphic as an `R`-algebra to `S ⧸ (e) × S ⧸ (f)`.
-/
noncomputable def AlgEquiv.prodQuotientOfIsIdempotentElem
    {S : Type*} [CommRing S] [Algebra R S] {e f : S} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) (hef₁ : e + f = 1) (hef₂ : e * f = 0) :
    S ≃ₐ[R] (S ⧸ Ideal.span {e}) × S ⧸ Ideal.span {f} :=
  AlgEquiv.ofBijective ((Ideal.Quotient.mkₐ _ _).prod (Ideal.Quotient.mkₐ _ _)) <|
    RingHom.prod_bijective_of_isIdempotentElem he hf hef₁ hef₂

/-- One can lift a family of complete orthogonal idempotents of `R/e₀` to get one on `R`.

Note that the lemma itself is stated in terms of surjections (where `T = S / I`)
instead for syntactic generality. -/
/-
**CompleteOrthogonalIdempotents.exists_eq_comp_of_ker_eq_span** 是 Mathlib 中的一个引理
，位于命名空间 ``。
形式化陈述：CompleteOrthogonalIdempotents.exists_eq_comp_of_ker_eq_span (f : R ->+* S)
 (e₀ : R) (he₀ : IsIdempotentElem e₀) (hfe₀ : RingHom.ker f = .span {e₀}) (e : I
 -> S) (he : CompleteOrthogonalIdempotents e) (hef : forall i, e i in f.range) :
 exists e', CompleteOrthogonalIdempotents (Option.rec e₀ e') ∧ e = f ∘ e'
参数：f : R ->+* S；e₀ : R；he₀ : IsIdempotentElem e₀；hfe₀ : RingHom.ker f = .span {e
₀}；e : I -> S；he : CompleteOrthogonalIdempotents e；hef : forall i, e i in f.rang
e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
（共 92 条，此处仅展示前 30 条）

--- 原说明 ---
One can lift a family of complete orthogonal idempotents of `R/e₀` to get one on
 `R`.

Note that the lemma itself is stated in terms of surjections (where `T = S / I`)
instead for syntactic generality.
-/
lemma CompleteOrthogonalIdempotents.exists_eq_comp_of_ker_eq_span
    (f : R →+* S) (e₀ : R) (he₀ : IsIdempotentElem e₀) (hfe₀ : RingHom.ker f = .span {e₀})
    (e : I → S) (he : CompleteOrthogonalIdempotents e) (hef : ∀ i, e i ∈ f.range) :
    ∃ e', CompleteOrthogonalIdempotents (Option.rec e₀ e') ∧ e = f ∘ e' := by
  choose e' he' using hef
  choose k hk using fun i ↦ Ideal.mem_span_singleton.mp
      (hfe₀.le (show f (e' i * e' i - e' i) = 0 by simp [he', (he.1.1 i).eq]))
  refine ⟨(1 - e₀) • e', ⟨⟨Option.rec he₀ fun i ↦ ?_, ?_⟩, ?_⟩, ?_⟩
  · rintro (_|i) (_|j) h
    · simp at h
    · dsimp; linear_combination - he₀.eq * e' j
    · dsimp; linear_combination - he₀.eq * e' i
    · obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp
        (hfe₀.le (show f (e' i * e' j) = 0 by simp [he', he.1.2 (by simpa using h)]))
      dsimp
      rw [mul_mul_mul_comm, hk, he₀.one_sub.eq, ← mul_assoc, he₀.one_sub_mul_self, zero_mul]
  · obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp
      (hfe₀.le (show f (∑ i, e' i - 1) = 0 by simpa [he', sub_eq_zero] using he.2))
    simp only [Fintype.sum_option, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
      sub_eq_iff_eq_add.mp hk]
    linear_combination - he₀.eq * k
  · have : f e₀ = 0 := by simpa using hfe₀.ge (Ideal.mem_span_singleton_self _)
    aesop
  · dsimp [IsIdempotentElem]
    linear_combination congr($(he₀.eq) * ((e' i) ^ 2 - k i) + (1 - e₀) * $(hk i))

end CommRing

section corner

variable {R : Type*} (e : R)

namespace Subsemigroup

variable [Semigroup R]

/-- The corner associated to an element `e` in a semigroup
is the subsemigroup of all elements of the form `e * r * e`. -/
/-
**Subsemigroup.corner** 是 Mathlib 中的一个定义，位于命名空间 `Subsemigroup`。
形式化陈述：corner : Subsemigroup R where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The corner associated to an element `e` in a semigroup
is the subsemigroup of all elements of the form `e * r * e`.
-/
def corner : Subsemigroup R where
  carrier := Set.range (e * · * e)
  mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * e * e * b, by simp_rw [mul_assoc]⟩

variable {e} (idem : IsIdempotentElem e)
include idem
/-
**Subsemigroup.mem_corner_iff** 是 Mathlib 中的一个引理，位于命名空间 `Subsemigroup`。
形式化陈述：mem_corner_iff {r : R} : r in corner e ↔ e * r = r ∧ r * e = r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma mem_corner_iff {r : R} : r ∈ corner e ↔ e * r = r ∧ r * e = r :=
  ⟨by rintro ⟨r, rfl⟩; simp_rw [← mul_assoc, idem.eq, mul_assoc, idem.eq, true_and],
    (⟨r, by simp_rw [·]⟩)⟩
/-
**Subsemigroup.mem_corner_iff_mul_left** 是 Mathlib 中的一个引理，位于命名空间 `Subsemigroup`。
形式化陈述：mem_corner_iff_mul_left (hc : IsMulCentral e) {r : R} : r in corner e ↔ e 
* r = r
参数：hc : IsMulCentral e。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subsemigroup.mem_corner_iff`：mem_corner_iff {r : R} : r in corner e ↔ e 
* r = r ∧ r * e = r
· 使用定理 `and_iff_left_of_imp`：∀ {a b : Prop}, (a → b) → (a ∧ b ↔ a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_corner_iff_mul_left (hc : IsMulCentral e) {r : R} : r ∈ corner e ↔ e * r = r := by
  rw [mem_corner_iff idem, and_iff_left_of_imp]; intro; rwa [← hc.comm]
/-
**Subsemigroup.mem_corner_iff_mul_right** 是 Mathlib 中的一个引理，位于命名空间 `Subsemigroup`
。
形式化陈述：mem_corner_iff_mul_right (hc : IsMulCentral e) {r : R} : r in corner e ↔ r
 * e = r
参数：hc : IsMulCentral e。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subsemigroup.mem_corner_iff_mul_left`：mem_corner_iff_mul_left (hc : IsMu
lCentral e) {r : R} : r in corner e ↔ e * r = r
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_corner_iff_mul_right (hc : IsMulCentral e) {r : R} : r ∈ corner e ↔ r * e = r := by
  rw [mem_corner_iff_mul_left idem hc, hc.comm]
/-
**Subsemigroup.mem_corner_iff_mem_range_mul_left** 是 Mathlib 中的一个引理，位于命名空间 `Subs
emigroup`。
形式化陈述：mem_corner_iff_mem_range_mul_left (hc : IsMulCentral e) {r : R} : r in cor
ner e ↔ r in Set.range (e * ·)
参数：hc : IsMulCentral e。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_corner_iff_mem_range_mul_left (hc : IsMulCentral e) {r : R} :
    r ∈ corner e ↔ r ∈ Set.range (e * ·) := by
  simp_rw [corner, mem_mk, Set.mem_range, ← (hc.comm _).eq, ← mul_assoc, idem.eq]
/-
**Subsemigroup.mem_corner_iff_mem_range_mul_right** 是 Mathlib 中的一个引理，位于命名空间 `Sub
semigroup`。
形式化陈述：mem_corner_iff_mem_range_mul_right (hc : IsMulCentral e) {r : R} : r in co
rner e ↔ r in Set.range (· * e)
参数：hc : IsMulCentral e。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subsemigroup.mem_corner_iff_mem_range_mul_left`：mem_corner_iff_mem_range
_mul_left (hc : IsMulCentral e) {r : R} : r in corner e ↔ r in Set.range (e * ·)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_corner_iff_mem_range_mul_right (hc : IsMulCentral e) {r : R} :
    r ∈ corner e ↔ r ∈ Set.range (· * e) := by
  simp_rw [mem_corner_iff_mem_range_mul_left idem hc, (hc.comm _).eq]

/-- The corner associated to an idempotent `e` in a semiring without 1
is the semiring with `e` as 1 consisting of all element of the form `e * r * e`. -/
@[nolint unusedArguments]
/-
**Subsemigroup._root_.IsIdempotentElem.Corner** 是 Mathlib 中的一个定义，位于命名空间 `Subsemi
group`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The corner associated to an idempotent `e` in a semiring without 1
is the semiring with `e` as 1 consisting of all element of the form `e * r * e`.
-/
def _root_.IsIdempotentElem.Corner (_ : IsIdempotentElem e) : Type _ := Subsemigroup.corner e

end Subsemigroup

/-- The corner associated to an element `e` in a semiring without 1
is the subsemiring without 1 of all elements of the form `e * r * e`. -/
/-
**NonUnitalSubsemiring.corner** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NonUnitalSubsemiring.corner [NonUnitalSemiring R] : NonUnitalSubsemiring R
 where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The corner associated to an element `e` in a semiring without 1
is the subsemiring without 1 of all elements of the form `e * r * e`.
-/
def NonUnitalSubsemiring.corner [NonUnitalSemiring R] : NonUnitalSubsemiring R where
  __ := Subsemigroup.corner e
  add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, by simp_rw [mul_add, add_mul]⟩
  zero_mem' := ⟨0, by simp_rw [mul_zero, zero_mul]⟩

/-- The corner associated to an element `e` in a ring without 1
is the subring without 1 of all elements of the form `e * r * e`. -/
/-
**NonUnitalRing.corner** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：NonUnitalRing.corner [NonUnitalRing R] : NonUnitalSubring R where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The corner associated to an element `e` in a ring without 1
is the subring without 1 of all elements of the form `e * r * e`.
-/
def NonUnitalRing.corner [NonUnitalRing R] : NonUnitalSubring R where
  __ := NonUnitalSubsemiring.corner e
  neg_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨-a, by simp_rw [mul_neg, neg_mul]⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalSemiring R] (idem : IsIdempotentElem e) : Semiring idem.Corner where
  __ : NonUnitalSemiring idem.Corner :=
    inferInstanceAs <| NonUnitalSemiring (NonUnitalSubsemiring.corner e)
  one := ⟨e, e, by simp_rw [idem.eq]⟩
  one_mul r := Subtype.ext ((Subsemigroup.mem_corner_iff idem).mp r.2).1
  mul_one r := Subtype.ext ((Subsemigroup.mem_corner_iff idem).mp r.2).2
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalCommSemiring R] (idem : IsIdempotentElem e) : CommSemiring idem.Corner where
  __ : Semiring idem.Corner := inferInstance
  __ : NonUnitalCommSemiring idem.Corner :=
    inferInstanceAs <| NonUnitalCommSemiring (NonUnitalSubsemiring.corner e)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalRing R] (idem : IsIdempotentElem e) : Ring idem.Corner where
  __ : Semiring idem.Corner := inferInstance
  __ : NonUnitalRing idem.Corner := inferInstanceAs <| NonUnitalRing (NonUnitalRing.corner e)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalCommRing R] (idem : IsIdempotentElem e) : CommRing idem.Corner where
  __ : Ring idem.Corner := inferInstance
  __ : NonUnitalCommRing idem.Corner :=
    inferInstanceAs <| NonUnitalCommRing (NonUnitalRing.corner e)

variable {I : Type*} [Fintype I] {e : I → R}

/-- A complete orthogonal family of central idempotents in a semiring
give rise to a direct product decomposition. -/
/-
**CompleteOrthogonalIdempotents.ringEquivOfIsMulCentral** 是 Mathlib 中的一个定义，位于命名空
间 ``。
形式化陈述：CompleteOrthogonalIdempotents.ringEquivOfIsMulCentral [Semiring R] (he : C
ompleteOrthogonalIdempotents e) (hc : forall i, IsMulCentral (e i)) : R ≃+* Π i,
 (he.idem i).Corner where toFun r i
参数：he : CompleteOrthogonalIdempotents e；hc : forall i, IsMulCentral (e i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complete orthogonal family of central idempotents in a semiring
give rise to a direct product decomposition.
-/
def CompleteOrthogonalIdempotents.ringEquivOfIsMulCentral [Semiring R]
    (he : CompleteOrthogonalIdempotents e) (hc : ∀ i, IsMulCentral (e i)) :
    R ≃+* Π i, (he.idem i).Corner where
  toFun r i := ⟨_, r, rfl⟩
  invFun r := ∑ i, (r i).1
  left_inv r := by
    simp_rw [((hc _).comm _).eq, mul_assoc, (he.idem _).eq, ← Finset.mul_sum, he.complete, mul_one]
  right_inv r := funext fun i ↦ Subtype.ext <| by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_eq_single i _ (by simp at ·)]
    · have ⟨r', eq⟩ := (r i).2
      rw [← eq]; simp_rw [← mul_assoc, (he.idem i).eq, mul_assoc, (he.idem i).eq]
    · intro j _ ne; have ⟨r', eq⟩ := (r j).2
      rw [← eq]; simp_rw [← mul_assoc, he.ortho ne.symm, zero_mul]
  map_mul' r₁ r₂ := funext fun i ↦ Subtype.ext <|
    calc e i * (r₁ * r₂) * e i
     _ = e i * (r₁ * e i * r₂) * e i := by
       simp_rw [← ((hc i).comm r₁).eq, ← mul_assoc, (he.idem i).eq]
     _ = e i * r₁ * e i * (e i * r₂ * e i) := by
      conv in (r₁ * _ * r₂) => rw [← (he.idem i).eq]
      simp_rw [mul_assoc]
  map_add' r₁ r₂ := funext fun i ↦ Subtype.ext <| by simpa [mul_add] using! add_mul ..

/-- A complete orthogonal family of idempotents in a commutative semiring
give rise to a direct product decomposition. -/
/-
**CompleteOrthogonalIdempotents.ringEquivOfComm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CompleteOrthogonalIdempotents.ringEquivOfComm [CommSemiring R] (he : Compl
eteOrthogonalIdempotents e) : R ≃+* Π i, (he.idem i).Corner
参数：he : CompleteOrthogonalIdempotents e。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complete orthogonal family of idempotents in a commutative semiring
give rise to a direct product decomposition.
-/
def CompleteOrthogonalIdempotents.ringEquivOfComm [CommSemiring R]
    (he : CompleteOrthogonalIdempotents e) : R ≃+* Π i, (he.idem i).Corner :=
  he.ringEquivOfIsMulCentral fun _ ↦ Semigroup.mem_center_iff.mpr fun _ ↦ mul_comm ..
/-
**Ideal.mem_map_span_singleton_iff_of_isIdempotentElem** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：Ideal.mem_map_span_singleton_iff_of_isIdempotentElem [CommRing R] {e r : R
} (he : IsIdempotentElem e) {I : Ideal R} : Ideal.Quotient.mk _ r in I.map (Idea
l.Quotient.mk (Ideal.span {e})) ↔ (1 - e) * r in I
参数：he : IsIdempotentElem e。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.mem_map_iff_of_surjective`：mem_map_iff_of_surjective {I : Ideal R}
 {y} : y in map f I ↔ exists x, x in I ∧ f x = y
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.add_eq_eq`：add_eq_eq [Add α] (p₁ : (a₁ 
: α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂
· 使用定理 `Mathlib.Tactic.LinearCombination.mul_eq_const`：mul_eq_const [Mul α] (p :
 a = b) (c : α) : a * c = b * c
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `Mathlib.Tactic.LinearCombination.mul_const_eq`：mul_const_eq [Mul α] (p :
 b = c) (a : α) : a * b = a * c
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
（共 59 条，此处仅展示前 30 条）
-/
lemma Ideal.mem_map_span_singleton_iff_of_isIdempotentElem
    [CommRing R] {e r : R} (he : IsIdempotentElem e) {I : Ideal R} :
    Ideal.Quotient.mk _ r ∈ I.map (Ideal.Quotient.mk (Ideal.span {e})) ↔ (1 - e) * r ∈ I := by
  simp only [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton]
  refine ⟨?_, fun H ↦ ⟨_, H, by simp [sub_mul]⟩⟩
  intro ⟨s, hs, t, hrst⟩
  convert I.mul_mem_left (1 - e) hs using 1
  linear_combination he.eq * t - (1 - e) * hrst

end corner

