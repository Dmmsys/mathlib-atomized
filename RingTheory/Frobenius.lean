/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.Unramified.Locus

/-!
# Frobenius elements

In algebraic number theory, if `L/K` is a finite Galois extension of number fields, with rings of
integers `𝓞L/𝓞K`, and if `q` is prime ideal of `𝓞L` lying over a prime ideal `p` of `𝓞K`, then
there exists a **Frobenius element** `Frob p` in `Gal(L/K)` with the property that
`Frob p x ≡ x ^ #(𝓞K/p) (mod q)` for all `x ∈ 𝓞L`.

Following `Mathlib/RingTheory/Invariant/Basic.lean`, we develop the theory in the setting that
there is a finite group `G` acting on a ring `S`, and `R` is the fixed subring of `S`.

## Main results

Let `S/R` be an extension of rings, `Q` be a prime of `S`,
and `P := R ∩ Q` with finite residue field of cardinality `q`.

- `AlgHom.IsArithFrobAt`: We say that a `φ : S →ₐ[R] S` is an (arithmetic) Frobenius at `Q`
  if `φ x ≡ x ^ q (mod Q)` for all `x : S`.
- `AlgHom.IsArithFrobAt.apply_of_pow_eq_one`:
  Suppose `S` is a domain and `φ` is a Frobenius at `Q`,
  then `φ ζ = ζ ^ q` for any `m`-th root of unity `ζ` with `q ∤ m`.
- `AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`:
  Suppose `S` is Noetherian, `Q` contains all zero-divisors, and the extension is unramified at `Q`.
  Then the Frobenius is unique (if exists).

Let `G` be a finite group acting on a ring `S`, and `R` is the fixed subring of `S`.

- `IsArithFrobAt`: We say that a `σ : G` is an (arithmetic) Frobenius at `Q`
  if `σ • x ≡ x ^ q (mod Q)` for all `x : S`.
- `IsArithFrobAt.mul_inv_mem_inertia`:
  Two Frobenius elements at `Q` differ by an element in the inertia subgroup of `Q`.
- `IsArithFrobAt.conj`: If `σ` is a Frobenius at `Q`, then `τστ⁻¹` is a Frobenius at `σ • Q`.
- `IsArithFrobAt.exists_of_isInvariant`: Frobenius element exists.
-/

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- `φ : S →ₐ[R] S` is an (arithmetic) Frobenius at `Q` if
`φ x ≡ x ^ #(R/p) (mod Q)` for all `x : S` (`AlgHom.IsArithFrobAt`). -/
/-
**AlgHom.IsArithFrobAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgHom.IsArithFrobAt (φ : S ->ₐ[R] S) (Q : Ideal S) : Prop
参数：φ : S ->ₐ[R] S；Q : Ideal S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`φ : S →ₐ[R] S` is an (arithmetic) Frobenius at `Q` if
`φ x ≡ x ^ #(R/p) (mod Q)` for all `x : S` (`AlgHom.IsArithFrobAt`).
-/
def AlgHom.IsArithFrobAt (φ : S →ₐ[R] S) (Q : Ideal S) : Prop :=
  ∀ x, φ x - x ^ Nat.card (R ⧸ Q.under R) ∈ Q

namespace AlgHom.IsArithFrobAt

variable {φ ψ : S →ₐ[R] S} {Q : Ideal S} (H : φ.IsArithFrobAt Q)

include H

/-
**AlgHom.IsArithFrobAt.mk_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom.IsArithFrobAt`
。
形式化陈述：mk_apply (x) : Ideal.Quotient.mk Q (φ x) = x ^ Nat.card (R ⧸ Q.under R)
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Ideal.Quotient.eq`：∀ {R : Type u} [inst : Ring R] {I : Ideal R} {x y : R
} [inst_1 : I.IsTwoSided],   (Ideal.Quotient.mk I) x = (Ideal.Quotient.mk I) y ↔
 x - y …
-/
lemma mk_apply (x) : Ideal.Quotient.mk Q (φ x) = x ^ Nat.card (R ⧸ Q.under R) := by
  rw [← map_pow, Ideal.Quotient.eq]
  exact H x
/-
**AlgHom.IsArithFrobAt.finite_quotient** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom.IsArith
FrobAt`。
形式化陈述：finite_quotient : _root_.Finite (R ⧸ Q.under R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `not_finite`：not_finite (α : Sort*) [Infinite α] [Finite α] : False
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.comap_top`：comap_top : (⊤ : Ideal S).comap f = ⊤
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `NonUnitalSubringClass.toNegMemClass`：∀ {S : Type u_1} {R : Type u} {inst
 : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUnitalSubringCla
ss S R], NegMemClass S R
· 使用定理 `instNonUnitalSubringClassIdeal`：∀ {R : Type u_1} [inst : Ring R], NonUni
talSubringClass (Ideal R) R
-/
lemma finite_quotient : _root_.Finite (R ⧸ Q.under R) := by
  by_contra! h
  obtain rfl : Q = ⊤ := by simpa [Nat.card_eq_zero_of_infinite, ← Ideal.eq_top_iff_one] using H 0
  simp only [Ideal.comap_top] at h
  exact not_finite (R ⧸ (⊤ : Ideal R))
/-
**AlgHom.IsArithFrobAt.card_pos** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom.IsArithFrobAt`
。
形式化陈述：card_pos : 0 < Nat.card (R ⧸ Q.under R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgHom.IsArithFrobAt.finite_quotient`：finite_quotient : _root_.Finite (R
 ⧸ Q.under R)
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `Ideal.Quotient.instNonemptyQuotient`：∀ {R : Type u} [inst : Ring R] {I :
 Ideal R} [I.IsTwoSided], Nonempty (R ⧸ I)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
lemma card_pos : 0 < Nat.card (R ⧸ Q.under R) :=
  have := H.finite_quotient
  Nat.card_pos
/-
**AlgHom.IsArithFrobAt.le_comap** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom.IsArithFrobAt`
。
形式化陈述：le_comap : Q <= Q.comap φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgHom.IsArithFrobAt.mk_apply`：mk_apply (x) : Ideal.Quotient.mk Q (φ x) 
= x ^ Nat.card (R ⧸ Q.under R)
· 使用引理 `zero_pow_eq`：zero_pow_eq (n : Nat) : (0 : M₀) ^ n = if n = 0 then 1 else
 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `AlgHom.IsArithFrobAt.card_pos`：card_pos : 0 < Nat.card (R ⧸ Q.under R)
· 使用定理 `false_implies`：∀ (p : Prop), (False → p) = True
-/
lemma le_comap : Q ≤ Q.comap φ := by
  intro x hx
  simp_all only [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem (I := Q), H.mk_apply,
    zero_pow_eq, ite_eq_right_iff, H.card_pos.ne', false_implies]

/-- A Frobenius element at `Q` restricts to the Frobenius map on `S ⧸ Q`. -/
/-
**AlgHom.IsArithFrobAt.restrict** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom.IsArithFrobAt`
。
形式化陈述：restrict : S ⧸ Q ->ₐ[R ⧸ Q.under R] S ⧸ Q where toRingHom
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `AlgHom.IsArithFrobAt.le_comap`：le_comap : Q <= Q.comap φ

--- 原说明 ---
A Frobenius element at `Q` restricts to the Frobenius map on `S ⧸ Q`.
-/
def restrict : S ⧸ Q →ₐ[R ⧸ Q.under R] S ⧸ Q where
  toRingHom := Ideal.quotientMap Q φ H.le_comap
  commutes' x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact DFunLike.congr_arg (Ideal.Quotient.mk Q) (φ.commutes x)
/-
**AlgHom.IsArithFrobAt.restrict_apply** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom.IsArithF
robAt`。
形式化陈述：restrict_apply (x : S ⧸ Q) : H.restrict x = x ^ Nat.card (R ⧸ Q.under R)
参数：x : S ⧸ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用引理 `AlgHom.IsArithFrobAt.mk_apply`：mk_apply (x) : Ideal.Quotient.mk Q (φ x) 
= x ^ Nat.card (R ⧸ Q.under R)
-/
lemma restrict_apply (x : S ⧸ Q) :
    H.restrict x = x ^ Nat.card (R ⧸ Q.under R) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact H.mk_apply x
/-
**AlgHom.IsArithFrobAt.restrict_mk** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom.IsArithFrob
At`。
形式化陈述：restrict_mk (x : S) : H.restrict ↑x = ↑(φ x)
参数：x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
lemma restrict_mk (x : S) : H.restrict ↑x = ↑(φ x) := rfl
/-
**AlgHom.IsArithFrobAt.restrict_injective** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom.IsAr
ithFrobAt`。
形式化陈述：restrict_injective [Q.IsPrime] : Function.Injective H.restrict
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgHom.IsArithFrobAt.restrict_apply`：restrict_apply (x : S ⧸ Q) : H.rest
rict x = x ^ Nat.card (R ⧸ Q.under R)
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `AlgHom.IsArithFrobAt.card_pos`：card_pos : 0 < Nat.card (R ⧸ Q.under R)
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma restrict_injective [Q.IsPrime] :
    Function.Injective H.restrict := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  simpa [restrict_apply, H.card_pos.ne'] using hx
/-
**AlgHom.IsArithFrobAt.comap_eq** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom.IsArithFrobAt`
。
形式化陈述：comap_eq [Q.IsPrime] : Q.comap φ = Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `AlgHom.IsArithFrobAt.restrict_injective`：restrict_injective [Q.IsPrime] 
: Function.Injective H.restrict
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `AlgHom.IsArithFrobAt.restrict_mk`：restrict_mk (x : S) : H.restrict ↑x = 
↑(φ x)
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用引理 `AlgHom.IsArithFrobAt.le_comap`：le_comap : Q <= Q.comap φ
-/
lemma comap_eq [Q.IsPrime] : Q.comap φ = Q := by
  refine le_antisymm (fun x hx ↦ ?_) H.le_comap
  rwa [← Ideal.Quotient.eq_zero_iff_mem, ← H.restrict_injective.eq_iff, map_zero, restrict_mk,
    Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap]

/-- Suppose `S` is a domain, and `φ : S →ₐ[R] S` is a Frobenius at `Q : Ideal S`.
Let `ζ` be a `m`-th root of unity with `Q ∤ m`, then `φ` sends `ζ` to `ζ ^ q`. -/
/-
**AlgHom.IsArithFrobAt.apply_of_pow_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom.IsA
rithFrobAt`。
形式化陈述：apply_of_pow_eq_one [IsDomain S] {ζ : S} {m : Nat} (hζ : ζ ^ m = 1) (hk' :
 ↑m ∉ Q) : φ ζ = ζ ^ Nat.card (R ⧸ Q.under R)
参数：hζ : ζ ^ m = 1；hk' : ↑m ∉ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsPrimitiveRoot.exists_pos`：exists_pos {k : Nat} (hζ : ζ ^ k = 1) (hk : 
k != 0) : exists k' > 0, IsPrimitiveRoot ζ k'
· 使用引理 `Ideal.mem_of_dvd`：mem_of_dvd (hab : a ∣ b) (ha : a in I) : b in I
· 使用引理 `Nat.cast_dvd_cast`：cast_dvd_cast (h : m ∣ n) : (m : α) ∣ (n : α)
· 使用定理 `IsPrimitiveRoot.dvd_of_pow_eq_one`：∀ {M : Type u_1} [inst : CommMonoid M
] {ζ : M} {k : ℕ}, IsPrimitiveRoot ζ k → ∀ (l : ℕ), ζ ^ l = 1 → k ∣ l
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `IsPrimitiveRoot.eq_pow_of_pow_eq_one`：eq_pow_of_pow_eq_one {k : Nat} [Ne
Zero k] {ζ ξ : R} (h : IsPrimitiveRoot ζ k) (hξ : ξ ^ k = 1) : exists i < k, ζ ^
 i = ξ
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IsPrimitiveRoot.pow_eq_one`：∀ {M : Type u_1} [inst : CommMonoid M] {ζ : 
M} {k : ℕ}, IsPrimitiveRoot ζ k → ζ ^ k = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Ideal.mul_unit_mem_iff_mem`：mul_unit_mem_iff_mem {x y : α} (hy : IsUnit 
y) : x * y in I ↔ x in I
· 使用定理 `IsUnit.pow`：∀ {M : Type u_1} [inst : Monoid M] {a : M} (n : ℕ), IsUnit a
 → IsUnit (a ^ n)
· 使用定理 `IsPrimitiveRoot.isUnit`：isUnit (h : IsPrimitiveRoot ζ k) (h0 : k != 0) :
 IsUnit ζ
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
（共 99 条，此处仅展示前 30 条）

--- 原说明 ---
Suppose `S` is a domain, and `φ : S →ₐ[R] S` is a Frobenius at `Q : Ideal S`.
Let `ζ` be a `m`-th root of unity with `Q ∤ m`, then `φ` sends `ζ` to `ζ ^ q`.
-/
lemma apply_of_pow_eq_one [IsDomain S] {ζ : S} {m : ℕ} (hζ : ζ ^ m = 1) (hk' : ↑m ∉ Q) :
    φ ζ = ζ ^ Nat.card (R ⧸ Q.under R) := by
  set q := Nat.card (R ⧸ Q.under R)
  have hm : m ≠ 0 := by rintro rfl; exact hk' (by simp)
  obtain ⟨k, hk, hζ⟩ := IsPrimitiveRoot.exists_pos hζ hm
  have hk' : ↑k ∉ Q := fun h ↦ hk' (Q.mem_of_dvd (Nat.cast_dvd_cast (hζ.2 m ‹_›)) h)
  have : NeZero k := ⟨hk.ne'⟩
  obtain ⟨i, hi, e⟩ := hζ.eq_pow_of_pow_eq_one (ξ := φ ζ) (by rw [← map_pow, hζ.1, map_one])
  have (j : _) : 1 - ζ ^ ((q + k - i) * j) ∈ Q := by
    rw [← Ideal.mul_unit_mem_iff_mem _ ((hζ.isUnit NeZero.out).pow (i * j)),
      sub_mul, one_mul, ← pow_add, ← add_mul, tsub_add_cancel_of_le (by linarith), add_mul,
        pow_add, pow_mul _ k, hζ.1, one_pow, mul_one, pow_mul, e, ← map_pow, mul_comm, pow_mul]
    exact H _
  have h₁ := sum_mem (t := Finset.range k) fun j _ ↦ this j
  have h₂ := geom_sum_mul (ζ ^ (q + k - i)) k
  rw [pow_right_comm, hζ.1, one_pow, sub_self, mul_eq_zero, sub_eq_zero] at h₂
  rcases h₂ with h₂ | h₂
  · simp [h₂, pow_mul, hk'] at h₁
  replace h₂ := congr($h₂ * ζ ^ i)
  rw [one_mul, ← pow_add, tsub_add_cancel_of_le (by linarith), pow_add, hζ.1, mul_one] at h₂
  rw [h₂, e]

set_option backward.isDefEq.respectTransparency.types false in
/-- A Frobenius element at `Q` restricts to an automorphism of `S_Q`. -/
noncomputable
/-
**AlgHom.IsArithFrobAt.localize** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom.IsArithFrobAt`
。
形式化陈述：localize [Q.IsPrime] : Localization.AtPrime Q ->ₐ[R] Localization.AtPrime 
Q where toRingHom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def localize [Q.IsPrime] : Localization.AtPrime Q →ₐ[R] Localization.AtPrime Q where
  toRingHom := Localization.localRingHom _ _ φ H.comap_eq.symm
  commutes' x := by
    simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime Q),
      Localization.localRingHom_to_map]

@[simp]
/-
**AlgHom.IsArithFrobAt.localize_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom.IsA
rithFrobAt`。
形式化陈述：localize_algebraMap [Q.IsPrime] (x : S) : H.localize (algebraMap _ _ x) = 
algebraMap _ _ (φ x)
参数：x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.localRingHom_to_map`：localRingHom_to_map (J : Ideal P) [J.I
sPrime] (f : R ->+* P) (hIJ : I = J.comap f) (x : R) : localRingHom I J f hIJ (a
lgebraMap _ _ x) = alg…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用引理 `AlgHom.IsArithFrobAt.comap_eq`：comap_eq [Q.IsPrime] : Q.comap φ = Q
-/
lemma localize_algebraMap [Q.IsPrime] (x : S) :
    H.localize (algebraMap _ _ x) = algebraMap _ _ (φ x) :=
  Localization.localRingHom_to_map _ _ _ H.comap_eq.symm _

open IsLocalRing nonZeroDivisors

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgHom.IsArithFrobAt.isArithFrobAt_localize** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom.
IsArithFrobAt`。
形式化陈述：isArithFrobAt_localize [Q.IsPrime] : H.localize.IsArithFrobAt (maximalIdea
l _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.under_def`：under_def : P.under A = Ideal.comap (algebraMap A B) P
· 使用定理 `Ideal.under_under`：under_under : (𝔓.under B).under A = 𝔓.under A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Localization.AtPrime.under_maximalIdeal`：∀ {R : Type u_1} [inst : CommSe
miring R] {I : Ideal R} [hI : I.IsPrime],   Ideal.under R (IsLocalRing.maximalId
eal (Localization I.primeComp…
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Localization.le_comap_primeCompl_iff`：le_comap_primeCompl_iff {J : Ideal
 P} [J.IsPrime] {f : R ->+* P} : I.primeCompl <= J.primeCompl.comap f ↔ J.comap 
f <= I
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Localization.localRingHom_mk'`：localRingHom_mk' (J : Ideal P) [J.IsPrime
] (f : R ->+* P) (hIJ : I = J.comap f) (x : R) (y : I.primeCompl) : localRingHom
 I J f hIJ (IsLocal…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLocalization.mk'_sub`：∀ {R : Type u_1} [inst : CommRing R] {M : Submon
oid R} (S : Type u_2) [inst_1 : CommRing S] [inst_2 : Algebra R S]   [inst_3 : I
sLocalizatio…
· 使用定理 `IsLocalization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemirin
g R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (P : Ideal 
R)   [hp : P.IsPrime] [I…
· 使用定理 `IsLocalization.AtPrime.mk'_mem_maximal_iff`：∀ {R : Type u_1} [inst : Com
mSemiring R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (I 
: Ideal R)   [hI : I.IsPrime] [i…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
（共 35 条，此处仅展示前 30 条）
-/
lemma isArithFrobAt_localize [Q.IsPrime] : H.localize.IsArithFrobAt (maximalIdeal _) := by
  have h : Nat.card (R ⧸ (maximalIdeal _).comap (algebraMap R (Localization.AtPrime Q))) =
      Nat.card (R ⧸ Q.under R) := by
    congr 2
    rw [← Ideal.under_def, ← Ideal.under_under (B := S), Localization.AtPrime.under_maximalIdeal]
  intro x
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq Q.primeCompl x
  simp only [localize, coe_mk, Localization.localRingHom_mk', RingHom.coe_coe, h,
    ← IsLocalization.mk'_pow]
  rw [← IsLocalization.mk'_sub,
    IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime Q) Q]
  simp only [SubmonoidClass.coe_pow, ← Ideal.Quotient.eq_zero_iff_mem]
  simp [H.mk_apply]

/-- Suppose `S` is Noetherian and `Q` is a prime of `S` containing all zero divisors.
If `S/R` is unramified at `Q`, then the Frobenius `φ : S →ₐ[R] S` over `Q` is unique. -/
/-
**AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt** 是 Mathlib 中的一个引理，位于命名空间 `AlgHom.Is
ArithFrobAt`。
形式化陈述：eq_of_isUnramifiedAt (H' : ψ.IsArithFrobAt Q) [Q.IsPrime] (hQ : Q.primeCom
pl <= S⁰) [Algebra.IsUnramifiedAt R Q] [IsNoetherianRing S] : φ = ψ
参数：H' : ψ.IsArithFrobAt Q；hQ : Q.primeCompl <= S⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyUnramified.ext_of_iInf`：ext_of_iInf [FormallyUnramified 
R A] (hI : ⨅ i, I ^ i = ⊥) {g₁ g₂ : A ->ₐ[R] B} (H : forall x, Ideal.Quotient.mk
 I (g₁ x) = Ideal.Quotient.m…
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Ideal.iInf_pow_eq_bot_of_isLocalRing`：Ideal.iInf_pow_eq_bot_of_isLocalRi
ng [IsNoetherianRing R] [IsLocalRing R] (h : I != ⊤) : ⨅ i : Nat, I ^ i = ⊥
· 使用定理 `IsLocalization.instIsNoetherianRingLocalization`：∀ {R : Type u_3} [inst 
: CommRing R] [IsNoetherianRing R] (S : Submonoid R), IsNoetherianRing (Localiza
tion S)
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgHom.IsArithFrobAt.mk_apply`：mk_apply (x) : Ideal.Quotient.mk Q (φ x) 
= x ^ Nat.card (R ⧸ Q.under R)
· 使用引理 `AlgHom.IsArithFrobAt.isArithFrobAt_localize`：isArithFrobAt_localize [Q.I
sPrime] : H.localize.IsArithFrobAt (maximalIdeal _)
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `IsLocalization.injective`：∀ {R : Type u_1} [inst : CommRing R] {M : Subm
onoid R} (S : Type u_2) [inst_1 : CommRing S] [inst_2 : Algebra R S]   [IsLocali
zation M S], M…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgHom.IsArithFrobAt.localize_algebraMap`：localize_algebraMap [Q.IsPrime
] (x : S) : H.localize (algebraMap _ _ x) = algebraMap _ _ (φ x)

--- 原说明 ---
Suppose `S` is Noetherian and `Q` is a prime of `S` containing all zero divisors
.
If `S/R` is unramified at `Q`, then the Frobenius `φ : S →ₐ[R] S` over `Q` is un
ique.
-/
lemma eq_of_isUnramifiedAt
    (H' : ψ.IsArithFrobAt Q) [Q.IsPrime] (hQ : Q.primeCompl ≤ S⁰)
    [Algebra.IsUnramifiedAt R Q] [IsNoetherianRing S] : φ = ψ := by
  have : H.localize = H'.localize := by
    apply Algebra.FormallyUnramified.ext_of_iInf _
      (Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal _) Ideal.IsPrime.ne_top')
    intro x
    rw [H.isArithFrobAt_localize.mk_apply, H'.isArithFrobAt_localize.mk_apply]
  ext x
  apply IsLocalization.injective (Localization.AtPrime Q) hQ
  rw [← H.localize_algebraMap, ← H'.localize_algebraMap, this]

end AlgHom.IsArithFrobAt

variable (R) in
/--
Suppose `S` is an `R` algebra, `M` is a monoid acting on `S` whose action is trivial on `R`
`σ : M` is an (arithmetic) Frobenius at an ideal `Q` of `S` if `σ • x ≡ x ^ q (mod Q)` for all `x`.
-/
/-
**IsArithFrobAt** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IsArithFrobAt {M : Type*} [Monoid M] [MulSemiringAction M S] [SMulCommClas
s M R S] (σ : M) (Q : Ideal S) : Prop
参数：σ : M；Q : Ideal S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Suppose `S` is an `R` algebra, `M` is a monoid acting on `S` whose action is tri
vial on `R`
`σ : M` is an (arithmetic) Frobenius at an ideal `Q` of `S` if `σ • x ≡ x ^ q (m
od Q)` for all `x`.
-/
abbrev IsArithFrobAt {M : Type*} [Monoid M] [MulSemiringAction M S] [SMulCommClass M R S]
    (σ : M) (Q : Ideal S) : Prop :=
  (MulSemiringAction.toAlgHom R S σ).IsArithFrobAt Q

namespace IsArithFrobAt

open scoped Pointwise

variable {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
variable {Q : Ideal S} {σ σ' : G}

/-
**IsArithFrobAt.mem_stabilizer** 是 Mathlib 中的一个定理，位于命名空间 `IsArithFrobAt`。
形式化陈述：mem_stabilizer [Q.IsPrime] (h : IsArithFrobAt R σ Q) : σ in MulAction.stab
ilizer G Q
参数：h : IsArithFrobAt R σ Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.mem_stabilizer_iff`：mem_stabilizer_iff {a : α} {g : G} : g in 
stabilizer G a ↔ g • a = a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgHom.IsArithFrobAt.comap_eq`：comap_eq [Q.IsPrime] : Q.comap φ = Q
· 使用定理 `Ideal.pointwise_smul_def`：pointwise_smul_def {a : M} (S : Ideal R) : a •
 S = S.map (MulSemiringAction.toRingHom _ _ a)
· 使用定理 `Ideal.map_comap_eq_self_of_equiv`：map_comap_eq_self_of_equiv {E : Type*}
 [EquivLike E R S] [RingEquivClass E R S] (e : E) (I : Ideal S) : map e (comap e
 I) = I
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem mem_stabilizer [Q.IsPrime] (h : IsArithFrobAt R σ Q) : σ ∈ MulAction.stabilizer G Q := by
  rw [MulAction.mem_stabilizer_iff]
  conv_lhs => rw [← h.comap_eq]
  rw [Ideal.pointwise_smul_def]
  exact Q.map_comap_eq_self_of_equiv (MulSemiringAction.toRingEquiv G S σ)
/-
**IsArithFrobAt.mul_inv_mem_inertia** 是 Mathlib 中的一个引理，位于命名空间 `IsArithFrobAt`。
形式化陈述：mul_inv_mem_inertia (H : IsArithFrobAt R σ Q) (H' : IsArithFrobAt R σ' Q) 
: σ * σ'⁻¹ in Q.inertia G
参数：H : IsArithFrobAt R σ Q；H' : IsArithFrobAt R σ' Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulSemiringAction.toAlgHom_apply`：∀ {M : Type u_1} (R : Type u_3) (A : T
ype u_4) [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   
[inst_3 : Monoid M] [i…
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `sub_sub_sub_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a - c - (b - c) = a - b
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
-/
lemma mul_inv_mem_inertia (H : IsArithFrobAt R σ Q) (H' : IsArithFrobAt R σ' Q) :
    σ * σ'⁻¹ ∈ Q.inertia G := by
  intro x
  simpa [mul_smul] using sub_mem (H (σ'⁻¹ • x)) (H' (σ'⁻¹ • x))
/-
**IsArithFrobAt.conj** 是 Mathlib 中的一个引理，位于命名空间 `IsArithFrobAt`。
形式化陈述：conj (H : IsArithFrobAt R σ Q) (τ : G) : IsArithFrobAt R (τ * σ * τ⁻¹) (τ 
• Q)
参数：H : IsArithFrobAt R σ Q；τ : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_symm`：comap_symm {I : Ideal R} (f : R ≃+* S) : I.comap f.sym
m = I.map f
· 使用引理 `Ideal.comap_coe`：comap_coe [RingHomClass F R S] (I : Ideal S) : I.comap 
(f : R ->+* S) = I.comap f
· 使用定理 `Ideal.under.eq_1`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type u_3
} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B),   Ideal.under A P 
= Idea…
· 使用定理 `Ideal.comap_comap`：comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f
 : R ->+* S) (g : S ->+* T) : (I.comap g).comap f = I.comap (g.comp f)
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `Ideal.pointwise_smul_eq_comap`：pointwise_smul_eq_comap {a : M} (S : Idea
l R) : a • S = S.comap (MulSemiringAction.toRingAut _ _ a).symm
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulSemiringAction.toRingAut_apply`：∀ (G : Type u_1) (R : Type u_2) [inst
 : Group G] [inst_1 : Semiring R] [inst_2 : MulSemiringAction G R] (a : G),   (M
ulSemiringAction.toRing…
· 使用定理 `MulSemiringAction.toAlgHom_apply`：∀ {M : Type u_1} (R : Type u_3) (A : T
ype u_4) [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   
[inst_3 : Monoid M] [i…
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Ideal.comap.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   (f f_1 : F),   f
 = f_1 → ∀ […
· 使用定理 `MulSemiringAction.toRingEquiv_apply_symm_apply`：∀ (G : Type u_1) [inst :
 Group G] (R : Type u_2) [inst_1 : Semiring R] [inst_2 : MulSemiringAction G R] 
(x : G) (a : R),   ((MulSemiringActi…
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `smul_pow'`：∀ {M : Type u_2} {A : Type u_3} [inst : Monoid M] [inst_1 : M
onoid A] [inst_2 : MulDistribMulAction M A] (r : M) (x : A)   (n : ℕ), r • x ^ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma conj (H : IsArithFrobAt R σ Q) (τ : G) : IsArithFrobAt R (τ * σ * τ⁻¹) (τ • Q) := by
  intro x
  have : (Q.map (MulSemiringAction.toRingEquiv G S τ)).under R = Q.under R := by
    rw [← Ideal.comap_symm, ← Ideal.comap_coe, Ideal.under, Ideal.comap_comap]
    congr 1
    exact (MulSemiringAction.toAlgEquiv R S τ).symm.toAlgHom.comp_algebraMap
  rw [Ideal.pointwise_smul_eq_comap, Ideal.mem_comap]
  simpa [smul_sub, mul_smul, this] using H (τ⁻¹ • x)

variable [Finite G] [Algebra.IsInvariant R S G]

variable (R G Q) in
attribute [local instance] Ideal.Quotient.field in
/-- Let `G` be a finite group acting on `S`, and `R` be the fixed subring.
If `Q` is a prime of `S` with finite residue field,
then there exists a Frobenius element `σ : G` at `Q`. -/
/-
**IsArithFrobAt.exists_of_isInvariant** 是 Mathlib 中的一个引理，位于命名空间 `IsArithFrobAt`。
形式化陈述：exists_of_isInvariant [Q.IsPrime] [Finite (S ⧸ Q)] : exists σ : G, IsArith
FrobAt R σ Q
参数：S ⧸ Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsInvariant.isIntegral`：isIntegral [Finite G] : Algebra.IsIntegr
al A B
· 使用定理 `Ideal.Quotient.maximal_of_isField`：maximal_of_isField {R} [CommRing R] (
I : Ideal R) (hqf : IsField (R ⧸ I)) : I.IsMaximal
· 使用定理 `Finite.isField_of_domain`：Finite.isField_of_domain (R) [CommRing R] [IsD
omain R] [Finite R] : IsField R
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `CharP.exists`：∀ (R : Type u_1) [inst : NonAssocSemiring R], ∃ p, CharP R
 p
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用定理 `Ideal.algebraMap_quotient_injective`：algebraMap_quotient_injective {R} [
CommRing R] {I : Ideal A} [I.IsTwoSided] [Algebra R A] : Function.Injective (alg
ebraMap (R ⧸ I.comap (alg…
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `FiniteField.card`：card (p : Nat) [CharP K p] : exists n : Nat+, Nat.Prim
e p ∧ q = p ^ (n : Nat)
· 使用定理 `Ideal.IsMaximal.under`：∀ (A : Type u_1) [inst : CommRing A] {B : Type u_
2} [inst_1 : CommRing B] [inst_2 : Algebra A B]   [Algebra.IsIntegral A B] (P : 
Ideal B) [P…
· 使用定理 `CharP.of_ringHom_of_ne_zero`：CharP.of_ringHom_of_ne_zero [NonAssocSemiri
ng R] [NoZeroDivisors R] [NonAssocSemiring A] [Nontrivial A] (f : R ->+* A) (p :
 Nat) (hp : p != …
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `RingEquiv.map_mul'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `RingEquiv.map_add'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `FiniteField.pow_card`：pow_card (a : K) : a ^ q = a
· 使用定理 `Ideal.Quotient.stabilizerHom_surjective`：Ideal.Quotient.stabilizerHom_su
rjective : Function.Surjective (Ideal.Quotient.stabilizerHom Q P G)
· 使用定理 `Ideal.Quotient.eq`：∀ {R : Type u} [inst : Ring R] {I : Ideal R} {x y : R
} [inst_1 : I.IsTwoSided],   (Ideal.Quotient.mk I) x = (Ideal.Quotient.mk I) y ↔
 x - y …
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
Let `G` be a finite group acting on `S`, and `R` be the fixed subring.
If `Q` is a prime of `S` with finite residue field,
then there exists a Frobenius element `σ : G` at `Q`.
-/
lemma exists_of_isInvariant [Q.IsPrime] [Finite (S ⧸ Q)] : ∃ σ : G, IsArithFrobAt R σ Q := by
  let P := Q.under R
  have := Algebra.IsInvariant.isIntegral R S G
  have : Q.IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (S ⧸ Q))
  obtain ⟨p, hc⟩ := CharP.exists (R ⧸ P)
  have : Finite (R ⧸ P) := .of_injective _ Ideal.algebraMap_quotient_injective
  cases nonempty_fintype (R ⧸ P)
  obtain ⟨k, hp, hk⟩ := FiniteField.card (R ⧸ P) p
  have := CharP.of_ringHom_of_ne_zero (algebraMap (R ⧸ P) (S ⧸ Q)) p hp.ne_zero
  have : ExpChar (S ⧸ Q) p := .prime hp
  let l : (S ⧸ Q) ≃ₐ[R ⧸ P] S ⧸ Q :=
    { __ := iterateFrobeniusEquiv (S ⧸ Q) p k,
      commutes' r := by
        dsimp [iterateFrobenius_def]
        rw [← map_pow, ← hk, FiniteField.pow_card] }
  obtain ⟨σ, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective G P Q l
  refine ⟨σ, fun x ↦ ?_⟩
  rw [← Ideal.Quotient.eq, Nat.card_eq_fintype_card, hk]
  exact DFunLike.congr_fun hσ (Ideal.Quotient.mk Q x)

variable (S G) in
/-
**IsArithFrobAt.exists_primesOver_isConj** 是 Mathlib 中的一个引理，位于命名空间 `IsArithFrobA
t`。
形式化陈述：exists_primesOver_isConj (P : Ideal R) (hP : exists Q : Ideal.primesOver P
 S, Finite (S ⧸ Q.1)) : exists σ : Ideal.primesOver P S -> G, (forall Q, IsArith
FrobAt R (σ Q) Q.1) ∧ (forall Q₁ Q₂, IsConj (σ Q₁) (σ Q₂))
参数：P : Ideal R；hP : exists Q : Ideal.primesOver P S, Finite (S ⧸ Q.1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsInvariant.exists_smul_of_under_eq`：exists_smul_of_under_eq [Fi
nite G] [SMulCommClass G A B] (P Q : Ideal B) [hP : P.IsPrime] [hQ : Q.IsPrime] 
(hPQ : P.under A = Q.under A) : e…
· 使用定理 `Ideal.primesOver.isPrime`：∀ {A : Type u_2} [inst : CommSemiring A] (p : 
Ideal A) {B : Type u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B]   (Q : ↑(p.
primesOver B))…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.LiesOver.over`：∀ {A : Type u_2} {inst : CommSemiring A} {B : Type 
u_3} {inst_1 : Semiring B} {inst_2 : Algebra A B} {P : Ideal B}   {p : Ideal A} 
[self : P…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `IsArithFrobAt.exists_of_isInvariant`：exists_of_isInvariant [Q.IsPrime] [
Finite (S ⧸ Q)] : exists σ : G, IsArithFrobAt R σ Q
· 使用引理 `IsArithFrobAt.conj`：conj (H : IsArithFrobAt R σ Q) (τ : G) : IsArithFrob
At R (τ * σ * τ⁻¹) (τ • Q)
· 使用定理 `IsConj.trans`：∀ {α : Type u} [inst : Monoid α] {a b c : α}, IsConj a b →
 IsConj b c → IsConj a c
· 使用引理 `IsConj.symm`：IsConj.symm (hσ : IsConj φ σ) : IsConj φ σ.symm
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isConj_iff`：isConj_iff {a b : α} : IsConj a b ↔ exists c : α, c * a * c⁻
¹ = b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma exists_primesOver_isConj (P : Ideal R)
    (hP : ∃ Q : Ideal.primesOver P S, Finite (S ⧸ Q.1)) :
    ∃ σ : Ideal.primesOver P S → G, (∀ Q, IsArithFrobAt R (σ Q) Q.1) ∧
      (∀ Q₁ Q₂, IsConj (σ Q₁) (σ Q₂)) := by
  obtain ⟨⟨Q, hQ₁, hQ₂⟩, hQ₃⟩ := hP
  have (Q' : Ideal.primesOver P S) : ∃ σ : G, Q'.1 = σ • Q :=
    Algebra.IsInvariant.exists_smul_of_under_eq R S G _ _ (hQ₂.over.symm.trans Q'.2.2.over)
  choose τ hτ using this
  obtain ⟨σ, hσ⟩ := exists_of_isInvariant R G Q
  refine ⟨fun Q' ↦ τ Q' * σ * (τ Q')⁻¹, fun Q' ↦ hτ Q' ▸ hσ.conj (τ Q'), fun Q₁ Q₂ ↦
    .trans (.symm (isConj_iff.mpr ⟨τ Q₁, rfl⟩)) (isConj_iff.mpr ⟨τ Q₂, rfl⟩)⟩

variable (R G Q)

/-- Let `G` be a finite group acting on `S`, `R` be the fixed subring, and `Q` be a prime of `S`
with finite residue field. This is an arbitrary choice of a Frobenius over `Q`. It is chosen so that
the Frobenius elements of `Q₁` and `Q₂` are conjugate if they lie over the same prime. -/
noncomputable
/-
**IsArithFrobAt._root_.arithFrobAt** 是 Mathlib 中的一个定义，位于命名空间 `IsArithFrobAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def _root_.arithFrobAt [Q.IsPrime] [Finite (S ⧸ Q)] : G :=
  (exists_primesOver_isConj S G (Q.under R)
    ⟨⟨Q, ‹_›, ⟨rfl⟩⟩, ‹Finite (S ⧸ Q)›⟩).choose ⟨Q, ‹_›, ⟨rfl⟩⟩
/-
**IsArithFrobAt.arithFrobAt** 是 Mathlib 中的一个定理，位于命名空间 `IsArithFrobAt`。
形式化陈述：∀ (R : Type u_1) {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (G : Type u_3)   [inst_3 : Group G] [inst_4 : MulSemiring
Action G S] [inst_5 : SMulCommClass G R S] (Q : Ideal S) [inst_6 : Finite G]   [
inst_7 : Algebra.IsInvariant R S G] [inst_8 : Q.IsPrime] [inst_9 : Finite (S ⧸ Q
)],   IsArithFrobAt R (arithFrobAt R G Q) Q
参数：R : Type u_1；G : Type u_3；Q : Ideal S；S ⧸ Q；arithFrobAt R G Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `IsArithFrobAt.exists_primesOver_isConj`：exists_primesOver_isConj (P : Id
eal R) (hP : exists Q : Ideal.primesOver P S, Finite (S ⧸ Q.1)) : exists σ : Ide
al.primesOver P S -> G, (for…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
protected lemma arithFrobAt [Q.IsPrime] [Finite (S ⧸ Q)] : IsArithFrobAt R (arithFrobAt R G Q) Q :=
  (exists_primesOver_isConj S G (Q.under R)
    ⟨⟨Q, ‹_›, ⟨rfl⟩⟩, ‹Finite (S ⧸ Q)›⟩).choose_spec.1 ⟨Q, ‹_›, ⟨rfl⟩⟩
/-
**IsArithFrobAt.arithFrobAt_mem_stabilizer** 是 Mathlib 中的一个定理，位于命名空间 `IsArithFro
bAt`。
形式化陈述：arithFrobAt_mem_stabilizer [Q.IsPrime] [Finite (S ⧸ Q)] : arithFrobAt R G 
Q in MulAction.stabilizer G Q
参数：S ⧸ Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsArithFrobAt.mem_stabilizer`：mem_stabilizer [Q.IsPrime] (h : IsArithFro
bAt R σ Q) : σ in MulAction.stabilizer G Q
· 使用定理 `IsArithFrobAt.arithFrobAt`：∀ (R : Type u_1) {S : Type u_2} [inst : CommR
ing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (G : Type u_3)   [inst_3 : G
roup G] [inst_4…
-/
theorem arithFrobAt_mem_stabilizer [Q.IsPrime] [Finite (S ⧸ Q)] :
    arithFrobAt R G Q ∈ MulAction.stabilizer G Q :=
  mem_stabilizer (.arithFrobAt R G Q)
/-
**IsArithFrobAt._root_.isConj_arithFrobAt** 是 Mathlib 中的一个引理，位于命名空间 `IsArithFrob
At`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.isConj_arithFrobAt
    [Q.IsPrime] [Finite (S ⧸ Q)] (Q' : Ideal S) [Q'.IsPrime] [Finite (S ⧸ Q')]
    (H : Q.under R = Q'.under R) : IsConj (arithFrobAt R G Q) (arithFrobAt R G Q') := by
  obtain ⟨P, hP, h₁, h₂⟩ : ∃ P : Ideal R, P.IsPrime ∧ P = Q.under R ∧ P = Q'.under R :=
    ⟨Q.under R, inferInstance, rfl, H⟩
  convert!
    (exists_primesOver_isConj S G P ⟨⟨Q, ‹_›, ⟨h₁⟩⟩, ‹Finite (S ⧸ Q)›⟩).choose_spec.2 ⟨Q, ‹_›, ⟨h₁⟩⟩
      ⟨Q', ‹_›, ⟨h₂⟩⟩
  · subst h₁; rfl
  · subst h₂; rfl

end IsArithFrobAt

