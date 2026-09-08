/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.CharP

/-!
# Results on characteristic polynomials and traces over finite fields.
-/

public section


noncomputable section

open Polynomial Matrix

open scoped Polynomial

variable {n : Type*} [DecidableEq n] [Fintype n]

@[simp]
/-
**FiniteField.Matrix.charpoly_pow_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteField.Matrix.charpoly_pow_card {K : Type*} [Field K] [Fintype K] (M 
: Matrix n n K) : (M ^ Fintype.card K).charpoly = M.charpoly
参数：M : Matrix n n K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `CharP.exists`：∀ (R : Type u_1) [inst : NonAssocSemiring R], ∃ p, CharP R
 p
· 使用定理 `FiniteField.card`：card (p : Nat) [CharP K p] : exists n : Nat+, Nat.Prim
e p ∧ q = p ^ (n : Nat)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.iterate`：∀ {α : Type u} {f : α → α}, Function.Injecti
ve f → ∀ (n : ℕ), Function.Injective f^[n]
· 使用定理 `frobenius_inj`：frobenius_inj : Function.Injective (frobenius R p)
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `iterate_frobenius`：iterate_frobenius : (frobenius R p)^[n] x = x ^ p ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FiniteField.expand_card`：expand_card (f : K[X]) : expand K q f = f ^ q
· 使用定理 `AlgHom.map_det`：∀ {n : Type u_2} [inst : DecidableEq n] [inst_1 : Fintyp
e n] {R : Type v} [inst_2 : CommRing R] {S : Type w}   [inst_3 : CommRing S] [in
st_4…
· 使用定理 `Matrix.coe_detMonoidHom`：coe_detMonoidHom : (detMonoidHom : Matrix n n R
 -> R) = det
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
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
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Matrix.matPolyEquiv_charmatrix`：matPolyEquiv_charmatrix : matPolyEquiv (
charmatrix M) = X - C M
· 使用引理 `sub_pow_char_pow_of_commute`：sub_pow_char_pow_of_commute (h : Commute x 
y) : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n
· 使用定理 `Polynomial.commute_X`：commute_X (p : R[X]) : Commute X p
· 使用定理 `Polynomial.C_pow`：C_pow : C (a ^ n) = C a ^ n
· 使用定理 `matPolyEquiv_eq_X_pow_sub_C`：matPolyEquiv_eq_X_pow_sub_C {K : Type*} (k 
: Nat) [CommRing K] (M : Matrix n n K) : matPolyEquiv ((expand K k : K[X] ->+* K
[X]).mapMatrix (c…
（共 31 条，此处仅展示前 30 条）
-/
theorem FiniteField.Matrix.charpoly_pow_card {K : Type*} [Field K] [Fintype K] (M : Matrix n n K) :
    (M ^ Fintype.card K).charpoly = M.charpoly := by
  cases (isEmpty_or_nonempty n).symm
  · obtain ⟨p, hp⟩ := CharP.exists K
    rcases FiniteField.card K p with ⟨⟨k, kpos⟩, ⟨hp, hk⟩⟩
    have : Fact p.Prime := ⟨hp⟩
    dsimp at hk; rw [hk]
    apply (frobenius_inj K[X] p).iterate k
    repeat' rw [iterate_frobenius (R := K[X])]; rw [← hk]
    rw [← FiniteField.expand_card]
    unfold charpoly
    rw [AlgHom.map_det, ← coe_detMonoidHom, ← (detMonoidHom : Matrix n n K[X] →* K[X]).map_pow]
    apply congr_arg det
    refine matPolyEquiv.injective ?_
    rw [map_pow, matPolyEquiv_charmatrix, hk, sub_pow_char_pow_of_commute, ← C_pow]
    · exact (id (matPolyEquiv_eq_X_pow_sub_C (p ^ k) M) :)
    · exact (C M).commute_X
  · exact congr_arg _ (Subsingleton.elim _ _)

@[simp]
/-
**ZMod.charpoly_pow_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZMod.charpoly_pow_card {p : Nat} [Fact p.Prime] (M : Matrix n n (ZMod p)) 
: (M ^ p).charpoly = M.charpoly
参数：M : Matrix n n (ZMod p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `FiniteField.Matrix.charpoly_pow_card`：FiniteField.Matrix.charpoly_pow_ca
rd {K : Type*} [Field K] [Fintype K] (M : Matrix n n K) : (M ^ Fintype.card K).c
harpoly = M.charpoly
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
-/
theorem ZMod.charpoly_pow_card {p : ℕ} [Fact p.Prime] (M : Matrix n n (ZMod p)) :
    (M ^ p).charpoly = M.charpoly := by
  have h := FiniteField.Matrix.charpoly_pow_card M
  rwa [ZMod.card] at h
/-
**FiniteField.trace_pow_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteField.trace_pow_card {K : Type*} [Field K] [Fintype K] (M : Matrix n
 n K) : trace (M ^ Fintype.card K) = trace M ^ Fintype.card K
参数：M : Matrix n n K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.trace_eq_neg_charpoly_coeff`：trace_eq_neg_charpoly_coeff [Nonempt
y n] (M : Matrix n n R) : trace M = -M.charpoly.coeff (Fintype.card n - 1)
· 使用定理 `FiniteField.Matrix.charpoly_pow_card`：FiniteField.Matrix.charpoly_pow_ca
rd {K : Type*} [Field K] [Fintype K] (M : Matrix n n K) : (M ^ Fintype.card K).c
harpoly = M.charpoly
· 使用定理 `FiniteField.pow_card`：pow_card (a : K) : a ^ q = a
-/
theorem FiniteField.trace_pow_card {K : Type*} [Field K] [Fintype K] (M : Matrix n n K) :
    trace (M ^ Fintype.card K) = trace M ^ Fintype.card K := by
  cases isEmpty_or_nonempty n
  · simp [Matrix.trace]
  rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff,
    FiniteField.Matrix.charpoly_pow_card, FiniteField.pow_card]
/-
**ZMod.trace_pow_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZMod.trace_pow_card {p : Nat} [Fact p.Prime] (M : Matrix n n (ZMod p)) : t
race (M ^ p) = trace M ^ p
参数：M : Matrix n n (ZMod p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `FiniteField.trace_pow_card`：FiniteField.trace_pow_card {K : Type*} [Fiel
d K] [Fintype K] (M : Matrix n n K) : trace (M ^ Fintype.card K) = trace M ^ Fin
type.card K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
-/
theorem ZMod.trace_pow_card {p : ℕ} [Fact p.Prime] (M : Matrix n n (ZMod p)) :
    trace (M ^ p) = trace M ^ p := by have h := FiniteField.trace_pow_card M; rwa [ZMod.card] at h
