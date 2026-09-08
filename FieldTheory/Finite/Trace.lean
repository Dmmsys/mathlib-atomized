/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The trace and norm maps for finite fields

We state several lemmas about the trace and norm maps for finite fields.

## Main Results

- `trace_to_zmod_nondegenerate`: the trace map from a finite field of characteristic `p` to
  `ZMod p` is nondegenerate.
- `algebraMap_trace_eq_sum_pow`: an explicit formula for the trace map:
  `trace[L/K](x) = ∑ i < [L:K], x ^ ((#K) ^ i)`.
- `algebraMap_norm_eq_prod_pow`: an explicit formula for the norm map:
  `norm[L/K](x) = ∏ i < [L:K], x ^ ((#K) ^ i)`.

## Tags
finite field, trace, norm
-/

public section


namespace FiniteField

open Fintype

/-- The trace map from a finite field to its prime field is nondegenerate. -/
/-
**FiniteField.trace_to_zmod_nondegenerate** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField
`。
形式化陈述：trace_to_zmod_nondegenerate (F : Type*) [Field F] [Finite F] [Algebra (ZMo
d (ringChar F)) F] {a : F} (ha : a != 0) : exists b : F, Algebra.trace (ZMod (ri
ngChar F)) F (a * b) != 0
参数：F : Type*；ZMod (ringChar F)；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharP.char_is_prime`：char_is_prime (p : Nat) [CharP R p] : p.Prime
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `ringChar.charP`：∀ (R : Type u_1) [inst : NonAssocSemiring R], CharP R (r
ingChar R)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `traceForm_nondegenerate`：traceForm_nondegenerate [FiniteDimensional K L]
 [Algebra.IsSeparable K L] : (traceForm K L).Nondegenerate
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `Normal.toIsAlgebraic`：∀ {F : Type u_1} {K : Type u_2} {inst : Field F} {
inst_1 : Field K} {inst_2 : Algebra F K} [self : Normal F K],   Algebra.IsAlgebr
aic F K
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `GaloisField.instIsGaloisOfFinite`：∀ {K : Type u_2} {K' : Type u_3} [inst
 : Field K] [inst_1 : Field K'] [Finite K'] [inst_3 : Algebra K K'], IsGalois K 
K'
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
The trace map from a finite field to its prime field is nondegenerate.
-/
theorem trace_to_zmod_nondegenerate (F : Type*) [Field F] [Finite F]
    [Algebra (ZMod (ringChar F)) F] {a : F} (ha : a ≠ 0) :
    ∃ b : F, Algebra.trace (ZMod (ringChar F)) F (a * b) ≠ 0 := by
  have : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  have htr := (traceForm_nondegenerate (ZMod (ringChar F)) F).1 a
  simp_rw [Algebra.traceForm_apply] at htr
  by_contra! hf
  exact ha (htr hf)

variable (K L : Type*) [Field K] [Field L] [Finite L] [Algebra K L] (x : L)

/-- An explicit formula for the trace map: `trace[L/K](x) = ∑ i < [L:K], x ^ ((#K) ^ i)`. -/
/-
**FiniteField.algebraMap_trace_eq_sum_pow** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField
`。
形式化陈述：algebraMap_trace_eq_sum_pow : algebraMap K L (Algebra.trace K L x) = ∑ i i
n Finset.range (Module.finrank K L), x ^ (Nat.card K ^ i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `trace_eq_sum_automorphisms`：trace_eq_sum_automorphisms (x : L) [FiniteDi
mensional K L] [IsGalois K L] : algebraMap K L (Algebra.trace K L x) = ∑ σ : Gal
(L/K), σ x
· 使用定理 `GaloisField.instIsGaloisOfFinite`：∀ {K : Type u_2} {K' : Type u_3} [inst
 : Field K] [inst_1 : Field K'] [Finite K'] [inst_3 : Algebra K K'], IsGalois K 
K'
· 使用定理 `Finset.sum_range`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} (f :
 ℕ → M), ∑ i ∈ Finset.range n, f i = ∑ i, f ↑i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.sum_bijective`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [i
nst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι → κ), 
Function.Bi…
· 使用定理 `FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow`：bijective_froben
iusAlgEquivOfAlgebraic_pow : Function.Bijective fun n : Fin (Module.finrank K L)
 => frobeniusAlgEquivOfAlgebraic K L ^ n.1
· 使用定理 `AlgEquiv.coe_pow`：∀ {R : Type uR} {A₁ : Type uA₁} [inst : CommSemiring R
] [inst_1 : Semiring A₁] [inst_2 : Algebra R A₁] (e : A₁ ≃ₐ[R] A₁)   (n : ℕ), ⇑(
e ^ n)…
· 使用引理 `FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate`：coe_frobeniusAlgEq
uivOfAlgebraic_iterate [Algebra.IsAlgebraic K L] (n : Nat) : (⇑(frobeniusAlgEqui
vOfAlgebraic K L))^[n] = (· ^ (Fintype.car…
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α

--- 原说明 ---
An explicit formula for the trace map: `trace[L/K](x) = ∑ i < [L:K], x ^ ((#K) ^
 i)`.
-/
theorem algebraMap_trace_eq_sum_pow :
    algebraMap K L (Algebra.trace K L x) =
      ∑ i ∈ Finset.range (Module.finrank K L), x ^ (Nat.card K ^ i) := by
  have := Finite.of_injective _ (FaithfulSMul.algebraMap_injective K L)
  have := ofFinite K
  rw [trace_eq_sum_automorphisms, Finset.sum_range]
  exact Eq.symm <| sum_bijective _ (bijective_frobeniusAlgEquivOfAlgebraic_pow K L) _ _ <|
    fun i ↦ by rw [AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate, card_eq_nat_card]

/-- An explicit formula for the norm map: `norm[L/K](x) = ∏ i < [L:K], x ^ ((#K) ^ i)`. -/
/-
**FiniteField.algebraMap_norm_eq_prod_pow** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField
`。
形式化陈述：algebraMap_norm_eq_prod_pow : algebraMap K L (Algebra.norm K x) = ∏ i in F
inset.range (Module.finrank K L), x ^ (Nat.card K ^ i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.norm_eq_prod_automorphisms`：norm_eq_prod_automorphisms [IsGalois
 K L] (x : L) : algebraMap K L (norm K x) = ∏ σ : Gal(L/K), σ x
· 使用定理 `GaloisField.instIsGaloisOfFinite`：∀ {K : Type u_2} {K' : Type u_3} [inst
 : Field K] [inst_1 : Field K'] [Finite K'] [inst_3 : Algebra K K'], IsGalois K 
K'
· 使用定理 `Finset.prod_range`：prod_range [CommMonoid M] {n : Nat} (f : Nat -> M) : 
∏ i in Finset.range n, f i = ∏ i : Fin n, f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Fintype.prod_bijective`：prod_bijective (e : ι -> κ) (he : e.Bijective) (
f : ι -> M) (g : κ -> M) (h : forall x, f x = g (e x)) : ∏ x, f x = ∏ x, g x
· 使用定理 `FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow`：bijective_froben
iusAlgEquivOfAlgebraic_pow : Function.Bijective fun n : Fin (Module.finrank K L)
 => frobeniusAlgEquivOfAlgebraic K L ^ n.1
· 使用定理 `AlgEquiv.coe_pow`：∀ {R : Type uR} {A₁ : Type uA₁} [inst : CommSemiring R
] [inst_1 : Semiring A₁] [inst_2 : Algebra R A₁] (e : A₁ ≃ₐ[R] A₁)   (n : ℕ), ⇑(
e ^ n)…
· 使用引理 `FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate`：coe_frobeniusAlgEq
uivOfAlgebraic_iterate [Algebra.IsAlgebraic K L] (n : Nat) : (⇑(frobeniusAlgEqui
vOfAlgebraic K L))^[n] = (· ^ (Fintype.car…
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α

--- 原说明 ---
An explicit formula for the norm map: `norm[L/K](x) = ∏ i < [L:K], x ^ ((#K) ^ i
)`.
-/
theorem algebraMap_norm_eq_prod_pow :
    algebraMap K L (Algebra.norm K x) =
      ∏ i ∈ Finset.range (Module.finrank K L), x ^ (Nat.card K ^ i) := by
  have := Finite.of_injective _ (FaithfulSMul.algebraMap_injective K L)
  have := ofFinite K
  rw [Algebra.norm_eq_prod_automorphisms, Finset.prod_range]
  exact Eq.symm <| prod_bijective _ (bijective_frobeniusAlgEquivOfAlgebraic_pow K L) _ _ <|
    fun i ↦ by rw [AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate, card_eq_nat_card]

/-- An explicit formula for the norm map: `norm[L/K](x) = x ^ (∑ i < [L:K], (#K) ^ i)`. -/
/-
**FiniteField.algebraMap_norm_eq_pow_sum** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`
。
形式化陈述：algebraMap_norm_eq_pow_sum : algebraMap K L (Algebra.norm K x) = x ^ ∑ i i
n Finset.range (Module.finrank K L), Nat.card K ^ i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteField.algebraMap_norm_eq_prod_pow`：algebraMap_norm_eq_prod_pow : a
lgebraMap K L (Algebra.norm K x) = ∏ i in Finset.range (Module.finrank K L), x ^
 (Nat.card K ^ i)
· 使用引理 `Finset.prod_pow_eq_pow_sum`：prod_pow_eq_pow_sum (s : Finset ι) (f : ι ->
 Nat) (a : M) : ∏ i in s, a ^ f i = a ^ ∑ i in s, f i

--- 原说明 ---
An explicit formula for the norm map: `norm[L/K](x) = x ^ (∑ i < [L:K], (#K) ^ i
)`.
-/
theorem algebraMap_norm_eq_pow_sum :
    algebraMap K L (Algebra.norm K x) =
      x ^ ∑ i ∈ Finset.range (Module.finrank K L), Nat.card K ^ i := by
  rw [algebraMap_norm_eq_prod_pow, Finset.prod_pow_eq_pow_sum]

end FiniteField

