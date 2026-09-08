/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.NumberTheory.ArithmeticFunction.Misc


/-!
# Lemmas on infinite sums over the antidiagonal of the divisors function

This file contains lemmas about the antidiagonal of the divisors function. It defines the map from
`Nat.divisorsAntidiagonal n` to `ℕ+ × ℕ+` given by sending `n = a * b` to `(a, b)`.

We then prove some identities about the infinite sums over this antidiagonal, such as
`∑' n : ℕ+, n ^ k * r ^ n / (1 - r ^ n) = ∑' n : ℕ+, σ k n * r ^ n`
which are used for Eisenstein series and their q-expansions. This is also a special case of
Lambert series.

-/

@[expose] public section

open Filter Complex ArithmeticFunction Nat Topology

/-- The map from `Nat.divisorsAntidiagonal n` to `ℕ+ × ℕ+` given by sending `n = a * b`
to `(a, b)`. -/
/-
**divisorsAntidiagonalFactors** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：divisorsAntidiagonalFactors (n : Nat+) : Nat.divisorsAntidiagonal n -> Nat
+ × Nat+
参数：n : Nat+。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from `Nat.divisorsAntidiagonal n` to `ℕ+ × ℕ+` given by sending `n = a *
 b`
to `(a, b)`.
-/
def divisorsAntidiagonalFactors (n : ℕ+) : Nat.divisorsAntidiagonal n → ℕ+ × ℕ+ := fun x ↦
  ⟨⟨x.1.1, Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal x.2)⟩,
    (⟨x.1.2, Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal x.2)⟩ : ℕ+),
    Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal x.2)⟩
/-
**divisorsAntidiagonalFactors_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：divisorsAntidiagonalFactors_eq {n : Nat+} (x : Nat.divisorsAntidiagonal n)
 : (divisorsAntidiagonalFactors n x).1.1 * (divisorsAntidiagonalFactors n x).2.1
 = n
参数：x : Nat.divisorsAntidiagonal n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_divisorsAntidiagonal`：mem_divisorsAntidiagonal {x : Nat × Nat} :
 x in divisorsAntidiagonal n ↔ x.fst * x.snd = n ∧ n != 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma divisorsAntidiagonalFactors_eq {n : ℕ+} (x : Nat.divisorsAntidiagonal n) :
    (divisorsAntidiagonalFactors n x).1.1 * (divisorsAntidiagonalFactors n x).2.1 = n := by
  simp [divisorsAntidiagonalFactors, (Nat.mem_divisorsAntidiagonal.mp x.2).1]
/-
**divisorsAntidiagonalFactors_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：divisorsAntidiagonalFactors_one (x : Nat.divisorsAntidiagonal 1) : (diviso
rsAntidiagonalFactors 1 x) = (1, 1)
参数：x : Nat.divisorsAntidiagonal 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_divisorsAntidiagonal`：mem_divisorsAntidiagonal {x : Nat × Nat} :
 x in divisorsAntidiagonal n ↔ x.fst * x.snd = n ∧ n != 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma divisorsAntidiagonalFactors_one (x : Nat.divisorsAntidiagonal 1) :
    (divisorsAntidiagonalFactors 1 x) = (1, 1) := by
  have h := Nat.mem_divisorsAntidiagonal.mp x.2
  simp only [mul_eq_one, ne_eq, one_ne_zero, not_false_eq_true, and_true] at h
  simp [divisorsAntidiagonalFactors, h.1, h.2]

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence from the union over `n` of `Nat.divisorsAntidiagonal n` to `ℕ+ × ℕ+`
given by sending `n = a * b` to `(a, b)`. -/
/-
**sigmaAntidiagonalEquivProd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：sigmaAntidiagonalEquivProd : (Σ n : Nat+, Nat.divisorsAntidiagonal n) ≃ Na
t+ × Nat+ where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence from the union over `n` of `Nat.divisorsAntidiagonal n` to `ℕ+ ×
 ℕ+`
given by sending `n = a * b` to `(a, b)`.
-/
def sigmaAntidiagonalEquivProd : (Σ n : ℕ+, Nat.divisorsAntidiagonal n) ≃ ℕ+ × ℕ+ where
  toFun x := divisorsAntidiagonalFactors x.1 x.2
  invFun x :=
    ⟨⟨x.1.val * x.2.val, mul_pos x.1.2 x.2.2⟩, ⟨x.1, x.2⟩, by simp [Nat.mem_divisorsAntidiagonal]⟩
  left_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    rw [Nat.mem_divisorsAntidiagonal] at h
    ext <;> simp [divisorsAntidiagonalFactors, ← PNat.coe_injective.eq_iff, h.1]
  right_inv _ := rfl
/-
**sigmaAntidiagonalEquivProd_symm_apply_fst** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sigmaAntidiagonalEquivProd_symm_apply_fst (x : Nat+ × Nat+) : (sigmaAntidi
agonalEquivProd.symm x).1 = x.1.1 * x.2.1
参数：x : Nat+ × Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma sigmaAntidiagonalEquivProd_symm_apply_fst (x : ℕ+ × ℕ+) :
    (sigmaAntidiagonalEquivProd.symm x).1 = x.1.1 * x.2.1 := rfl
/-
**sigmaAntidiagonalEquivProd_symm_apply_snd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sigmaAntidiagonalEquivProd_symm_apply_snd (x : Nat+ × Nat+) : (sigmaAntidi
agonalEquivProd.symm x).2 = (x.1.1, x.2.1)
参数：x : Nat+ × Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma sigmaAntidiagonalEquivProd_symm_apply_snd (x : ℕ+ × ℕ+) :
    (sigmaAntidiagonalEquivProd.symm x).2 = (x.1.1, x.2.1) := rfl

section tsum

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormSMulClass ℤ 𝕜]

omit [NormSMulClass ℤ 𝕜] in
/-
**summable_norm_pow_mul_geometric_div_one_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：summable_norm_pow_mul_geometric_div_one_sub (k : Nat) {r : 𝕜} (hr : ‖r‖ < 
1) : Summable fun n : Nat => n ^ k * r ^ n / (1 - r ^ n)
参数：k : Nat；hr : ‖r‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_one_div`：div_eq_mul_one_div (a b : G) : a / b = a * (1 / b)
· 使用引理 `Summable.mul_tendsto_const`：Summable.mul_tendsto_const {F ι : Type*} [No
rmedRing F] [NormMulClass F] [NormOneClass F] [CompleteSpace F] {f g : ι -> F} (
hf : Summable fu…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `summable_norm_pow_mul_geometric_of_norm_lt_one`：summable_norm_pow_mul_ge
ometric_of_norm_lt_one (k : Nat) {r : R} (hr : ‖r‖ < 1) : Summable fun n : Nat =
> ‖((n : R) ^ k * r ^ n : R)‖
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
· 使用定理 `Filter.Tendsto.div`：Filter.Tendsto.div {l : Filter α} {a b : G₀} (hf : T
endsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (hy : b != 0) : Tendsto (f / g) l (𝓝 
(a / b))
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Tendsto.const_sub`：∀ {G : Type w} {α : Type u} [inst : Topologica
lSpace G] [inst_1 : Sub G] [ContinuousSub G] (b : G) {c : G} {f : α → G}   {l : 
Filter α}, Fil…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`：tendsto_pow_atTop_nhds_zero_
of_norm_lt_one {R : Type*} [SeminormedRing R] {x : R} (h : ‖x‖ < 1) : Tendsto (f
un n : Nat => x ^ n) atTop (𝓝 0)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma summable_norm_pow_mul_geometric_div_one_sub (k : ℕ) {r : 𝕜} (hr : ‖r‖ < 1) :
    Summable fun n : ℕ ↦ n ^ k * r ^ n / (1 - r ^ n) := by
  simp only [div_eq_mul_one_div (_ * _ ^ _)]
  apply Summable.mul_tendsto_const (c := 1 / (1 - 0))
    (by simpa using! summable_norm_pow_mul_geometric_of_norm_lt_one k hr)
  simpa only [Nat.cofinite_eq_atTop] using!
   tendsto_const_nhds.div ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr).const_sub 1) (by simp)
/-
**summable_divisorsAntidiagonal_aux** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma summable_divisorsAntidiagonal_aux (k : ℕ) {r : 𝕜} (hr : ‖r‖ < 1) :
    Summable fun c : (n : ℕ+) × {x // x ∈ (n : ℕ).divisorsAntidiagonal} ↦
    (c.2.1.2) ^ k * (r ^ (c.2.1.1 * c.2.1.2)) := by
  apply Summable.of_norm
  rw [summable_sigma_of_nonneg (fun a ↦ by positivity)]
  constructor
  · exact fun n ↦ (hasSum_fintype _).summable
  · simp only [norm_mul, norm_pow, tsum_fintype, Finset.univ_eq_attach]
    apply Summable.of_nonneg_of_le (f := fun c : ℕ+ ↦ ‖(c : 𝕜) ^ (k + 1) * r ^ (c : ℕ)‖)
      (fun b ↦ Finset.sum_nonneg (fun _ _ ↦ mul_nonneg (by simp) (by simp))) (fun b ↦ ?_)
      (by apply (summable_norm_pow_mul_geometric_of_norm_lt_one (k + 1) hr).subtype)
    transitivity ∑ _ ∈ (b : ℕ).divisors, ‖(b : 𝕜)‖ ^ k * ‖r ^ (b : ℕ)‖
    · rw [(b : ℕ).divisorsAntidiagonal.sum_attach (fun x ↦ ‖(x.2 : 𝕜)‖ ^ _ * _ ^ (x.1 * x.2)),
          sum_divisorsAntidiagonal ((fun x y ↦ ‖(y : 𝕜)‖ ^ k * _ ^ (x * y)))]
      gcongr with i hi
      · simpa using! le_of_dvd b.2 (div_dvd_of_dvd (dvd_of_mem_divisors hi))
      · rw [norm_pow, mul_comm, Nat.div_mul_cancel (dvd_of_mem_divisors hi)]
    · simp only [norm_pow, Finset.sum_const, nsmul_eq_mul, ← mul_assoc, add_comm k 1, pow_add,
        pow_one, norm_mul]
      gcongr
      simpa using! Nat.card_divisors_le_self b
/-
**summable_prod_mul_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_prod_mul_pow (k : Nat) {r : 𝕜} (hr : ‖r‖ < 1) : Summable fun c : 
(Nat+ × Nat+) => c.2 ^ k * (r ^ (c.1 * c.2 : Nat))
参数：k : Nat；hr : ‖r‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.summable_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst
 : AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   (e : γ ≃ β), Sum
mable (f…
· 使用定理 `_private.Mathlib.NumberTheory.TsumDivisorsAntidiagonal.0.summable_diviso
rsAntidiagonal_aux`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] [Complet
eSpace 𝕜] [NormSMulClass ℤ 𝕜] (k : ℕ) {r : 𝕜},   ‖r‖ < 1 → Summable fun c => ↑(↑
…
-/
theorem summable_prod_mul_pow (k : ℕ) {r : 𝕜} (hr : ‖r‖ < 1) :
    Summable fun c : (ℕ+ × ℕ+) ↦ c.2 ^ k * (r ^ (c.1 * c.2 : ℕ)) := by
  simpa [sigmaAntidiagonalEquivProd.summable_iff.symm] using! summable_divisorsAntidiagonal_aux k hr

-- access notation `σ`
open scoped sigma
/-
**tsum_prod_pow_eq_tsum_sigma** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_prod_pow_eq_tsum_sigma (k : Nat) {r : 𝕜} (hr : ‖r‖ < 1) : ∑' d : Nat+
, ∑' c : Nat+, c ^ k * r ^ (d * c : Nat) = ∑' e : Nat+, σ k e * r ^ (e : Nat)
参数：k : Nat；hr : ‖r‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用定理 `Summable.tsum_sigma`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommGrou
p α] [inst_1 : UniformSpace α] [IsUniformAddGroup α]   [CompleteSpace α] [T0Spac
e α] {γ :…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `_private.Mathlib.NumberTheory.TsumDivisorsAntidiagonal.0.summable_diviso
rsAntidiagonal_aux`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] [Complet
eSpace 𝕜] [NormSMulClass ℤ 𝕜] (k : ℕ) {r : 𝕜},   ‖r‖ < 1 → Summable fun c => ↑(↑
…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ArithmeticFunction.sigma_eq_sum_div`：sigma_eq_sum_div (k n : Nat) : sigm
a k n = ∑ d in divisors n, (n / d) ^ k
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `Nat.sum_divisorsAntidiagonal`：∀ {M : Type u_1} [inst : AddCommMonoid M] 
(f : ℕ → ℕ → M) {n : ℕ},   ∑ i ∈ n.divisorsAntidiagonal, f i.1 i.2 = ∑ i ∈ n.div
isors, f i (n / i)
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
（共 33 条，此处仅展示前 30 条）
-/
theorem tsum_prod_pow_eq_tsum_sigma (k : ℕ) {r : 𝕜} (hr : ‖r‖ < 1) :
    ∑' d : ℕ+, ∑' c : ℕ+, c ^ k * r ^ (d * c : ℕ) = ∑' e : ℕ+, σ k e * r ^ (e : ℕ) := by
  suffices ∑' c : ℕ+ × ℕ+, c.2 ^ k * r ^ (c.1 * c.2 : ℕ) =
    ∑' e : ℕ+, σ k e * r ^ (e : ℕ) by rwa [← (summable_prod_mul_pow k hr).tsum_prod]
  simp only [← sigmaAntidiagonalEquivProd.tsum_eq, sigmaAntidiagonalEquivProd,
    divisorsAntidiagonalFactors, PNat.mk_coe, Equiv.coe_fn_mk, sigma_eq_sum_div, cast_sum,
    cast_pow, Summable.tsum_sigma (summable_divisorsAntidiagonal_aux k hr :)]
  refine tsum_congr fun n ↦ ?_
  simpa [tsum_fintype, Finset.sum_mul,
    (n : ℕ).divisorsAntidiagonal.sum_attach fun x : ℕ × ℕ ↦ x.2 ^ k * r ^ (x.1 * x.2),
    sum_divisorsAntidiagonal fun x y ↦ y ^ k * r ^ (x * y)]
      using Finset.sum_congr rfl fun i hi ↦ by rw [Nat.mul_div_cancel' (dvd_of_mem_divisors hi)]
/-
**tsum_pow_div_one_sub_eq_tsum_sigma** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tsum_pow_div_one_sub_eq_tsum_sigma {r : 𝕜} (hr : ‖r‖ < 1) (k : Nat) : ∑' n
 : Nat+, n ^ k * r ^ (n : Nat) / (1 - r ^ (n : Nat)) = ∑' n : Nat+, σ k n * r ^ 
(n : Nat)
参数：hr : ‖r‖ < 1；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_geometric_of_norm_lt_one`：tsum_geometric_of_norm_lt_one (h : ‖ξ‖ < 
1) : ∑' n : Nat, ξ ^ n = (1 - ξ)⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `pow_lt_one₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preo
rder M₀] {a : M₀} [PosMulMono M₀],   0 ≤ a → a < 1 → ∀ {n : ℕ}, n ≠ 0 → a ^ n < 
1
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NeZero.pnat`：∀ {a : ℕ+}, NeZero ↑a
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `tsum_pnat_eq_tsum_succ`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_
1 : TopologicalSpace M] {f : ℕ → M},   ∑' (n : ℕ+), f ↑n = ∑' (n : ℕ), f (n + 1)
· 使用定理 `tsum_prod_pow_eq_tsum_sigma`：tsum_prod_pow_eq_tsum_sigma (k : Nat) {r : 
𝕜} (hr : ‖r‖ < 1) : ∑' d : Nat+, ∑' c : Nat+, c ^ k * r ^ (d * c : Nat) = ∑' e :
 Nat+, σ k e * r …
· 使用定理 `Summable.tsum_comm`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst
 : AddCommGroup α] [inst_1 : UniformSpace α] [IsUniformAddGroup α]   [CompleteSp
ace α] […
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
（共 38 条，此处仅展示前 30 条）
-/
lemma tsum_pow_div_one_sub_eq_tsum_sigma {r : 𝕜} (hr : ‖r‖ < 1) (k : ℕ) :
    ∑' n : ℕ+, n ^ k * r ^ (n : ℕ) / (1 - r ^ (n : ℕ)) = ∑' n : ℕ+, σ k n * r ^ (n : ℕ) := by
  have (m : ℕ) [NeZero m] := tsum_geometric_of_norm_lt_one (ξ := r ^ m)
    (by simpa using pow_lt_one₀ (by simp) hr (NeZero.ne _))
  simp only [div_eq_mul_inv, ← this, ← tsum_mul_left, mul_assoc, ← _root_.pow_succ',
    ← fun (n : ℕ) ↦ tsum_pnat_eq_tsum_succ (f := fun m ↦ n ^ k * (r ^ n) ^ m)]
  have h00 := tsum_prod_pow_eq_tsum_sigma k hr
  rw [Summable.tsum_comm (by apply (summable_prod_mul_pow k hr).prod_symm)] at h00
  rw [← h00]
  exact tsum_congr₂ <| fun b c ↦ by simp [mul_comm c.val b.val, pow_mul]

omit [CompleteSpace 𝕜] [NormSMulClass ℤ 𝕜] in
/-
**tendsto_zero_geometric_tsum_pnat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_zero_geometric_tsum_pnat {r : 𝕜} (hr : ‖r‖ < 1) : Tendsto (fun m :
 Nat+ => ∑' n : Nat+, r ^ (n * m : Nat)) atTop (𝓝 0)
参数：hr : ‖r‖ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `pow_lt_one_iff_of_nonneg`：pow_lt_one_iff_of_nonneg (ha : 0 <= a) (hn : n
 != 0) : a ^ n < 1 ↔ a < 1
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `NeZero.pnat`：∀ {a : ℕ+}, NeZero ↑a
· 使用定理 `tsum_geometric_of_norm_lt_one`：tsum_geometric_of_norm_lt_one (h : ‖ξ‖ < 
1) : ∑' n : Nat, ξ ^ n = (1 - ξ)⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsum_zero_pnat_eq_tsum_nat`：∀ {G : Type u_2} [inst : AddCommGroup G] [in
st_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {f : ℕ → G}, 
Summable f → f 0…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `summable_geometric_of_norm_lt_one`：summable_geometric_of_norm_lt_one {K 
: Type*} [NormedRing K] [HasSummableGeomSeries K] {x : K} (h : ‖x‖ < 1) : Summab
le (fun n => x ^ n)
· 使用定理 `instHasSummableGeomSeries`：∀ {K : Type u_4} [inst : NormedDivisionRing K
], HasSummableGeomSeries K
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Filter.tendsto_sub_const_iff`：∀ {α : Type u} {G : Type u_1} [inst : Topo
logicalSpace G] [inst_1 : AddGroup G] [ContinuousSub G] (b : G) {c : G}   {f : α
 → G} {l : Filter …
（共 40 条，此处仅展示前 30 条）
-/
lemma tendsto_zero_geometric_tsum_pnat {r : 𝕜} (hr : ‖r‖ < 1) :
    Tendsto (fun m : ℕ+ ↦ ∑' n : ℕ+, r ^ (n * m : ℕ)) atTop (𝓝 0) := by
  have h1 (m : ℕ+) : ‖r ^ (m : ℕ)‖ < 1 := by
    rwa [norm_pow, pow_lt_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne _)]
  have h2 (m : ℕ+) : ∑' n : ℕ+, r ^ (n * m : ℕ) = (1 - r ^ (m : ℕ))⁻¹ - 1 := by
    have := tsum_geometric_of_norm_lt_one (h1 m)
    rw [← tsum_zero_pnat_eq_tsum_nat (summable_geometric_of_norm_lt_one (h1 m) :)] at this
    simp_rw [← this, pow_zero, add_sub_cancel_left, mul_comm, pow_mul]
  rw [funext h2, (by simp : 𝓝 (0 : 𝕜) = 𝓝 ((1 - 0)⁻¹ - 1)), tendsto_sub_const_iff,
    tendsto_inv_iff₀ (by simp), tendsto_const_sub_iff]
  exact (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr).comp <| tendsto_PNat_val_atTop_atTop

end tsum

