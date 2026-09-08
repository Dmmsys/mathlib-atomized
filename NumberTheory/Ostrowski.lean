/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Fabrizio Barroero, Laura Capuano, Nirvana Coppola,
María Inés de Frutos-Fernández, Sam van Gool, Silvain Rideau-Kikuchi, Amos Turchet,
Francesco Veneziano
-/
module

public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.NumberTheory.Padics.PadicNorm

/-!
# Ostrowski’s Theorem

Ostrowski's Theorem for the field `ℚ`: every absolute value on `ℚ` is equivalent to either a
`p`-adic absolute value or to the standard Archimedean (Euclidean) absolute value.

## Main results

- `Rat.AbsoluteValue.equiv_real_or_padic`: given an absolute value on `ℚ`, it is equivalent
  to the standard Archimedean (Euclidean) absolute value `Rat.AbsoluteValue.real` or to a `p`-adic
  absolute value `Rat.AbsoluteValue.padic p` for a unique prime number `p`.

## TODO

Extend to arbitrary number fields.

## References

* [K. Conrad, *Ostrowski's Theorem for Q*][conradQ]
* [K. Conrad, *Ostrowski for number fields*][conradnumbfield]
* [J. W. S. Cassels, *Local fields*][cassels1986local]

## Tags

absolute value, Ostrowski's theorem
-/

@[expose] public section

open Filter Nat Real Topology

-- For any `C > 0`, the limit of `C ^ (1/k)` is 1 as `k → ∞`
/-
**tendsto_const_rpow_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma tendsto_const_rpow_inv {C : ℝ} (hC : 0 < C) :
    Tendsto (fun k : ℕ ↦ C ^ (k : ℝ)⁻¹) atTop (𝓝 1) :=
  ((continuous_iff_continuousAt.mpr fun _ ↦ continuousAt_const_rpow hC.ne').tendsto'
    0 1 (rpow_zero C)).comp <| tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

--extends the lemma `tendsto_rpow_div` when the function has natural input
/-
**tendsto_nat_rpow_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma tendsto_nat_rpow_inv :
    Tendsto (fun k : ℕ ↦ (k : ℝ) ^ (k : ℝ)⁻¹) atTop (𝓝 1) := by
  simp_rw [← one_div]
  exact Tendsto.comp tendsto_rpow_div tendsto_natCast_atTop_atTop

-- Multiplication by a constant moves in a List.sum
/-
**list_mul_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma list_mul_sum {R : Type*} [Semiring R] {T : Type*} (l : List T) (y : R) (x : R) :
    (l.mapIdx fun i _ => x * y ^ i).sum = x * (l.mapIdx fun i _ => y ^ i).sum := by
  simp_rw [← smul_eq_mul, List.smul_sum, List.mapIdx_eq_zipIdx_map]
  congr 1
  simp

-- Geometric sum for lists
/-
**list_geom** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma list_geom {T : Type*} {F : Type*} [DivisionRing F] (l : List T) {y : F} (hy : y ≠ 1) :
    (l.mapIdx fun i _ => y ^ i).sum = (y ^ l.length - 1) / (y - 1) := by
  rw [← geom_sum_eq hy l.length, List.mapIdx_eq_zipIdx_map, Finset.sum_range,
    ← Fin.sum_univ_fun_getElem]
  simp only
  let e : Fin l.zipIdx.length ≃ Fin l.length := finCongr List.length_zipIdx
  exact Fintype.sum_bijective e e.bijective _ _ fun _ ↦ by simp [e]

open AbsoluteValue -- does not work as intended after `namespace Rat.AbsoluteValue`

namespace Rat.AbsoluteValue

/-!
### Preliminary lemmas
-/

open Int

variable {f g : AbsoluteValue ℚ ℝ}

/-- Values of an absolute value on the rationals are determined by the values on the natural
numbers. -/
/-
**Rat.AbsoluteValue.eq_on_nat_iff_eq** 是 Mathlib 中的一个引理，位于命名空间 `Rat.AbsoluteValu
e`。
形式化陈述：eq_on_nat_iff_eq : (forall n : Nat, f n = g n) ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbsoluteValue.ext`：ext ⦃f g : AbsoluteValue R S⦄ : (forall x, f x = g x)
 -> f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Rat.num_div_den`：num_div_den (r : Rat) : (r.num : Rat) / (r.den : Rat) =
 r
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AbsoluteValue.eq_on_nat_iff_eq_on_int`：eq_on_nat_iff_eq_on_int {f g : Ab
soluteValue R S} : (forall n : Nat, f n = g n) ↔ forall n : Int, f n = g n
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a

--- 原说明 ---
Values of an absolute value on the rationals are determined by the values on the
 natural
numbers.
-/
lemma eq_on_nat_iff_eq : (∀ n : ℕ, f n = g n) ↔ f = g := by
  refine ⟨fun h ↦ ?_, fun h n ↦ congrFun (congrArg DFunLike.coe h) ↑n⟩
  ext1 z
  rw [← Rat.num_div_den z, map_div₀, map_div₀, h, eq_on_nat_iff_eq_on_int.mp h]

/-- The equivalence class of an absolute value on the rationals is determined by its values on
the natural numbers. -/
/-
**Rat.AbsoluteValue.exists_nat_rpow_iff_isEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Rat.A
bsoluteValue`。
形式化陈述：exists_nat_rpow_iff_isEquiv : (exists c : Real, 0 < c ∧ forall n : Nat, f 
n ^ c = g n) ↔ f.IsEquiv g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AbsoluteValue.isEquiv_iff_exists_rpow_eq`：isEquiv_iff_exists_rpow_eq {v 
w : AbsoluteValue F Real} : v.IsEquiv w ↔ exists c : Real, 0 < c ∧ (v · ^ c) = w
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Rat.num_div_den`：num_div_den (r : Rat) : (r.num : Rat) / (r.den : Rat) =
 r
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Real.div_rpow`：div_rpow (hx : 0 <= x) (hy : 0 <= y) (z : Real) : (x / y)
 ^ z = x ^ z / y ^ z
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用引理 `AbsoluteValue.apply_natAbs_eq`：apply_natAbs_eq (x : Int) : abv (natAbs x
) = abv x
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a

--- 原说明 ---
The equivalence class of an absolute value on the rationals is determined by its
 values on
the natural numbers.
-/
lemma exists_nat_rpow_iff_isEquiv : (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, f n ^ c = g n) ↔ f.IsEquiv g := by
  rw [isEquiv_iff_exists_rpow_eq]
  refine ⟨fun ⟨c, hc, h⟩ ↦ ⟨c, hc, ?_⟩, fun ⟨c, hc, h⟩ ↦ ⟨c, hc, (congrFun h ·)⟩⟩
  ext1 x
  rw [← Rat.num_div_den x, map_div₀, map_div₀, div_rpow (by positivity) (by positivity), h x.den,
    ← apply_natAbs_eq, ← apply_natAbs_eq, h (natAbs x.num)]

section Non_archimedean

/-!
### The non-archimedean case

Every bounded absolute value on `ℚ` is equivalent to a `p`-adic absolute value.
-/

/-- The real-valued `AbsoluteValue` corresponding to the p-adic norm on `ℚ`. -/
/-
**Rat.AbsoluteValue.padic** 是 Mathlib 中的一个定义，位于命名空间 `Rat.AbsoluteValue`。
形式化陈述：padic (p : Nat) [Fact p.Prime] : AbsoluteValue Rat Real where toFun x
参数：p : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The real-valued `AbsoluteValue` corresponding to the p-adic norm on `ℚ`.
-/
def padic (p : ℕ) [Fact p.Prime] : AbsoluteValue ℚ ℝ where
  toFun x := (padicNorm p x : ℝ)
  map_mul' := by simp only [padicNorm.mul, Rat.cast_mul, forall_const]
  nonneg' x := cast_nonneg.mpr <| padicNorm.nonneg x
  eq_zero' _ :=
    ⟨fun H ↦ padicNorm.zero_of_padicNorm_eq_zero <| cast_eq_zero.mp H,
      fun H ↦ cast_eq_zero.mpr <| H ▸ padicNorm.zero (p := p)⟩
  add_le' := mod_cast padicNorm.triangle_ineq
/-
**Rat.AbsoluteValue.padic_eq_padicNorm** 是 Mathlib 中的一个定理，位于命名空间 `Rat.AbsoluteVa
lue`。
形式化陈述：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (r : ℚ), (Rat.AbsoluteValue.padic p)
 r = ↑(padicNorm p r)
参数：p : ℕ；Nat.Prime p；r : ℚ；Rat.AbsoluteValue.padic p；padicNorm p r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma padic_eq_padicNorm (p : ℕ) [Fact p.Prime] (r : ℚ) : padic p r = padicNorm p r := rfl
/-
**Rat.AbsoluteValue.padic_le_one** 是 Mathlib 中的一个引理，位于命名空间 `Rat.AbsoluteValue`。
形式化陈述：padic_le_one (p : Nat) [Fact p.Prime] (n : Int) : padic p n <= 1
参数：p : Nat；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `padicNorm.of_int`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (z : ℤ), padicNorm
 p ↑z ≤ 1
-/
lemma padic_le_one (p : ℕ) [Fact p.Prime] (n : ℤ) : padic p n ≤ 1 := by
  simp only [padic_eq_padicNorm]
  exact_mod_cast padicNorm.of_int n

-- ## Step 1: define `p = minimal n s. t. 0 < f n < 1`

variable (hf_nontriv : f.IsNontrivial) (bdd : ∀ n : ℕ, f n ≤ 1)

include hf_nontriv bdd in
/-- There exists a minimal positive integer with absolute value smaller than 1. -/
/-
**Rat.AbsoluteValue.exists_minimal_nat_zero_lt_and_lt_one** 是 Mathlib 中的一个引理，位于命
名空间 `Rat.AbsoluteValue`。
形式化陈述：exists_minimal_nat_zero_lt_and_lt_one : exists p : Nat, (0 < f p ∧ f p < 1
) ∧ forall m : Nat, 0 < f m ∧ f m < 1 -> p <= m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用引理 `AbsoluteValue.isNontrivial_iff_ne_trivial`：isNontrivial_iff_ne_trivial [
DecidablePred fun x : R => x = 0] [NoZeroDivisors R] [Nontrivial S] (v : Absolut
eValue R S) : v.IsNontrivial ↔ …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Rat.AbsoluteValue.eq_on_nat_iff_eq`：eq_on_nat_iff_eq : (forall n : Nat, 
f n = g n) ↔ f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `AbsoluteValue.map_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring
 R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S),
 abv 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `AbsoluteValue.trivial_apply`：trivial_apply {x : R} (hx : x != 0) : Absol
uteValue.trivial (S
· 使用定理 `map_pos_of_ne_zero`：∀ {F : Type u_2} {α : Type u_3} {β : Type u_4} [inst
 : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoid β]   [inst_3 : L
inearOrd…
· 使用定理 `MulRingNormClass.toAddGroupNormClass`：∀ {F : Type u_7} {α : outParam (Ty
pe u_8)} {β : outParam (Type u_9)} [inst : NonAssocRing α] [inst_1 : Semiring β]
   [inst_2 : PartialOrder …
· 使用定理 `AbsoluteValue.instMulRingNormClassOfNontrivialOfIsDomain`：∀ {R : Type u_
3} {S : Type u_4} [inst : CommRing S] [inst_1 : PartialOrder S] [IsOrderedRing S
] [inst_3 : Ring R]   [NoZeroDivisors S] [Nont…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Nat.sInf_mem`：sInf_mem {s : Set Nat} (h : s.Nonempty) : sInf s in s
· 使用定理 `Nat.sInf_le`：∀ {s : Set ℕ} {m : ℕ}, m ∈ s → sInf s ≤ m

--- 原说明 ---
There exists a minimal positive integer with absolute value smaller than 1.
-/
lemma exists_minimal_nat_zero_lt_and_lt_one :
    ∃ p : ℕ, (0 < f p ∧ f p < 1) ∧ ∀ m : ℕ, 0 < f m ∧ f m < 1 → p ≤ m := by
  -- There is a positive integer with absolute value different from one.
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, n ≠ 0 ∧ f n ≠ 1 := by
    contrapose! hf_nontriv
    refine (isNontrivial_iff_ne_trivial f).not_left.mpr <| eq_on_nat_iff_eq.mp fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hf_nontriv, hn]
  set P := {m : ℕ | 0 < f ↑m ∧ f ↑m < 1} -- p is going to be the minimum of this set.
  have hP : P.Nonempty :=
    ⟨n, map_pos_of_ne_zero f (Nat.cast_ne_zero.mpr hn1), lt_of_le_of_ne (bdd n) hn2⟩
  exact ⟨sInf P, Nat.sInf_mem hP, fun _ hm ↦ Nat.sInf_le hm⟩

-- ## Step 2: p is prime

variable {p : ℕ} (hp0 : 0 < f p) (hp1 : f p < 1) (hmin : ∀ m : ℕ, 0 < f m ∧ f m < 1 → p ≤ m)

include hp0 hp1 hmin in
/-- The minimal positive integer with absolute value smaller than 1 is a prime number. -/
/-
**Rat.AbsoluteValue.is_prime_of_minimal_nat_zero_lt_and_lt_one** 是 Mathlib 中的一个引
理，位于命名空间 `Rat.AbsoluteValue`。
形式化陈述：is_prime_of_minimal_nat_zero_lt_and_lt_one : p.Prime
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.ge_of_not_lt`：∀ {n m : ℕ}, ¬n < m → n ≥ m
· 使用定理 `Mathlib.Tactic.IntervalCases.of_lt_right`：of_lt_right [LinearOrder α] (h
 : (a : α) < b) (eq : b = b') : ¬b' <= a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.prime_iff_not_exists_mul_eq`：prime_iff_not_exists_mul_eq {p : Nat} :
 p.Prime ↔ 2 <= p ∧ ¬ exists m n, m < p ∧ n < p ∧ m * n = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `map_pos_of_ne_zero`：∀ {F : Type u_2} {α : Type u_3} {β : Type u_4} [inst
 : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoid β]   [inst_3 : L
inearOrd…
· 使用定理 `MulRingNormClass.toAddGroupNormClass`：∀ {F : Type u_7} {α : outParam (Ty
pe u_8)} {β : outParam (Type u_9)} [inst : NonAssocRing α] [inst_1 : Semiring β]
   [inst_2 : PartialOrder …
· 使用定理 `AbsoluteValue.instMulRingNormClassOfNontrivialOfIsDomain`：∀ {R : Type u_
3} {S : Type u_4} [inst : CommRing S] [inst_1 : PartialOrder S] [IsOrderedRing S
] [inst_3 : Ring R]   [NoZeroDivisors S] [Nont…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用引理 `one_le_mul_of_one_le_of_one_le`：one_le_mul_of_one_le_of_one_le [ZeroLEOn
eClass M₀] [PosMulMono M₀] (ha : 1 <= a) (hb : 1 <= b) : (1 : M₀) <= a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
The minimal positive integer with absolute value smaller than 1 is a prime numbe
r.
-/
lemma is_prime_of_minimal_nat_zero_lt_and_lt_one : p.Prime := by
  have hp2 : 2 ≤ p := by
    by_contra! hp
    interval_cases p <;> grind
  rw [Nat.prime_iff_not_exists_mul_eq]
  refine ⟨hp2, ?_⟩
  rintro ⟨a, b, ha, hb, rfl⟩
  obtain ⟨ha₀, hb₀⟩ := mul_ne_zero_iff.mp (by omega : a * b ≠ 0)
  have h {n : ℕ} (hn₀ : n ≠ 0) (hn : n < a * b) : 1 ≤ f n := by
    by_contra! hn₁
    exact (not_le_of_gt hn) <| hmin n ⟨map_pos_of_ne_zero f (mod_cast hn₀), hn₁⟩
  rw [Nat.cast_mul, map_mul] at hp1
  exact not_le_of_gt hp1 <| one_le_mul_of_one_le_of_one_le (h ha₀ ha) (h hb₀ hb)

-- ## Step 3: if p does not divide m, then f m = 1

open Real

include hp0 hp1 hmin bdd in
/-- A natural number not divisible by `p` has absolute value 1. -/
/-
**Rat.AbsoluteValue.eq_one_of_not_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Rat.AbsoluteVal
ue`。
形式化陈述：eq_one_of_not_dvd {m : Nat} (hpm : ¬ p ∣ m) : f m = 1
参数：hpm : ¬ p ∣ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsCoprime.pow`：IsCoprime.pow (H : IsCoprime x y) : IsCoprime (x ^ m) (y 
^ n)
· 使用定理 `Nat.Coprime.isCoprime`：∀ {m n : ℕ}, m.Coprime n → IsCoprime ↑m ↑n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
· 使用引理 `Rat.AbsoluteValue.is_prime_of_minimal_nat_zero_lt_and_lt_one`：is_prime_o
f_minimal_nat_zero_lt_and_lt_one : p.Prime
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Real.rpow_lt_rpow_of_exponent_gt`：rpow_lt_rpow_of_exponent_gt (hx0 : 0 <
 x) (hx1 : x < 1) (hyz : z < y) : x ^ y < x ^ z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `lt_add_of_le_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
Preorder α] [AddLeftStrictMono α] {a b c : α},   b ≤ c → 0 < a → b < c + a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.le_ceil`：le_ceil (a : R) : a <= ⌈a⌉₊
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.rpow_le_rpow_of_exponent_ge`：rpow_le_rpow_of_exponent_ge (hx0 : 0 <
 x) (hx1 : x <= 1) (hyz : z <= y) : x ^ y <= x ^ z
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.log_inv`：log_inv (x : Real) : log x⁻¹ = -log x
（共 141 条，此处仅展示前 30 条）

--- 原说明 ---
A natural number not divisible by `p` has absolute value 1.
-/
lemma eq_one_of_not_dvd {m : ℕ} (hpm : ¬ p ∣ m) : f m = 1 := by
  apply le_antisymm (bdd m)
  by_contra! hm
  set M := f p ⊔ f m with hM
  set k := Nat.ceil (M.logb (1 / 2)) + 1 with hk
  obtain ⟨a, b, bezout⟩ : IsCoprime (p ^ k : ℤ) (m ^ k) :=
    is_prime_of_minimal_nat_zero_lt_and_lt_one hp0 hp1 hmin
      |>.coprime_iff_not_dvd |>.mpr hpm |>.isCoprime |>.pow
  have le_half {x} (hx0 : 0 < x) (hx1 : x < 1) (hxM : x ≤ M) : x ^ k < 1 / 2 := by
    calc
    x ^ k = x ^ (k : ℝ) := (rpow_natCast x k).symm
    _ < x ^ M.logb (1 / 2) := by
      apply rpow_lt_rpow_of_exponent_gt hx0 hx1
      rw [hk]
      push_cast
      exact lt_add_of_le_of_pos (Nat.le_ceil _) zero_lt_one
    _ ≤ x ^ x.logb (1 / 2) := by
      apply rpow_le_rpow_of_exponent_ge hx0 hx1.le
      simp only [one_div, ← log_div_log, log_inv, neg_div, ← div_neg, hM]
      gcongr
      simp only [Left.neg_pos_iff]
      exact log_neg (lt_sup_iff.mpr <| .inl hp0) (sup_lt_iff.mpr ⟨hp1, hm⟩)
    _ = 1 / 2 := rpow_logb hx0 hx1.ne one_half_pos
  apply lt_irrefl (1 : ℝ)
  calc
  1 = f 1 := (map_one f).symm
  _ = f (a * p ^ k + b * m ^ k) := by rw_mod_cast [bezout]; norm_cast
  _ ≤ f (a * p ^ k) + f (b * m ^ k) := f.add_le' ..
  _ ≤ 1 * (f p) ^ k + 1 * (f m) ^ k := by
    simp only [map_mul, map_pow]
    gcongr <;> simpa only [← apply_natAbs_eq] using bdd _
  _ < 1 := by
    have hm₀ : 0 < f m := f.pos <| Nat.cast_ne_zero.mpr fun H ↦ hpm <| H ▸ dvd_zero p
    linarith only [le_half hp0 hp1 le_sup_left, le_half hm₀ hm le_sup_right]

-- ## Step 4: f p = p ^ (-t) for some positive real t

include hp0 hp1 hmin in
/-- The absolute value of `p` is `p ^ (-t)` for some positive real number `t`. -/
/-
**Rat.AbsoluteValue.exists_pos_eq_pow_neg** 是 Mathlib 中的一个引理，位于命名空间 `Rat.Absolut
eValue`。
形式化陈述：exists_pos_eq_pow_neg : exists t : Real, 0 < t ∧ f p = p ^ (-t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用引理 `Rat.AbsoluteValue.is_prime_of_minimal_nat_zero_lt_and_lt_one`：is_prime_o
f_minimal_nat_zero_lt_and_lt_one : p.Prime
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Real.logb_neg`：logb_neg (h0 : 0 < x) (h1 : x < 1) : logb b x < 0
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Real.rpow_logb`：rpow_logb (hx : 0 < x) : b ^ logb b x = x
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b

--- 原说明 ---
The absolute value of `p` is `p ^ (-t)` for some positive real number `t`.
-/
lemma exists_pos_eq_pow_neg : ∃ t : ℝ, 0 < t ∧ f p = p ^ (-t) := by
  have hp : (1 : ℝ) < p :=
    mod_cast (is_prime_of_minimal_nat_zero_lt_and_lt_one hp0 hp1 hmin).one_lt
  exact ⟨-logb p (f p), neg_pos.mpr <| logb_neg hp hp0 hp1, by
    simpa using (rpow_logb (zero_lt_one.trans hp) hp.ne' hp0).symm⟩

-- ## Non-archimedean case: end goal

include hf_nontriv bdd in
/-- If `f` is bounded and not trivial, then it is equivalent to a p-adic absolute value. -/
/-
**Rat.AbsoluteValue.equiv_padic_of_bounded** 是 Mathlib 中的一个定理，位于命名空间 `Rat.Absolu
teValue`。
形式化陈述：equiv_padic_of_bounded : exists! p, exists (_ : Fact p.Prime), f.IsEquiv (
padic p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Rat.AbsoluteValue.exists_minimal_nat_zero_lt_and_lt_one`：exists_minimal_
nat_zero_lt_and_lt_one : exists p : Nat, (0 < f p ∧ f p < 1) ∧ forall m : Nat, 0
 < f m ∧ f m < 1 -> p <= m
· 使用引理 `Rat.AbsoluteValue.is_prime_of_minimal_nat_zero_lt_and_lt_one`：is_prime_o
f_minimal_nat_zero_lt_and_lt_one : p.Prime
· 使用引理 `Rat.AbsoluteValue.exists_pos_eq_pow_neg`：exists_pos_eq_pow_neg : exists 
t : Real, 0 < t ∧ f p = p ^ (-t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `AbsoluteValue.map_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring
 R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S),
 abv 0 = 0
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.exists_eq_pow_mul_and_not_dvd`：exists_eq_pow_mul_and_not_dvd {n : Na
t} (hn : n != 0) (p : Nat) (hp : p != 1) : exists e n' : Nat, ¬p ∣ n' ∧ n = p ^ 
e * n'
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `padicNorm.nat_eq_one_iff`：nat_eq_one_iff (m : Nat) : padicNorm p m = 1 ↔
 ¬p ∣ m
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is bounded and not trivial, then it is equivalent to a p-adic absolute va
lue.
-/
theorem equiv_padic_of_bounded :
    ∃! p, ∃ (_ : Fact p.Prime), f.IsEquiv (padic p) := by
  obtain ⟨p, ⟨hp0, hp1⟩, hmin⟩ := exists_minimal_nat_zero_lt_and_lt_one hf_nontriv bdd
  have hp := is_prime_of_minimal_nat_zero_lt_and_lt_one hp0 hp1 hmin
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht, hpt⟩ := exists_pos_eq_pow_neg hp0 hp1 hmin
  simp_rw [← exists_nat_rpow_iff_isEquiv]
  refine ⟨p, ⟨inferInstance, t⁻¹, inv_pos.mpr ht, fun n ↦ ?_⟩, fun q ⟨hq, heq⟩ ↦ ?_⟩
  · rcases eq_or_ne n 0 with rfl | hn
    · simp [ht.ne']
    · rcases Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one with ⟨_, m, hpm, rfl⟩
      have := (padicNorm.nat_eq_one_iff m).mpr hpm
      simp_all [← rpow_natCast, ← rpow_mul, mul_comm t, mul_inv_cancel_right₀ ht.ne',
        eq_one_of_not_dvd bdd hp0 hp1 hmin hpm]
  · by_contra! hpq
    apply hq.elim.ne_one
    rw [ne_comm, ← Nat.coprime_primes hp hq.elim, hp.coprime_iff_not_dvd] at hpq
    rcases heq with ⟨_, _, heq⟩
    simpa [eq_one_of_not_dvd bdd hp0 hp1 hmin hpq] using heq q

end Non_archimedean

section Archimedean

/-!
### Archimedean case

Every unbounded absolute value on `ℚ` is equivalent to the standard absolute value.
-/

/-- The standard absolute value on `ℚ`. We name it `real` because it corresponds to the
unique real place of `ℚ`. -/
/-
**Rat.AbsoluteValue.real** 是 Mathlib 中的一个定义，位于命名空间 `Rat.AbsoluteValue`。
形式化陈述：real : AbsoluteValue Rat Real where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The standard absolute value on `ℚ`. We name it `real` because it corresponds to 
the
unique real place of `ℚ`.
-/
def real : AbsoluteValue ℚ ℝ where
  toFun x := |x|
  map_mul' := by simp
  nonneg' := by simp
  eq_zero' := by simp
  add_le' := by simp [abs_add_le]
/-
**Rat.AbsoluteValue.real_eq_abs** 是 Mathlib 中的一个定理，位于命名空间 `Rat.AbsoluteValue`。
形式化陈述：∀ (r : ℚ), Rat.AbsoluteValue.real r = ↑|r|
参数：r : ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_abs`：∀ {K : Type u_5} [inst : Field K] [inst_1 : LinearOrder K]
 [IsStrictOrderedRing K] (q : ℚ), ↑|q| = |↑q|
-/
@[simp] lemma real_eq_abs (r : ℚ) : real r = |r| := (cast_abs r).symm

-- ## Preliminary result

/-- Given any two integers `n`, `m` with `m > 1`, the absolute value of `n` is bounded by
`m + m * f m + m * (f m) ^ 2 + ... + m * (f m) ^ d` where `d` is the number of digits of the
expansion of `n` in base `m`. -/
/-
**Rat.AbsoluteValue.apply_le_sum_digits** 是 Mathlib 中的一个引理，位于命名空间 `Rat.AbsoluteV
alue`。
形式化陈述：apply_le_sum_digits (n : Nat) {m : Nat} (hm : 1 < m) : f n <= ((Nat.digits
 m n).mapIdx fun i _ => m * (f m) ^ i).sum
参数：n : Nat；hm : 1 < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `AbsoluteValue.apply_nat_le_self`：apply_nat_le_self [IsOrderedRing S] (n 
: Nat) : abv n <= n
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.digits_lt_base`：digits_lt_base {b m d : Nat} (hb : 1 < b) (hd : d in
 digits b m) : d < b
· 使用定理 `Nat.ofDigits_digits`：ofDigits_digits (b n : Nat) : ofDigits b (digits b 
n) = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.ofDigits_eq_sum_mapIdx`：ofDigits_eq_sum_mapIdx (b : Nat) (L : List N
at) : ofDigits b L = (L.mapIdx fun i a => a * b ^ i).sum
· 使用引理 `Nat.cast_list_sum`：cast_list_sum [AddMonoidWithOne R] (s : List Nat) : (
↑s.sum : R) = (s.map (↑)).sum
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AbsoluteValue.listSum_le`：listSum_le [AddLeftMono S] (l : List R) : abv 
l.sum <= (l.map abv).sum
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.mapIdx_eq_zipIdx_map`：∀ {α : Type u_1} {β : Type u_2} {l : List α} 
{f : ℕ → α → β},   List.mapIdx f l =     List.map       (fun x =>         match 
x with         …
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.sum_le_sum`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddMonoid M] [i
nst_1 : Preorder M] [AddRightMono M] [AddLeftMono M] {l : List ι}   {f g : ι → M
}, (∀…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `List.mem_zipIdx`：∀ {α : Type u_1} {x : α} {i : ℕ} {xs : List α} {k : ℕ} 
(h : (x, i) ∈ xs.zipIdx k),   k ≤ i ∧ i < k + xs.length ∧ x = xs[i - k]
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `AbsoluteValue.map_mul`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (
x y : R), a…
· 使用定理 `AbsoluteValue.map_pow`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) [
IsDomain S]…
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
Given any two integers `n`, `m` with `m > 1`, the absolute value of `n` is bound
ed by
`m + m * f m + m * (f m) ^ 2 + ... + m * (f m) ^ d` where `d` is the number of d
igits of the
expansion of `n` in base `m`.
-/
lemma apply_le_sum_digits (n : ℕ) {m : ℕ} (hm : 1 < m) :
    f n ≤ ((Nat.digits m n).mapIdx fun i _ ↦ m * (f m) ^ i).sum := by
  set L := Nat.digits m n
  set L' : List ℚ := List.map Nat.cast (L.mapIdx fun i a ↦ a * m ^ i)
  -- If `c` is a digit in the expansion of `n` in base `m`, then `f c` is less than `m`.
  have hcoef {c : ℕ} (hc : c ∈ Nat.digits m n) : f c < m :=
    lt_of_le_of_lt (f.apply_nat_le_self c) (mod_cast Nat.digits_lt_base hm hc)
  calc
  f n = f ((Nat.ofDigits m L : ℕ) : ℚ) := by rw [Nat.ofDigits_digits m n]
    _ = f L'.sum := by simp [L', Nat.ofDigits_eq_sum_mapIdx]
    _ ≤ (L'.map f).sum := listSum_le f L'
    _ ≤ (L.mapIdx fun i _ ↦ m * (f m) ^ i).sum := ?_
  simp only [List.mapIdx_eq_zipIdx_map, List.map_map, L']
  refine List.sum_le_sum fun ⟨a, i⟩ hia ↦ ?_
  replace hia := List.mem_zipIdx hia
  simp only [Function.comp_apply, Nat.cast_mul, Nat.cast_pow, AbsoluteValue.map_mul,
    AbsoluteValue.map_pow]
  refine mul_le_mul_of_nonneg_right ?_ <| pow_nonneg (f.nonneg _) i
  simp only [zero_le, zero_add, true_and] at hia
  exact (hcoef (List.mem_iff_get.mpr ⟨⟨i, hia.1⟩, hia.2.symm⟩)).le

-- ## Step 1: if f is an AbsoluteValue and f n > 1 for some natural n, then f n > 1 for all n ≥ 2

/-- If `f n > 1` for some `n` then `f n > 1` for all `n ≥ 2` -/
/-
**Rat.AbsoluteValue.one_lt_of_not_bounded** 是 Mathlib 中的一个引理，位于命名空间 `Rat.Absolut
eValue`。
形式化陈述：one_lt_of_not_bounded (notbdd : ¬ forall n : Nat, f n <= 1) {n₀ : Nat} (hn
₀ : 1 < n₀) : 1 < f n₀
参数：notbdd : ¬ forall n : Nat, f n <= 1；hn₀ : 1 < n₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Rat.AbsoluteValue.apply_le_sum_digits`：apply_le_sum_digits (n : Nat) {m 
: Nat} (hm : 1 < m) : f n <= ((Nat.digits m n).mapIdx fun i _ => m * (f m) ^ i).
sum
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mapIdx_eq_zipIdx_map`：∀ {α : Type u_1} {β : Type u_2} {l : List α} 
{f : ℕ → α → β},   List.mapIdx f l =     List.map       (fun x =>         match 
x with         …
· 使用定理 `List.sum_le_sum`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddMonoid M] [i
nst_1 : Preorder M] [AddRightMono M] [AddLeftMono M] {l : List ι}   {f g : ι → M
}, (∀…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_le_of_le_one_right`：mul_le_of_le_one_right [PosMulMono α] (ha : 0 <=
 a) (h : b <= 1) : a * b <= a
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `pow_le_one₀`：pow_le_one₀ [PosMulMono M₀] {n : Nat} (ha₀ : 0 <= a) (ha₁ :
 a <= 1) : a ^ n <= 1
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `List.eq_replicate_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, (∀ b ∈ 
l, b = a) → l = List.replicate l.length a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_const'`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {b : β}, L
ist.map (fun x => b) l = List.replicate l.length b
· 使用定理 `List.length_zipIdx`：∀ {α : Type u_1} {l : List α} {i : ℕ}, (l.zipIdx i).
length = l.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 91 条，此处仅展示前 30 条）

--- 原说明 ---
If `f n > 1` for some `n` then `f n > 1` for all `n ≥ 2`
-/
lemma one_lt_of_not_bounded (notbdd : ¬ ∀ n : ℕ, f n ≤ 1) {n₀ : ℕ} (hn₀ : 1 < n₀) : 1 < f n₀ := by
  contrapose! notbdd with h
  intro n
  have h_ineq1 {m : ℕ} (hm : 1 ≤ m) : f m ≤ n₀ * (logb n₀ m + 1) := by
    /- L is the string of digits of `n` in the base `n₀` -/
    set L := Nat.digits n₀ m
    calc
    f m ≤ (L.mapIdx fun i _ ↦ n₀ * f n₀ ^ i).sum := apply_le_sum_digits m hn₀
    _ ≤ (L.mapIdx fun _ _ ↦ (n₀ : ℝ)).sum := by
      simp only [List.mapIdx_eq_zipIdx_map]
      refine List.sum_le_sum fun ⟨i, a⟩ _ ↦ ?_
      exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by positivity) h)
    _ = n₀ * (Nat.log n₀ m + 1) := by
      rw [List.mapIdx_eq_zipIdx_map, List.eq_replicate_of_mem (a := (n₀ : ℝ)) (l := L.zipIdx.map _),
        List.sum_replicate, List.length_map, List.length_zipIdx, nsmul_eq_mul, mul_comm,
        Nat.length_digits n₀ m hn₀ (ne_zero_of_lt hm), Nat.cast_add_one]
      simp +contextual
    _ ≤ n₀ * (logb n₀ m + 1) := by
      gcongr
      exact natLog_le_logb ..
  -- For h_ineq2 we need to exclude the case n = 0.
  rcases eq_or_ne n 0 with rfl | h₀
  · simp
  have h_ineq2 (k : ℕ) (hk : 0 < k) :
      f n ≤ (n₀ * (logb n₀ n + 1)) ^ (k : ℝ)⁻¹ * k ^ (k : ℝ)⁻¹ := by
    have : 0 ≤ logb n₀ n := logb_nonneg (mod_cast hn₀) (mod_cast one_le_iff_ne_zero.mpr h₀)
    calc
    f n = (f ↑(n ^ k)) ^ (k : ℝ)⁻¹ := by
      rw [Nat.cast_pow, map_pow, ← rpow_natCast, rpow_rpow_inv (by positivity) (by positivity)]
    _ ≤ (n₀ * (logb n₀ ↑(n ^ k) + 1)) ^ (k : ℝ)⁻¹ := by
      gcongr
      exact h_ineq1 <| one_le_pow₀ (one_le_iff_ne_zero.mpr h₀)
    _ = (n₀ * (k * logb n₀ n + 1)) ^ (k : ℝ)⁻¹ := by
      rw [Nat.cast_pow, logb_pow]
    _ ≤ (n₀ * (k * logb n₀ n + k)) ^ (k : ℝ)⁻¹ := by
      gcongr
      exact one_le_cast.mpr hk
    _ = (n₀ * (logb n₀ n + 1)) ^ (k : ℝ)⁻¹ * k ^ (k : ℝ)⁻¹ := by
      rw [← mul_rpow (by positivity) (by positivity), mul_assoc, add_mul, one_mul,
        mul_comm _ (k : ℝ)]
-- For 0 < logb n₀ n below we also need to exclude n = 1.
  rcases eq_or_ne n 1 with rfl | h₁
  · simp
  refine le_of_tendsto_of_tendsto tendsto_const_nhds ?_ (eventually_atTop.mpr ⟨1, h_ineq2⟩)
  have : 0 < logb n₀ n := logb_pos (mod_cast hn₀) (by norm_cast; lia)
  simpa using (tendsto_const_rpow_inv (by positivity)).mul tendsto_nat_rpow_inv

-- ## Step 2: given m, n ≥ 2 and |m| = m^s, |n| = n^t for s, t > 0, we have t ≤ s

variable {m n : ℕ} (hm : 1 < m) (hn : 1 < n) (notbdd : ¬ ∀ n : ℕ, f n ≤ 1)

include hm notbdd in
/-
**Rat.AbsoluteValue.expr_pos** 是 Mathlib 中的一个引理，位于命名空间 `Rat.AbsoluteValue`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma expr_pos : 0 < m * f m / (f m - 1) := by
  apply div_pos (mul_pos (mod_cast hm.pos) (map_pos_of_ne_zero f (mod_cast hm.ne_zero)))
  linarith only [one_lt_of_not_bounded notbdd hm]

include hn hm notbdd in
/-
**Rat.AbsoluteValue.param_upperbound** 是 Mathlib 中的一个引理，位于命名空间 `Rat.AbsoluteValu
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma param_upperbound {k : ℕ} (hk : k ≠ 0) :
    f n ≤ (m * f m / (f m - 1)) ^ (k : ℝ)⁻¹ * f m ^ logb m n := by
  have h_ineq1 {m n : ℕ} (hm : 1 < m) (hn : 1 < n) :
      f n ≤ (m * f m / (f m - 1)) * f m ^ logb m n := by
    let d := Nat.log m n
    have hfm := one_lt_of_not_bounded notbdd hm
    calc
    f n ≤ ((Nat.digits m n).mapIdx fun i _ ↦ m * f m ^ i).sum := apply_le_sum_digits n hm
    _ = m * ((Nat.digits m n).mapIdx fun i _ ↦ f m ^ i).sum := list_mul_sum (m.digits n) (f m) m
    _ = m * ((f m ^ (d + 1) - 1) / (f m - 1)) := by
      rw [list_geom _ hfm.ne', ← Nat.length_digits m n hm (ne_zero_of_lt hn)]
    _ ≤ m * ((f m ^ (d + 1)) / (f m - 1)) := by
      gcongr; linarith
    _ = ↑m * f ↑m / (f ↑m - 1) * f ↑m ^ d := by ring
    _ ≤ ↑m * f ↑m / (f ↑m - 1) * f ↑m ^ logb ↑m ↑n := by
      gcongr
      rw [← rpow_natCast, rpow_le_rpow_left_iff hfm]
      exact natLog_le_logb n m
  have he := expr_pos hm notbdd
  apply le_of_pow_le_pow_left₀ hk (by positivity)
  nth_rewrite 2 [← rpow_natCast]
  rw [mul_rpow (by positivity) (by positivity), ← rpow_mul he.le, ← rpow_mul (apply_nonneg f ↑m),
    inv_mul_cancel₀ (mod_cast hk), rpow_one, mul_comm (logb ..)]
  calc
    (f n) ^ k = f ↑(n ^ k) := by simp
    _ ≤ (m * f m / (f m - 1)) * f m ^ logb m ↑(n ^ k) := h_ineq1 hm (Nat.one_lt_pow hk hn)
    _ = (m * f m / (f m - 1)) * f m ^ (k * logb m n) := by rw [Nat.cast_pow, logb_pow]

include hm hn notbdd in
/-- Given two natural numbers `n, m` greater than 1 we have `f n ≤ f m ^ logb m n`. -/
/-
**Rat.AbsoluteValue.le_pow_log** 是 Mathlib 中的一个引理，位于命名空间 `Rat.AbsoluteValue`。
形式化陈述：le_pow_log : f n <= f m ^ logb m n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Filter.Tendsto.mul_const`：Filter.Tendsto.mul_const {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (f · * b) 
x (𝓝 (a * b))
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `_private.Mathlib.NumberTheory.Ostrowski.0.tendsto_const_rpow_inv`：∀ {C :
 ℝ}, 0 < C → Filter.Tendsto (fun k => C ^ (↑k)⁻¹) Filter.atTop (nhds 1)
· 使用定理 `_private.Mathlib.NumberTheory.Ostrowski.0.Rat.AbsoluteValue.expr_pos`：∀ 
{f : AbsoluteValue ℚ ℝ} {m : ℕ}, 1 < m → (¬∀ (n : ℕ), f ↑n ≤ 1) → 0 < ↑m * f ↑m 
/ (f ↑m - 1)
· 使用定理 `le_of_tendsto_of_tendsto`：le_of_tendsto_of_tendsto {f g : β -> α} {b : F
ilter β} {a₁ a₂ : α} [hb : NeBot b] (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b 
(𝓝 a₂)) (h : f…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `_private.Mathlib.NumberTheory.Ostrowski.0.Rat.AbsoluteValue.param_upperb
ound`：∀ {f : AbsoluteValue ℚ ℝ} {m n : ℕ},   1 < m →     1 < n →       (¬∀ (n : 
ℕ), f ↑n ≤ 1) → ∀ {k : ℕ}, k ≠ 0 → f ↑n ≤ (↑m * f ↑m / (f ↑m - 1))…
· 使用定理 `ne_zero_of_lt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α

--- 原说明 ---
Given two natural numbers `n, m` greater than 1 we have `f n ≤ f m ^ logb m n`.
-/
lemma le_pow_log : f n ≤ f m ^ logb m n := by
  have : Tendsto (fun k : ℕ ↦ (m * f m / (f m - 1)) ^ (k : ℝ)⁻¹ * f m ^ logb m n)
      atTop (𝓝 (f m ^ logb m n)) := by
    nth_rw 2 [← one_mul (f ↑m ^ logb ↑m ↑n)]
    exact (tendsto_const_rpow_inv (expr_pos hm notbdd)).mul_const _
  exact le_of_tendsto_of_tendsto (tendsto_const_nhds (x := f ↑n)) this <|
    eventually_atTop.mpr ⟨2, fun b hb ↦ param_upperbound hm hn notbdd (ne_zero_of_lt hb)⟩

include hm hn notbdd in
/-- Given `m, n ≥ 2` and `f m = m ^ s`, `f n = n ^ t` for `s, t > 0`, we have `t ≤ s`. -/
/-
**Rat.AbsoluteValue.le_of_eq_pow** 是 Mathlib 中的一个引理，位于命名空间 `Rat.AbsoluteValue`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `m, n ≥ 2` and `f m = m ^ s`, `f n = n ^ t` for `s, t > 0`, we have `t ≤ s
`.
-/
private lemma le_of_eq_pow {s t : ℝ} (hfm : f m = m ^ s) (hfn : f n = n ^ t) : t ≤ s := by
  rw [← rpow_le_rpow_left_iff (x := n) (mod_cast hn), ← hfn]
  apply le_trans <| le_pow_log hm hn notbdd
  rw [hfm, ← rpow_mul (Nat.cast_nonneg m), mul_comm, rpow_mul (Nat.cast_nonneg m),
    rpow_logb (mod_cast zero_lt_of_lt hm) (mod_cast hm.ne') (mod_cast zero_lt_of_lt hn)]

include hm hn notbdd in
/-
**Rat.AbsoluteValue.eq_of_eq_pow** 是 Mathlib 中的一个引理，位于命名空间 `Rat.AbsoluteValue`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma eq_of_eq_pow {s t : ℝ} (hfm : f m = m ^ s) (hfn : f n = n ^ t) : s = t :=
  le_antisymm (le_of_eq_pow hn hm notbdd hfn hfm) (le_of_eq_pow hm hn notbdd hfm hfn)

-- ## Archimedean case: end goal

include notbdd in
/-- If `f` is not bounded and not trivial, then it is equivalent to the standard absolute value on
`ℚ`. -/
/-
**Rat.AbsoluteValue.equiv_real_of_unbounded** 是 Mathlib 中的一个定理，位于命名空间 `Rat.Absol
uteValue`。
形式化陈述：equiv_real_of_unbounded : f.IsEquiv real
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.exists_not_of_not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀
 (x : α), p x) → ∃ x, ¬p x
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.le_one_iff_eq_zero_or_eq_one`：∀ {n : ℕ}, n ≤ 1 ↔ n = 0 ∨ n = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `AbsoluteValue.map_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring
 R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S),
 abv 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `AbsoluteValue.map_one`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) [
IsDomain S]…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用引理 `Rat.AbsoluteValue.exists_nat_rpow_iff_isEquiv`：exists_nat_rpow_iff_isEqu
iv : (exists c : Real, 0 < c ∧ forall n : Nat, f n ^ c = g n) ↔ f.IsEquiv g
· 使用定理 `Real.logb_pos`：logb_pos (hx : 1 < x) : 0 < logb b x
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is not bounded and not trivial, then it is equivalent to the standard abs
olute value on
`ℚ`.
-/
theorem equiv_real_of_unbounded : f.IsEquiv real := by
  obtain ⟨m, hm⟩ := Classical.exists_not_of_not_forall notbdd
  have hfm1 : 1 < f m := lt_of_not_ge hm
  have oneltm : 1 < m := by
    contrapose! hm
    rcases le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl <;> simp
  rw [← exists_nat_rpow_iff_isEquiv]
  set s := logb m (f m) with hs
  have hs0 : 0 < s := hs ▸ logb_pos (mod_cast oneltm) hfm1
  refine ⟨s⁻¹, inv_pos.mpr hs0, fun n ↦ ?_⟩
  rcases lt_trichotomy n 1 with h | rfl | h
  · obtain rfl : n = 0 := by lia
    simp [hs0.ne']
  · simp
  · simp only [real_eq_abs, abs_cast, Rat.cast_natCast]
    rw [rpow_inv_eq (by positivity) (by positivity) hs0.ne']
    have hfm : f m = m ^ s := by
      rw [rpow_logb (by positivity) (by norm_cast; omega) (zero_lt_one.trans hfm1)]
    have hfn : f n = n ^ logb n (f n) := by
      rw [rpow_logb (by positivity) (by norm_cast; omega)
        (map_pos_of_ne_zero f (by exact_mod_cast ne_zero_of_lt h))]
    rw [hfn, ← eq_of_eq_pow oneltm h notbdd hfm hfn]

end Archimedean

/-!
### The main result
-/

/-- **Ostrowski's Theorem**: every absolute value (with values in `ℝ`) on `ℚ` is equivalent
to either the standard absolute value or a `p`-adic absolute value for a prime `p`. -/
/-
**Rat.AbsoluteValue.equiv_real_or_padic** 是 Mathlib 中的一个定理，位于命名空间 `Rat.AbsoluteV
alue`。
形式化陈述：equiv_real_or_padic (f : AbsoluteValue Rat Real) (hf_nontriv : f.IsNontriv
ial) : f ≈ real ∨ exists! p, exists (_ : Fact p.Prime), f ≈ (padic p)
参数：f : AbsoluteValue Rat Real；hf_nontriv : f.IsNontrivial。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.AbsoluteValue.equiv_padic_of_bounded`：equiv_padic_of_bounded : exist
s! p, exists (_ : Fact p.Prime), f.IsEquiv (padic p)
· 使用定理 `Rat.AbsoluteValue.equiv_real_of_unbounded`：equiv_real_of_unbounded : f.I
sEquiv real

--- 原说明 ---
**Ostrowski's Theorem**: every absolute value (with values in `ℝ`) on `ℚ` is equ
ivalent
to either the standard absolute value or a `p`-adic absolute value for a prime `
p`.
-/
theorem equiv_real_or_padic (f : AbsoluteValue ℚ ℝ) (hf_nontriv : f.IsNontrivial) :
    f ≈ real ∨ ∃! p, ∃ (_ : Fact p.Prime), f ≈ (padic p) := by
  by_cases bdd : ∀ n : ℕ, f n ≤ 1
  · exact .inr <| equiv_padic_of_bounded hf_nontriv bdd
  · exact .inl <| equiv_real_of_unbounded bdd

/-- The standard absolute value on `ℚ` is not equivalent to any `p`-adic absolute value. -/
/-
**Rat.AbsoluteValue.not_real_isEquiv_padic** 是 Mathlib 中的一个引理，位于命名空间 `Rat.Absolu
teValue`。
形式化陈述：not_real_isEquiv_padic (p : Nat) [Fact p.Prime] : ¬ real.IsEquiv (padic p)
参数：p : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AbsoluteValue.isEquiv_iff_exists_rpow_eq`：isEquiv_iff_exists_rpow_eq {v 
w : AbsoluteValue F Real} : v.IsEquiv w ↔ exists c : Real, 0 < c ∧ (v · ^ c) = w
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `Rat.AbsoluteValue.padic_le_one`：padic_le_one (p : Nat) [Fact p.Prime] (n
 : Int) : padic p n <= 1
· 使用定理 `Real.one_lt_rpow`：one_lt_rpow {x z : Real} (hx : 1 < x) (hz : 0 < z) : 1
 < x ^ z
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Rat.AbsoluteValue.real_eq_abs`：∀ (r : ℚ), Rat.AbsoluteValue.real r = ↑|r
|
· 使用定理 `Nat.abs_ofNat`：abs_ofNat (n : Nat) [n.AtLeastTwo] : |(ofNat(n) : R)| = o
fNat(n)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Rat.cast_ofNat`：∀ {α : Type u_3} [inst : DivisionRing α] (n : ℕ) [inst_1
 : n.AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The standard absolute value on `ℚ` is not equivalent to any `p`-adic absolute va
lue.
-/
lemma not_real_isEquiv_padic (p : ℕ) [Fact p.Prime] : ¬ real.IsEquiv (padic p) := by
  rw [isEquiv_iff_exists_rpow_eq]
  rintro ⟨c, hc₀, hc⟩
  apply_fun (· 2) at hc
  simp only [real_eq_abs, abs_ofNat, cast_ofNat] at hc
  exact ((padic_le_one p 2).trans_lt <| one_lt_rpow one_lt_two hc₀).ne' hc

end Rat.AbsoluteValue

