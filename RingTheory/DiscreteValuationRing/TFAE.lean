/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.KrullDimension.Zero

/-!

# Equivalent conditions for DVR

In `IsDiscreteValuationRing.TFAE`, we show that the following are equivalent for a
Noetherian local domain that is not a field `(R, m, k)`:
- `R` is a discrete valuation ring
- `R` is a valuation ring
- `R` is a Dedekind domain
- `R` is integrally closed with a unique prime ideal
- `m` is principal
- `dimₖ m/m² = 1`
- Every nonzero ideal is a power of `m`.

Also see `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain` for a version without `¬ IsField R`.
-/

public section


variable (R : Type*) [CommRing R]

open scoped Multiplicative

open IsLocalRing Module

/-
**exists_maximalIdeal_pow_eq_of_principal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_maximalIdeal_pow_eq_of_principal [IsNoetherianRing R] [IsLocalRing 
R] [IsDomain R] (h' : (maximalIdeal R).IsPrincipal) (I : Ideal R) (hI : I != ⊥) 
: exists n : Nat, I = maximalIdeal R ^ n
参数：h' : (maximalIdeal R).IsPrincipal；I : Ideal R；hI : I != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `IsSimpleModule.toIsSimpleOrder`：∀ {R : Type u_2} {inst : Ring R} {M : Ty
pe u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : IsSimpl
eModule R M], IsSimp…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `Ring.ne_bot_of_isMaximal_of_not_isField`：ne_bot_of_isMaximal_of_not_isFi
eld [Nontrivial R] {M : Ideal R} (max : M.IsMaximal) (not_field : ¬IsField R) : 
M != ⊥
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.span_zero_singleton`：span_zero_singleton : R ∙ (0 : M) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal`：irreducible
_of_span_eq_maximalIdeal {R : Type*} [CommSemiring R] [IsLocalRing R] [IsDomain 
R] (ϖ : R) (hϖ : ϖ != 0) (h : maximalIdeal R = Id…
· 使用定理 `WfDvdMonoid.not_isUnit_iff_exists_factors_eq`：not_isUnit_iff_exists_fact
ors_eq (a : α) (hn0 : a != 0) : ¬IsUnit a ↔ exists f : Multiset α, (forall b in 
f, Irreducible b) ∧ f.prod = a ∧ f…
· 使用定理 `IsNoetherianRing.wfDvdMonoid`：∀ {R : Type u_1} [inst : CommSemiring R] [
IsDomain R] [h : IsNoetherianRing R], WfDvdMonoid R
· 使用定理 `Irreducible.associated_of_dvd`：Irreducible.associated_of_dvd [Monoid M] 
{p q : M} (p_irr : Irreducible p) (q_irr : Irreducible q) (dvd : p ∣ q) : Associ
ated p q
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
（共 62 条，此处仅展示前 30 条）
-/
theorem exists_maximalIdeal_pow_eq_of_principal [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (h' : (maximalIdeal R).IsPrincipal) (I : Ideal R) (hI : I ≠ ⊥) :
    ∃ n : ℕ, I = maximalIdeal R ^ n := by
  by_cases h : IsField R
  · let _ := h.toField
    exact ⟨0, by simp [(eq_bot_or_eq_top I).resolve_left hI]⟩
  classical
  obtain ⟨x, hx : _ = Ideal.span _⟩ := h'
  by_cases hI' : I = ⊤
  · use 0; rw [pow_zero, hI', Ideal.one_eq_top]
  have H : ∀ r : R, ¬IsUnit r ↔ x ∣ r := fun r =>
    (SetLike.ext_iff.mp hx r).trans Ideal.mem_span_singleton
  have : x ≠ 0 := by
    rintro rfl
    apply Ring.ne_bot_of_isMaximal_of_not_isField (maximalIdeal.isMaximal R) h
    simp [hx]
  have hx' := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal x this hx
  have H' : ∀ r : R, r ≠ 0 → r ∈ nonunits R → ∃ n : ℕ, Associated (x ^ n) r := by
    intro r hr₁ hr₂
    obtain ⟨f, hf₁, rfl, hf₂⟩ := (WfDvdMonoid.not_isUnit_iff_exists_factors_eq r hr₁).mp hr₂
    have : ∀ b ∈ f, Associated x b := by
      intro b hb
      exact Irreducible.associated_of_dvd hx' (hf₁ b hb) ((H b).mp (hf₁ b hb).1)
    clear hr₁ hr₂ hf₁
    induction f using Multiset.induction with
    | empty => exact (hf₂ rfl).elim
    | cons fa fs fh => ?_
    rcases eq_or_ne fs ∅ with (rfl | hf')
    · use 1
      rw [pow_one, Multiset.prod_cons, Multiset.empty_eq_zero, Multiset.prod_zero, mul_one]
      exact this _ (Multiset.mem_cons_self _ _)
    · obtain ⟨n, hn⟩ := fh hf' fun b hb => this _ (Multiset.mem_cons_of_mem hb)
      use n + 1
      rw [pow_add, Multiset.prod_cons, mul_comm, pow_one]
      exact Associated.mul_mul (this _ (Multiset.mem_cons_self _ _)) hn
  have : ∃ n : ℕ, x ^ n ∈ I := by
    obtain ⟨r, hr₁, hr₂⟩ : ∃ r : R, r ∈ I ∧ r ≠ 0 := by
      by_contra! h; apply hI; rw [eq_bot_iff]; exact h
    obtain ⟨n, u, rfl⟩ := H' r hr₂ (le_maximalIdeal hI' hr₁)
    use n
    rwa [← I.unit_mul_mem_iff_mem u.isUnit, mul_comm]
  use Nat.find this
  apply le_antisymm
  · change ∀ s ∈ I, s ∈ _
    by_contra! ⟨s, hs₁, hs₂⟩
    apply hs₂
    by_cases hs₃ : s = 0; · rw [hs₃]; exact zero_mem _
    obtain ⟨n, u, rfl⟩ := H' s hs₃ (le_maximalIdeal hI' hs₁)
    rw [mul_comm, Ideal.unit_mul_mem_iff_mem _ u.isUnit] at hs₁ ⊢
    apply Ideal.pow_le_pow_right (Nat.find_min' this hs₁)
    apply Ideal.pow_mem_pow
    exact (H _).mpr (dvd_refl _)
  · rw [hx, Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
    exact Nat.find_spec this
/-
**maximalIdeal_isPrincipal_of_isDedekindDomain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：maximalIdeal_isPrincipal_of_isDedekindDomain [IsLocalRing R] [IsDedekindDo
main R] : (maximalIdeal R).IsPrincipal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Ideal.radical_eq_sInf`：radical_eq_sInf (I : Ideal R) : radical I = sInf 
{ J : Ideal R | I <= J ∧ IsPrime J }
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `IsLocalRing.eq_maximalIdeal`：eq_maximalIdeal {I : Ideal R} (hI : I.IsMax
imal) : I = maximalIdeal R
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `IsDedekindRing.toDimensionLEOne`：∀ {A : Type u_2} {inst : CommRing A} [s
elf : IsDedekindRing A], Ring.DimensionLEOne A
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_singleton_eq_bot`：span_singleton_eq_bot {x} : span ({x} : Set
 α) = ⊥ ↔ x = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.exists_radical_pow_le_of_fg`：exists_radical_pow_le_of_fg {R : Type
*} [CommSemiring R] (I : Ideal R) (h : I.radical.FG) : exists n : Nat, I.radical
 ^ n <= I
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
· 使用定理 `IsDedekindRing.toIsNoetherian`：∀ {A : Type u_2} {inst : CommRing A} [sel
f : IsDedekindRing A], IsNoetherian A A
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 80 条，此处仅展示前 30 条）
-/
theorem maximalIdeal_isPrincipal_of_isDedekindDomain [IsLocalRing R] [IsDedekindDomain R] :
    (maximalIdeal R).IsPrincipal := by
  classical
  by_cases ne_bot : maximalIdeal R = ⊥
  · rw [ne_bot]; infer_instance
  obtain ⟨a, ha₁, ha₂⟩ : ∃ a ∈ maximalIdeal R, a ≠ (0 : R) := by
    by_contra! h'; apply ne_bot; rwa [eq_bot_iff]
  have hle : Ideal.span {a} ≤ maximalIdeal R := by rwa [Ideal.span_le, Set.singleton_subset_iff]
  have : (Ideal.span {a}).radical = maximalIdeal R := by
    rw [Ideal.radical_eq_sInf]
    apply le_antisymm
    · exact sInf_le ⟨hle, inferInstance⟩
    · refine
        le_sInf fun I hI =>
          (eq_maximalIdeal <| hI.2.isMaximal (fun e => ha₂ ?_)).ge
      rw [← Ideal.span_singleton_eq_bot, eq_bot_iff, ← e]; exact hI.1
  have : ∃ n, maximalIdeal R ^ n ≤ Ideal.span {a} := by
    rw [← this]; apply Ideal.exists_radical_pow_le_of_fg; exact IsNoetherian.noetherian _
  rcases hn : Nat.find this with - | n
  · have := Nat.find_spec this
    rw [hn, pow_zero, Ideal.one_eq_top] at this
    exact (Ideal.IsMaximal.ne_top inferInstance (eq_top_iff.mpr <| this.trans hle)).elim
  obtain ⟨b, hb₁, hb₂⟩ : ∃ b ∈ maximalIdeal R ^ n, b ∉ Ideal.span {a} := by
    by_contra! h'; rw [Nat.find_eq_iff] at hn; exact hn.2 n n.lt_succ_self fun x hx => h' x hx
  have hb₃ : ∀ m ∈ maximalIdeal R, ∃ k : R, k * a = b * m := by
    intro m hm; rw [← Ideal.mem_span_singleton']; apply Nat.find_spec this
    rw [hn, pow_succ]; exact Ideal.mul_mem_mul hb₁ hm
  have hb₄ : b ≠ 0 := by rintro rfl; apply hb₂; exact zero_mem _
  let K := FractionRing R
  let x : K := algebraMap R K b / algebraMap R K a
  let M := Submodule.map (Algebra.linearMap R K) (maximalIdeal R)
  have ha₃ : algebraMap R K a ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr ha₂
  by_cases hx : ∀ y ∈ M, x * y ∈ M
  · have := isIntegral_of_smul_mem_submodule M ?_ ?_ x hx
    · obtain ⟨y, e⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral this
      refine (hb₂ (Ideal.mem_span_singleton'.mpr ⟨y, ?_⟩)).elim
      apply IsFractionRing.injective R K
      rw [map_mul, e, div_mul_cancel₀ _ ha₃]
    · rw [Submodule.ne_bot_iff]; refine ⟨_, ⟨a, ha₁, rfl⟩, ?_⟩
      exact (IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr ha₂
    · apply Submodule.FG.map; exact IsNoetherian.noetherian _
  · have :
        (M.map (DistribSMul.toLinearMap R K x)).comap (Algebra.linearMap R K) = ⊤ := by
      contrapose! hx with h
      rintro m' ⟨m, hm, rfl : algebraMap R K m = m'⟩
      obtain ⟨k, hk⟩ := hb₃ m hm
      have hk' : x * algebraMap R K m = algebraMap R K k := by
        rw [← mul_div_right_comm, ← map_mul, ← hk, map_mul, mul_div_cancel_right₀ _ ha₃]
      exact ⟨k, le_maximalIdeal h ⟨_, ⟨_, hm, rfl⟩, hk'⟩, hk'.symm⟩
    obtain ⟨y, hy₁, hy₂⟩ : ∃ y ∈ maximalIdeal R, b * y = a := by
      rw [Ideal.eq_top_iff_one, Submodule.mem_comap] at this
      obtain ⟨_, ⟨y, hy, rfl⟩, hy' : x * algebraMap R K y = algebraMap R K 1⟩ := this
      rw [map_one, ← mul_div_right_comm, div_eq_one_iff_eq ha₃, ← map_mul] at hy'
      exact ⟨y, hy, IsFractionRing.injective R K hy'⟩
    refine ⟨⟨y, ?_⟩⟩
    apply le_antisymm
    · intro m hm; obtain ⟨k, hk⟩ := hb₃ m hm; rw [← hy₂, mul_comm, mul_assoc] at hk
      rw [← mul_left_cancel₀ hb₄ hk, mul_comm]; exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
    · rwa [Submodule.span_le, Set.singleton_subset_iff]

/--
Let `(R, m, k)` be a Noetherian local domain (possibly a field).
The following are equivalent:
0. `R` is a PID
1. `R` is a valuation ring
2. `R` is a Dedekind domain
3. `R` is integrally closed with at most one non-zero prime ideal
4. `m` is principal
5. `dimₖ m/m² ≤ 1`
6. Every nonzero ideal is a power of `m`.

Also see `IsDiscreteValuationRing.TFAE` for a version assuming `¬ IsField R`.
-/
/-
**tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain [IsNoetherianRing R] [
IsLocalRing R] [IsDomain R] : List.TFAE [IsPrincipalIdealRing R, ValuationRing R
, IsDedekindDomain R, IsIntegrallyClosed R ∧ forall P : Ideal R, P != ⊥ -> P.IsP
rime -> P = maximalIdeal R, (maximalIdeal R).IsPrincipal, finrank (ResidueField 
R) (CotangentSpace R) <= 1, forall I != ⊥, exists n : Nat, I = maximalIdeal R ^ 
n]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationRing.instOfIsLocalRingOfIsBezout`：∀ {R : Type u_1} [inst : Comm
Ring R] [inst_1 : IsDomain R] [IsLocalRing R] [IsBezout R], ValuationRing R
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsBezout.TFAE`：TFAE [IsBezout R] [IsDomain R] : List.TFAE [IsNoetherianR
ing R, IsPrincipalIdealRing R, UniqueFactorizationMonoid R, WfDvdMonoid R]
· 使用定理 `ValuationRing.instIsBezout`：∀ {R : Type u_1} [inst : CommRing R] [inst_1
 : IsDomain R] [ValuationRing R], IsBezout R
· 使用定理 `IsDedekindRing.toIsIntegralClosure`：∀ {A : Type u_2} {inst : CommRing A}
 [self : IsDedekindRing A], IsIntegralClosure A A (FractionRing A)
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsLocalRing.eq_maximalIdeal`：eq_maximalIdeal {I : Ideal R} (hI : I.IsMax
imal) : I = maximalIdeal R
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `IsDedekindRing.toDimensionLEOne`：∀ {A : Type u_2} {inst : CommRing A} [s
elf : IsDedekindRing A], Ring.DimensionLEOne A
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `maximalIdeal_isPrincipal_of_isDedekindDomain`：maximalIdeal_isPrincipal_o
f_isDedekindDomain [IsLocalRing R] [IsDedekindDomain R] : (maximalIdeal R).IsPri
ncipal
· 使用定理 `IsLocalRing.finrank_cotangentSpace_le_one_iff`：∀ {R : Type u_1} [inst : 
CommRing R] [inst_1 : IsLocalRing R] [IsNoetherianRing R],   Module.finrank (IsL
ocalRing.ResidueField R) (IsLocalRi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `exists_maximalIdeal_pow_eq_of_principal`：exists_maximalIdeal_pow_eq_of_p
rincipal [IsNoetherianRing R] [IsLocalRing R] [IsDomain R] (h' : (maximalIdeal R
).IsPrincipal) (I : Ideal R) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ValuationRing.iff_ideal_total`：iff_ideal_total : ValuationRing R ↔ @Std.
Total (Ideal R) (· <= ·)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `ne_of_not_le`：ne_of_not_le (h : ¬a <= b) : a != b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Mathlib.Tactic.Order.le_of_not_lt_le`：le_of_not_lt_le {α : Type u} [Preo
rder α] {x y : α} (h1 : ¬(x < y)) (h2 : x <= y) : y <= x
· 使用引理 `Mathlib.Tactic.Order.not_lt_of_not_le`：not_lt_of_not_le {α : Type u} [Pr
eorder α] {x y : α} (h : ¬(x <= y)) : ¬(x < y)
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
Let `(R, m, k)` be a Noetherian local domain (possibly a field).
The following are equivalent:
0. `R` is a PID
1. `R` is a valuation ring
2. `R` is a Dedekind domain
3. `R` is integrally closed with at most one non-zero prime ideal
4. `m` is principal
5. `dimₖ m/m² ≤ 1`
6. Every nonzero ideal is a power of `m`.

Also see `IsDiscreteValuationRing.TFAE` for a version assuming `¬ IsField R`.
-/
theorem tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
    [IsNoetherianRing R] [IsLocalRing R] [IsDomain R] :
    List.TFAE
      [IsPrincipalIdealRing R, ValuationRing R, IsDedekindDomain R,
        IsIntegrallyClosed R ∧ ∀ P : Ideal R, P ≠ ⊥ → P.IsPrime → P = maximalIdeal R,
        (maximalIdeal R).IsPrincipal,
        finrank (ResidueField R) (CotangentSpace R) ≤ 1,
        ∀ I ≠ ⊥, ∃ n : ℕ, I = maximalIdeal R ^ n] := by
  tfae_have 1 → 2 := fun _ ↦ inferInstance
  tfae_have 2 → 1 := fun _ ↦ ((IsBezout.TFAE (R := R)).out 0 1).mp ‹_›
  tfae_have 1 → 4
  | H => ⟨inferInstance, fun P hP hP' ↦ eq_maximalIdeal (hP'.isMaximal hP)⟩
  tfae_have 4 → 3 :=
    fun ⟨h₁, h₂⟩ ↦ { h₁ with maximalOfPrime := (h₂ _ · · ▸ maximalIdeal.isMaximal R) }
  tfae_have 3 → 5 := fun h ↦ maximalIdeal_isPrincipal_of_isDedekindDomain R
  tfae_have 6 ↔ 5 := finrank_cotangentSpace_le_one_iff
  tfae_have 5 → 7 := exists_maximalIdeal_pow_eq_of_principal R
  tfae_have 7 → 2 := by
    rw [ValuationRing.iff_ideal_total]
    intro H
    constructor
    intro I J
    by_cases hI : I = ⊥; · order
    by_cases hJ : J = ⊥; · order
    obtain ⟨n, rfl⟩ := H I hI
    obtain ⟨m, rfl⟩ := H J hJ
    exact (le_total m n).imp Ideal.pow_le_pow_right Ideal.pow_le_pow_right
  tfae_finish

/--
The following are equivalent for a
Noetherian local domain that is not a field `(R, m, k)`:
0. `R` is a discrete valuation ring
1. `R` is a valuation ring
2. `R` is a Dedekind domain
3. `R` is integrally closed with a unique non-zero prime ideal
4. `m` is principal
5. `dimₖ m/m² = 1`
6. Every nonzero ideal is a power of `m`.

Also see `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain` for a version without `¬ IsField R`.
-/
/-
**IsDiscreteValuationRing.TFAE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsDiscreteValuationRing.TFAE [IsNoetherianRing R] [IsLocalRing R] [IsDomai
n R] (h : ¬IsField R) : List.TFAE [IsDiscreteValuationRing R, ValuationRing R, I
sDedekindDomain R, IsIntegrallyClosed R ∧ exists! P : Ideal R, P != ⊥ ∧ P.IsPrim
e, (maximalIdeal R).IsPrincipal, finrank (ResidueField R) (CotangentSpace R) = 1
, forall (I) (_ : I != ⊥), exists n : Nat, I = maximalIdeal R ^ n]
参数：h : ¬IsField R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `IsLocalRing.isField_iff_maximalIdeal_eq`：isField_iff_maximalIdeal_eq : I
sField R ↔ maximalIdeal R = ⊥
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain`：tfae_of_isNoetheria
nRing_of_isLocalRing_of_isDomain [IsNoetherianRing R] [IsLocalRing R] [IsDomain 
R] : List.TFAE [IsPrincipalIdealRing R, V…

--- 原说明 ---
The following are equivalent for a
Noetherian local domain that is not a field `(R, m, k)`:
0. `R` is a discrete valuation ring
1. `R` is a valuation ring
2. `R` is a Dedekind domain
3. `R` is integrally closed with a unique non-zero prime ideal
4. `m` is principal
5. `dimₖ m/m² = 1`
6. Every nonzero ideal is a power of `m`.

Also see `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain` for a version wit
hout `¬ IsField R`.
-/
theorem IsDiscreteValuationRing.TFAE [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (h : ¬IsField R) :
    List.TFAE
      [IsDiscreteValuationRing R, ValuationRing R, IsDedekindDomain R,
        IsIntegrallyClosed R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime, (maximalIdeal R).IsPrincipal,
        finrank (ResidueField R) (CotangentSpace R) = 1,
        ∀ (I) (_ : I ≠ ⊥), ∃ n : ℕ, I = maximalIdeal R ^ n] := by
  have : finrank (ResidueField R) (CotangentSpace R) = 1 ↔
      finrank (ResidueField R) (CotangentSpace R) ≤ 1 := by
    simp [Nat.le_one_iff_eq_zero_or_eq_one, finrank_cotangentSpace_eq_zero_iff, h]
  rw [this]
  have : maximalIdeal R ≠ ⊥ := isField_iff_maximalIdeal_eq.not.mp h
  convert! tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R
  · exact ⟨fun _ ↦ inferInstance, fun h ↦ { h with not_a_field' := this }⟩
  · exact ⟨fun h P h₁ h₂ ↦ h.unique ⟨h₁, h₂⟩ ⟨this, inferInstance⟩,
      fun H ↦ ⟨_, ⟨this, inferInstance⟩, fun P hP ↦ H P hP.1 hP.2⟩⟩

variable {R}
/-
**IsLocalRing.finrank_CotangentSpace_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalRing.finrank_CotangentSpace_eq_one_iff [IsNoetherianRing R] [IsLoca
lRing R] [IsDomain R] : finrank (ResidueField R) (CotangentSpace R) = 1 ↔ IsDisc
reteValuationRing R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalRing.finrank_cotangentSpace_eq_zero`：∀ (R : Type u_2) [inst : Fie
ld R], Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R
) = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `IsDiscreteValuationRing.not_a_field'`：∀ {R : Type u} {inst : CommRing R}
 {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R],   IsLocalRing.maximal
Ideal R ≠ ⊥
· 使用定理 `IsLocalRing.maximalIdeal_eq_bot`：maximalIdeal_eq_bot {R : Type*} [Field 
R] : IsLocalRing.maximalIdeal R = ⊥
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsDiscreteValuationRing.TFAE`：IsDiscreteValuationRing.TFAE [IsNoetherian
Ring R] [IsLocalRing R] [IsDomain R] (h : ¬IsField R) : List.TFAE [IsDiscreteVal
uationRing R, Valu…
-/
lemma IsLocalRing.finrank_CotangentSpace_eq_one_iff [IsNoetherianRing R] [IsLocalRing R]
    [IsDomain R] : finrank (ResidueField R) (CotangentSpace R) = 1 ↔ IsDiscreteValuationRing R := by
  by_cases hR : IsField R
  · let := hR.toField
    simp only [finrank_cotangentSpace_eq_zero, zero_ne_one, false_iff]
    exact fun h ↦ h.3 maximalIdeal_eq_bot
  · exact (IsDiscreteValuationRing.TFAE R hR).out 5 0

variable (R)
/-
**IsLocalRing.finrank_CotangentSpace_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalRing.finrank_CotangentSpace_eq_one [IsDomain R] [IsDiscreteValuatio
nRing R] : finrank (ResidueField R) (CotangentSpace R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用引理 `IsLocalRing.finrank_CotangentSpace_eq_one_iff`：IsLocalRing.finrank_Cotan
gentSpace_eq_one_iff [IsNoetherianRing R] [IsLocalRing R] [IsDomain R] : finrank
 (ResidueField R) (CotangentSpace R…
· 使用定理 `IsDedekindRing.toIsNoetherian`：∀ {A : Type u_2} {inst : CommRing A} [sel
f : IsDedekindRing A], IsNoetherian A A
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
-/
lemma IsLocalRing.finrank_CotangentSpace_eq_one [IsDomain R] [IsDiscreteValuationRing R] :
    finrank (ResidueField R) (CotangentSpace R) = 1 :=
  finrank_CotangentSpace_eq_one_iff.mpr ‹_›

open Ring in
/-
**IsDiscreteValuationRing.ringKrullDim_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsDiscreteValuationRing.ringKrullDim_eq_one [IsDomain R] [IsDiscreteValuat
ionRing R] : ringKrullDim R = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_le_of_not_lt`：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a =
 b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Ring.krullDimLE_iff`：Ring.krullDimLE_iff {n : Nat} : KrullDimLE n R ↔ ri
ngKrullDim R <= n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Ring.krullDimLE_one_iff_of_isPrime_bot`：Ring.krullDimLE_one_iff_of_isPri
me_bot [(⊥ : Ideal R).IsPrime] : Ring.KrullDimLE 1 R ↔ forall I : Ideal R, I != 
⊥ -> I.IsPrime -> I.IsMaxima…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `IsDedekindRing.toDimensionLEOne`：∀ {A : Type u_2} {inst : CommRing A} [s
elf : IsDedekindRing A], Ring.DimensionLEOne A
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用引理 `ENat.WithBot.lt_add_one_iff`：lt_add_one_iff {n : WithBot Nat∞} {m : Nat}
 : n < m + 1 ↔ n <= m
· 使用定理 `IsDiscreteValuationRing.not_isField`：not_isField : ¬IsField R
· 使用引理 `Ring.KrullDimLE.isField_of_isDomain`：Ring.KrullDimLE.isField_of_isDomain
 [IsDomain R] : IsField R
-/
lemma IsDiscreteValuationRing.ringKrullDim_eq_one [IsDomain R] [IsDiscreteValuationRing R] :
    ringKrullDim R = 1 := by
  refine eq_of_le_of_not_lt (krullDimLE_iff (n := 1).mp ?_) fun h ↦ ?_
  · exact krullDimLE_one_iff_of_isPrime_bot.mpr fun I hI hI' ↦ hI'.isMaximal hI
  · have : KrullDimLE 0 R := krullDimLE_iff.mpr (ENat.WithBot.lt_add_one_iff.mp h)
    exact IsDiscreteValuationRing.not_isField R KrullDimLE.isField_of_isDomain

open Ring in
/-
**IsDiscreteValuationRing.not_krullDimLE_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsDiscreteValuationRing.not_krullDimLE_zero [IsDomain R] [IsDiscreteValuat
ionRing R] : ¬ KrullDimLE 0 R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `IsDiscreteValuationRing.ringKrullDim_eq_one`：IsDiscreteValuationRing.rin
gKrullDim_eq_one [IsDomain R] [IsDiscreteValuationRing R] : ringKrullDim R = 1
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
-/
lemma IsDiscreteValuationRing.not_krullDimLE_zero [IsDomain R] [IsDiscreteValuationRing R] :
      ¬ KrullDimLE 0 R := by
  simp [krullDimLE_iff, ringKrullDim_eq_one R]

open Ring in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsDomain R] [IsDiscreteValuationRing R] : KrullDimLE 1 R :=
    krullDimLE_iff.mpr (IsDiscreteValuationRing.ringKrullDim_eq_one R).le
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsDedekindDomain.isPrincipalIdealRing
    [IsLocalRing R] [IsDedekindDomain R] : IsPrincipalIdealRing R :=
  ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 2 0).mp ‹_›
