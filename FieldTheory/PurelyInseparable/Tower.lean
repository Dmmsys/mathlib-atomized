/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!

# Tower law for purely inseparable extensions

This file contains results related to `Field.sepDegree`, `Field.insepDegree` and the tower law.

## Main results

- `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`: the separable degrees satisfy the
  tower law: $[E:F]_s [K:E]_s = [K:F]_s$.

- `Field.lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic`:
  `Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic`: the inseparable degrees satisfy the
  tower law: $[E:F]_i [K:E]_i = [K:F]_i$.

- `IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable`,
  `IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable'`:
  if `K / E / F` is a field extension tower, such that `E / F` is purely inseparable, then
  for any subset `S` of `K` such that `F(S) / F` is algebraic, the `E(S) / E` and `F(S) / F` have
  the same separable degree. In particular, if `S` is an intermediate field of `K / F` such that
  `S / F` is algebraic, the `E(S) / E` and `S / F` have the same separable degree.

- `minpoly.map_eq_of_isSeparable_of_isPurelyInseparable`: if `K / E / F` is a field extension tower,
  such that `E / F` is purely inseparable, then for any element `x` of `K` separable over `F`,
  it has the same minimal polynomials over `F` and over `E`.

- `Polynomial.Separable.map_irreducible_of_isPurelyInseparable`: if `E / F` is purely inseparable,
  `f` is a separable irreducible polynomial over `F`, then it is also irreducible over `E`.

## Tags

separable degree, degree, separable closure, purely inseparable

-/

public section

open Polynomial IntermediateField Field

noncomputable section

universe u v w

section TowerLaw

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
variable (K : Type w) [Field K] [Algebra F K]

variable [Algebra E K] [IsScalarTower F E K]

variable {F K} in
/-- If `K / E / F` is a field extension tower such that `E / F` is purely inseparable,
if `{ u_i }` is a family of separable elements of `K` which is `F`-linearly independent,
then it is also `E`-linearly independent. -/
/-
**LinearIndependent.map_of_isPurelyInseparable_of_isSeparable** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：LinearIndependent.map_of_isPurelyInseparable_of_isSeparable [IsPurelyInsep
arable F E] {ι : Type*} {v : ι -> K} (hsep : forall i : ι, IsSeparable F (v i)) 
(h : LinearIndependent F v) : LinearIndependent E v
参数：hsep : forall i : ι, IsSeparable F (v i)；h : LinearIndependent F v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpChar.exists`：ExpChar.exists [Ring R] [IsDomain R] : exists q, ExpChar
 R q
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `expChar_of_injective_algebraMap`：expChar_of_injective_algebraMap [CommSe
miring R] [Semiring A] [Algebra R A] (h : Function.Injective (algebraMap R A)) (
q : Nat) [ExpChar R q…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndependent_iff`：linearIndependent_iff : LinearIndependent R v ↔ f
orall l, Finsupp.linearCombination R v l = 0 -> l = 0
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `expChar_pow_pos`：expChar_pow_pos (q : Nat) [ExpChar R q] (n : Nat) : 0 <
 q ^ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Nat.add_sub_of_le`：∀ {a b : ℕ}, a ≤ b → a + (b - a) = b
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
If `K / E / F` is a field extension tower such that `E / F` is purely inseparabl
e,
if `{ u_i }` is a family of separable elements of `K` which is `F`-linearly inde
pendent,
then it is also `E`-linearly independent.
-/
theorem LinearIndependent.map_of_isPurelyInseparable_of_isSeparable [IsPurelyInseparable F E]
    {ι : Type*} {v : ι → K} (hsep : ∀ i : ι, IsSeparable F (v i))
    (h : LinearIndependent F v) : LinearIndependent E v := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  have := expChar_of_injective_algebraMap (algebraMap F K).injective q
  refine linearIndependent_iff.mpr fun l hl ↦ Finsupp.ext fun i ↦ ?_
  choose f hf using fun i ↦ (isPurelyInseparable_iff_pow_mem F q).1 ‹_› (l i)
  let n := l.support.sup f
  have := (expChar_pow_pos F q n).ne'
  replace hf (i : ι) : l i ^ q ^ n ∈ (algebraMap F E).range := by
    by_cases hs : i ∈ l.support
    · convert! pow_mem (hf i) (q ^ (n - f i)) using 1
      rw [← pow_mul, ← pow_add, Nat.add_sub_of_le (Finset.le_sup hs)]
    exact ⟨0, by rw [map_zero, Finsupp.notMem_support_iff.1 hs, zero_pow this]⟩
  choose lF hlF using hf
  let lF₀ := Finsupp.onFinset l.support lF fun i ↦ by
    contrapose
    refine fun hs ↦ (injective_iff_map_eq_zero _).mp (algebraMap F E).injective _ ?_
    rw [hlF, Finsupp.notMem_support_iff.1 hs, zero_pow this]
  replace h := linearIndependent_iff.1 (h.map_pow_expChar_pow_of_isSeparable' q n hsep :) lF₀ <| by
    replace hl := congr($hl ^ q ^ n)
    rw [Finsupp.linearCombination_apply, Finsupp.sum, sum_pow_char_pow, zero_pow this] at hl
    rw [← hl, Finsupp.linearCombination_apply,
      Finsupp.onFinset_sum _ (fun _ ↦ by exact zero_smul _ _)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp_rw [Algebra.smul_def, mul_pow, IsScalarTower.algebraMap_apply F E K, hlF, map_pow]
  refine eq_zero_of_pow_eq_zero ((hlF _).symm.trans ?_)
  convert! map_zero (algebraMap F E)
  exact congr($h i)

variable {F K} in
/-- If `K / E / F` is a field extension tower such that `E / F` is purely inseparable,
if `S` is an intermediate field of `K / F` which is separable over `F`, then `S` and `E` are
linearly disjoint over `F`. -/
/-
**IntermediateField.linearDisjoint_of_isPurelyInseparable_of_isSeparable** 是 Mat
hlib 中的一个定理，位于命名空间 ``。
形式化陈述：IntermediateField.linearDisjoint_of_isPurelyInseparable_of_isSeparable [Is
PurelyInseparable F E] (S : IntermediateField F K) [Algebra.IsSeparable F S] : S
.LinearDisjoint E
参数：S : IntermediateField F K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.exists_basis`：exists_basis : exists s : Set V, Nonempty (Ba
sis s K V)
· 使用定理 `IntermediateField.LinearDisjoint.of_basis_left`：of_basis_left {ι : Type*
} (a : Basis ι F A) (H : LinearIndependent L (A.val ∘ a)) : A.LinearDisjoint L
· 使用定理 `LinearIndependent.map_of_isPurelyInseparable_of_isSeparable`：LinearIndep
endent.map_of_isPurelyInseparable_of_isSeparable [IsPurelyInseparable F E] {ι : 
Type*} {v : ι -> K} (hsep : forall i : ι, IsSepar…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.minpoly_eq`：minpoly_eq (x : S) : minpoly K x = minpoly
 K (x : L)
· 使用定理 `Algebra.IsSeparable.isSeparable`：Algebra.IsSeparable.isSeparable [Algebr
a.IsSeparable F K] : forall x : K, IsSeparable F x
· 使用定理 `LinearIndependent.map'`：LinearIndependent.map' (hv : LinearIndependent R
 v) (f : M ->ₗ[R] M') (hf_inj : LinearMap.ker f = ⊥) : LinearIndependent R (f ∘ 
v)
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `LinearMap.ker_eq_bot_of_injective`：ker_eq_bot_of_injective {f : M ->ₛₗ[τ
₁₂] M₂} (hf : Injective f) : ker f = ⊥
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
If `K / E / F` is a field extension tower such that `E / F` is purely inseparabl
e,
if `S` is an intermediate field of `K / F` which is separable over `F`, then `S`
 and `E` are
linearly disjoint over `F`.
-/
theorem IntermediateField.linearDisjoint_of_isPurelyInseparable_of_isSeparable
    [IsPurelyInseparable F E] (S : IntermediateField F K) [Algebra.IsSeparable F S] :
    S.LinearDisjoint E :=
  have ⟨ι, ⟨b⟩⟩ := Module.Basis.exists_basis F S
  .of_basis_left b <| b.linearIndependent.map' S.val.toLinearMap
    (LinearMap.ker_eq_bot_of_injective S.val.injective)
    |>.map_of_isPurelyInseparable_of_isSeparable E fun i ↦ by
      simpa only [IsSeparable, minpoly_eq] using! Algebra.IsSeparable.isSeparable F (b i)

namespace Field

/-- If `K / E / F` is a field extension tower, such that `E / F` is purely inseparable and `K / E`
is separable, then the separable degree of `K / F` is equal to the degree of `K / E`.
It is a special case of `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`, and is an
intermediate result used to prove it. -/
/-
**Field.sepDegree_eq_of_isPurelyInseparable_of_isSeparable** 是 Mathlib 中的一个引理，位于
命名空间 `Field`。
形式化陈述：sepDegree_eq_of_isPurelyInseparable_of_isSeparable [IsPurelyInseparable F 
E] [Algebra.IsSeparable E K] : sepDegree F K = Module.rank E K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.LinearDisjoint.adjoin_rank_eq_rank_left_of_isAlgebraic
_left`：adjoin_rank_eq_rank_left_of_isAlgebraic_left (H : A.LinearDisjoint L) [Al
gebra.IsAlgebraic F A] : Module.rank L (adjoin L (A : Set E)) = Mod…
· 使用定理 `IntermediateField.linearDisjoint_of_isPurelyInseparable_of_isSeparable`：
IntermediateField.linearDisjoint_of_isPurelyInseparable_of_isSeparable [IsPurely
Inseparable F E] (S : IntermediateField F K) [Algebra.IsSepa…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.rank_top'`：∀ {F : Type u_1} [inst : Field F] {E : Type
 u_2} [inst_1 : Field E] [inst_2 : Algebra F E],   Module.rank F ↥⊤ = Module.ran
k F E
· 使用引理 `separableClosure.adjoin_eq_of_isAlgebraic_of_isSeparable`：adjoin_eq_of_i
sAlgebraic_of_isSeparable [Algebra.IsAlgebraic F E] [Algebra.IsSeparable E K] : 
adjoin E (separableClosure F K : Set K) = ⊤
· 使用定理 `Normal.toIsAlgebraic`：∀ {F : Type u_1} {K : Type u_2} {inst : Field F} {
inst_1 : Field K} {inst_2 : Algebra F K} [self : Normal F K],   Algebra.IsAlgebr
aic F K

--- 原说明 ---
If `K / E / F` is a field extension tower, such that `E / F` is purely inseparab
le and `K / E`
is separable, then the separable degree of `K / F` is equal to the degree of `K 
/ E`.
It is a special case of `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`
, and is an
intermediate result used to prove it.
-/
lemma sepDegree_eq_of_isPurelyInseparable_of_isSeparable
    [IsPurelyInseparable F E] [Algebra.IsSeparable E K] : sepDegree F K = Module.rank E K := by
  have h := (separableClosure F K).linearDisjoint_of_isPurelyInseparable_of_isSeparable E
    |>.adjoin_rank_eq_rank_left_of_isAlgebraic_left |>.symm
  rwa [separableClosure.adjoin_eq_of_isAlgebraic_of_isSeparable K, rank_top'] at h

/-- If `K / E / F` is a field extension tower, such that `E / F` is separable,
then $[E:F] [K:E]_s = [K:F]_s$.
It is a special case of `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`, and is an
intermediate result used to prove it. -/
/-
**Field.lift_rank_mul_lift_sepDegree_of_isSeparable** 是 Mathlib 中的一个引理，位于命名空间 `F
ield`。
形式化陈述：lift_rank_mul_lift_sepDegree_of_isSeparable [Algebra.IsSeparable F E] : Ca
rdinal.lift.{w} (Module.rank F E) * Cardinal.lift.{v} (sepDegree E K) = Cardinal
.lift.{v} (sepDegree F K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Field.sepDegree.eq_1`：∀ (F : Type u) (E : Type v) [inst : Field F] [inst
_1 : Field E] [inst_2 : Algebra F E],   Field.sepDegree F E = Module.rank F ↥(se
parableClo…
· 使用定理 `separableClosure.eq_restrictScalars_of_isSeparable`：separableClosure.eq_
restrictScalars_of_isSeparable [Algebra E K] [IsScalarTower F E K] [Algebra.IsSe
parable F E] : separableClosure F K = (s…
· 使用定理 `lift_rank_mul_lift_rank`：lift_rank_mul_lift_rank : Cardinal.lift.{w} (Mo
dule.rank F K) * Cardinal.lift.{v} (Module.rank K A) = Cardinal.lift.{v} (Module
.rank F A)
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V

--- 原说明 ---
If `K / E / F` is a field extension tower, such that `E / F` is separable,
then $[E:F] [K:E]_s = [K:F]_s$.
It is a special case of `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`
, and is an
intermediate result used to prove it.
-/
lemma lift_rank_mul_lift_sepDegree_of_isSeparable [Algebra.IsSeparable F E] :
    Cardinal.lift.{w} (Module.rank F E) * Cardinal.lift.{v} (sepDegree E K) =
    Cardinal.lift.{v} (sepDegree F K) := by
  rw [sepDegree, sepDegree, separableClosure.eq_restrictScalars_of_isSeparable F E K]
  exact lift_rank_mul_lift_rank F E (separableClosure E K)

/-- The same-universe version of `Field.lift_rank_mul_lift_sepDegree_of_isSeparable`. -/
/-
**Field.rank_mul_sepDegree_of_isSeparable** 是 Mathlib 中的一个引理，位于命名空间 `Field`。
形式化陈述：rank_mul_sepDegree_of_isSeparable (K : Type v) [Field K] [Algebra F K] [Al
gebra E K] [IsScalarTower F E K] [Algebra.IsSeparable F E] : Module.rank F E * s
epDegree E K = sepDegree F K
参数：K : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用引理 `Field.lift_rank_mul_lift_sepDegree_of_isSeparable`：lift_rank_mul_lift_se
pDegree_of_isSeparable [Algebra.IsSeparable F E] : Cardinal.lift.{w} (Module.ran
k F E) * Cardinal.lift.{v} (sepDegree E…

--- 原说明 ---
The same-universe version of `Field.lift_rank_mul_lift_sepDegree_of_isSeparable`
.
-/
lemma rank_mul_sepDegree_of_isSeparable (K : Type v) [Field K] [Algebra F K]
    [Algebra E K] [IsScalarTower F E K] [Algebra.IsSeparable F E] :
    Module.rank F E * sepDegree E K = sepDegree F K := by
  simpa only [Cardinal.lift_id] using lift_rank_mul_lift_sepDegree_of_isSeparable F E K

/-- If `K / E / F` is a field extension tower, such that `E / F` is separable,
then $[K:F]_i = [K:E]_i$.
It is a special case of `Field.lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic`, and is an
intermediate result used to prove it. -/
/-
**Field.insepDegree_eq_of_isSeparable** 是 Mathlib 中的一个引理，位于命名空间 `Field`。
形式化陈述：insepDegree_eq_of_isSeparable [Algebra.IsSeparable F E] : insepDegree F K 
= insepDegree E K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Field.insepDegree.eq_1`：∀ (F : Type u) (E : Type v) [inst : Field F] [in
st_1 : Field E] [inst_2 : Algebra F E],   Field.insepDegree F E = Module.rank (↥
(separableCl…
· 使用定理 `separableClosure.eq_restrictScalars_of_isSeparable`：separableClosure.eq_
restrictScalars_of_isSeparable [Algebra E K] [IsScalarTower F E K] [Algebra.IsSe
parable F E] : separableClosure F K = (s…

--- 原说明 ---
If `K / E / F` is a field extension tower, such that `E / F` is separable,
then $[K:F]_i = [K:E]_i$.
It is a special case of `Field.lift_insepDegree_mul_lift_insepDegree_of_isAlgebr
aic`, and is an
intermediate result used to prove it.
-/
lemma insepDegree_eq_of_isSeparable [Algebra.IsSeparable F E] :
    insepDegree F K = insepDegree E K := by
  rw [insepDegree, insepDegree, separableClosure.eq_restrictScalars_of_isSeparable F E K]
  rfl

/-- If `K / E / F` is a field extension tower, such that `E / F` is purely inseparable,
then $[K:F]_s = [K:E]_s$.
It is a special case of `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`, and is an
intermediate result used to prove it. -/
/-
**Field.sepDegree_eq_of_isPurelyInseparable** 是 Mathlib 中的一个引理，位于命名空间 `Field`。
形式化陈述：sepDegree_eq_of_isPurelyInseparable [IsPurelyInseparable F E] : sepDegree 
F K = sepDegree E K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Field.sepDegree.eq_1`：∀ (F : Type u) (E : Type v) [inst : Field F] [inst
_1 : Field E] [inst_2 : Algebra F E],   Field.sepDegree F E = Module.rank F ↥(se
parableClo…
· 使用定理 `separableClosure.map_eq_of_separableClosure_eq_bot`：separableClosure.map
_eq_of_separableClosure_eq_bot [Algebra E K] [IsScalarTower F E K] (h : separabl
eClosure E K = ⊥) : (separableClosure F …
· 使用定理 `separableClosure.separableClosure_eq_bot`：separableClosure.separableClos
ure_eq_bot : separableClosure (separableClosure F E) E = ⊥
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁
· 使用引理 `Field.sepDegree_eq_of_isPurelyInseparable_of_isSeparable`：sepDegree_eq_o
f_isPurelyInseparable_of_isSeparable [IsPurelyInseparable F E] [Algebra.IsSepara
ble E K] : sepDegree F K = Module.rank E K

--- 原说明 ---
If `K / E / F` is a field extension tower, such that `E / F` is purely inseparab
le,
then $[K:F]_s = [K:E]_s$.
It is a special case of `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`
, and is an
intermediate result used to prove it.
-/
lemma sepDegree_eq_of_isPurelyInseparable [IsPurelyInseparable F E] :
    sepDegree F K = sepDegree E K := by
  convert! sepDegree_eq_of_isPurelyInseparable_of_isSeparable F E (separableClosure E K)
  have : IsScalarTower F (separableClosure E K) K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [sepDegree, ← separableClosure.map_eq_of_separableClosure_eq_bot F
    (separableClosure.separableClosure_eq_bot E K)]
  exact (separableClosure F (separableClosure E K)).equivMap
    (IsScalarTower.toAlgHom F (separableClosure E K) K) |>.symm.toLinearEquiv.rank_eq

/-- If `K / E / F` is a field extension tower, such that `E / F` is purely inseparable,
then $[E:F] [K:E]_i = [K:F]_i$.
It is a special case of `Field.lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic`, and is an
intermediate result used to prove it. -/
/-
**Field.lift_rank_mul_lift_insepDegree_of_isPurelyInseparable** 是 Mathlib 中的一个引理
，位于命名空间 `Field`。
形式化陈述：lift_rank_mul_lift_insepDegree_of_isPurelyInseparable [IsPurelyInseparable
 F E] : Cardinal.lift.{w} (Module.rank F E) * Cardinal.lift.{v} (insepDegree E K
) = Cardinal.lift.{v} (insepDegree F K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.LinearDisjoint.lift_rank_right_mul_lift_adjoin_rank_eq
_of_isAlgebraic_left`：lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_lef
t (H : A.LinearDisjoint L) [Algebra.IsAlgebraic F A] : Cardinal.lift.{v} (Module
.r…
· 使用定理 `IntermediateField.linearDisjoint_of_isPurelyInseparable_of_isSeparable`：
IntermediateField.linearDisjoint_of_isPurelyInseparable_of_isSeparable [IsPurely
Inseparable F E] (S : IntermediateField F K) [Algebra.IsSepa…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `separableClosure.adjoin_eq_of_isAlgebraic`：adjoin_eq_of_isAlgebraic [Alg
ebra.IsAlgebraic F E] : adjoin E (separableClosure F K) = separableClosure E K
· 使用定理 `Normal.toIsAlgebraic`：∀ {F : Type u_1} {K : Type u_2} {inst : Field F} {
inst_1 : Field K} {inst_2 : Algebra F K} [self : Normal F K],   Algebra.IsAlgebr
aic F K

--- 原说明 ---
If `K / E / F` is a field extension tower, such that `E / F` is purely inseparab
le,
then $[E:F] [K:E]_i = [K:F]_i$.
It is a special case of `Field.lift_insepDegree_mul_lift_insepDegree_of_isAlgebr
aic`, and is an
intermediate result used to prove it.
-/
lemma lift_rank_mul_lift_insepDegree_of_isPurelyInseparable [IsPurelyInseparable F E] :
    Cardinal.lift.{w} (Module.rank F E) * Cardinal.lift.{v} (insepDegree E K) =
    Cardinal.lift.{v} (insepDegree F K) := by
  have h := (separableClosure F K).linearDisjoint_of_isPurelyInseparable_of_isSeparable E
    |>.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_left
  rwa [separableClosure.adjoin_eq_of_isAlgebraic] at h

/-- The same-universe version of `Field.lift_rank_mul_lift_insepDegree_of_isPurelyInseparable`. -/
/-
**Field.rank_mul_insepDegree_of_isPurelyInseparable** 是 Mathlib 中的一个引理，位于命名空间 `F
ield`。
形式化陈述：rank_mul_insepDegree_of_isPurelyInseparable (K : Type v) [Field K] [Algebr
a F K] [Algebra E K] [IsScalarTower F E K] [IsPurelyInseparable F E] : Module.ra
nk F E * insepDegree E K = insepDegree F K
参数：K : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用引理 `Field.lift_rank_mul_lift_insepDegree_of_isPurelyInseparable`：lift_rank_m
ul_lift_insepDegree_of_isPurelyInseparable [IsPurelyInseparable F E] : Cardinal.
lift.{w} (Module.rank F E) * Cardinal.lift.{v} (i…

--- 原说明 ---
The same-universe version of `Field.lift_rank_mul_lift_insepDegree_of_isPurelyIn
separable`.
-/
lemma rank_mul_insepDegree_of_isPurelyInseparable (K : Type v) [Field K] [Algebra F K]
    [Algebra E K] [IsScalarTower F E K] [IsPurelyInseparable F E] :
    Module.rank F E * insepDegree E K = insepDegree F K := by
  simpa only [Cardinal.lift_id] using lift_rank_mul_lift_insepDegree_of_isPurelyInseparable F E K

/-- If `K / E / F` is a field extension tower, such that `E / F` is algebraic, then their
separable degrees satisfy the tower law: $[E:F]_s [K:E]_s = [K:F]_s$. -/
/-
**Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic** 是 Mathlib 中的一个定理，位于命名
空间 `Field`。
形式化陈述：lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic [Algebra.IsAlgebraic F E]
 : Cardinal.lift.{w} (sepDegree F E) * Cardinal.lift.{v} (sepDegree E K) = Cardi
nal.lift.{v} (sepDegree F K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Field.lift_rank_mul_lift_sepDegree_of_isSeparable`：lift_rank_mul_lift_se
pDegree_of_isSeparable [Algebra.IsSeparable F E] : Cardinal.lift.{w} (Module.ran
k F E) * Cardinal.lift.{v} (sepDegree E…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Field.sepDegree_eq_of_isPurelyInseparable`：sepDegree_eq_of_isPurelyInsep
arable [IsPurelyInseparable F E] : sepDegree F K = sepDegree E K

--- 原说明 ---
If `K / E / F` is a field extension tower, such that `E / F` is algebraic, then 
their
separable degrees satisfy the tower law: $[E:F]_s [K:E]_s = [K:F]_s$.
-/
theorem lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic [Algebra.IsAlgebraic F E] :
    Cardinal.lift.{w} (sepDegree F E) * Cardinal.lift.{v} (sepDegree E K) =
    Cardinal.lift.{v} (sepDegree F K) := by
  have h := lift_rank_mul_lift_sepDegree_of_isSeparable F (separableClosure F E) K
  rwa [sepDegree_eq_of_isPurelyInseparable (separableClosure F E) E K] at h

/-- The same-universe version of `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`. -/
@[stacks 09HK "Part 1"]
/-
**Field.sepDegree_mul_sepDegree_of_isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 `Field`
。
形式化陈述：sepDegree_mul_sepDegree_of_isAlgebraic (K : Type v) [Field K] [Algebra F K
] [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlgebraic F E] : sepDegree F E 
* sepDegree E K = sepDegree F K
参数：K : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`：lift_sepDegree_m
ul_lift_sepDegree_of_isAlgebraic [Algebra.IsAlgebraic F E] : Cardinal.lift.{w} (
sepDegree F E) * Cardinal.lift.{v} (sepDegre…

--- 原说明 ---
The same-universe version of `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgeb
raic`.
-/
theorem sepDegree_mul_sepDegree_of_isAlgebraic (K : Type v) [Field K] [Algebra F K]
    [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlgebraic F E] :
    sepDegree F E * sepDegree E K = sepDegree F K := by
  simpa only [Cardinal.lift_id] using lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic F E K

/-- If `K / E / F` is a field extension tower, such that `E / F` is algebraic, then their
inseparable degrees satisfy the tower law: $[E:F]_i [K:E]_i = [K:F]_i$. -/
/-
**Field.lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic** 是 Mathlib 中的一个定理，
位于命名空间 `Field`。
形式化陈述：lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic [Algebra.IsAlgebraic 
F E] : Cardinal.lift.{w} (insepDegree F E) * Cardinal.lift.{v} (insepDegree E K)
 = Cardinal.lift.{v} (insepDegree F K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Field.lift_rank_mul_lift_insepDegree_of_isPurelyInseparable`：lift_rank_m
ul_lift_insepDegree_of_isPurelyInseparable [IsPurelyInseparable F E] : Cardinal.
lift.{w} (Module.rank F E) * Cardinal.lift.{v} (i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Field.insepDegree_eq_of_isSeparable`：insepDegree_eq_of_isSeparable [Alge
bra.IsSeparable F E] : insepDegree F K = insepDegree E K

--- 原说明 ---
If `K / E / F` is a field extension tower, such that `E / F` is algebraic, then 
their
inseparable degrees satisfy the tower law: $[E:F]_i [K:E]_i = [K:F]_i$.
-/
theorem lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic [Algebra.IsAlgebraic F E] :
    Cardinal.lift.{w} (insepDegree F E) * Cardinal.lift.{v} (insepDegree E K) =
    Cardinal.lift.{v} (insepDegree F K) := by
  have h := lift_rank_mul_lift_insepDegree_of_isPurelyInseparable (separableClosure F E) E K
  rwa [← insepDegree_eq_of_isSeparable F (separableClosure F E) K] at h

/-- The same-universe version of `Field.lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic`. -/
@[stacks 09HK "Part 2"]
/-
**Field.insepDegree_mul_insepDegree_of_isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 `Fi
eld`。
形式化陈述：insepDegree_mul_insepDegree_of_isAlgebraic (K : Type v) [Field K] [Algebra
 F K] [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlgebraic F E] : insepDegre
e F E * insepDegree E K = insepDegree F K
参数：K : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Field.lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic`：lift_insepDe
gree_mul_lift_insepDegree_of_isAlgebraic [Algebra.IsAlgebraic F E] : Cardinal.li
ft.{w} (insepDegree F E) * Cardinal.lift.{v} (in…

--- 原说明 ---
The same-universe version of `Field.lift_insepDegree_mul_lift_insepDegree_of_isA
lgebraic`.
-/
theorem insepDegree_mul_insepDegree_of_isAlgebraic (K : Type v) [Field K] [Algebra F K]
    [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlgebraic F E] :
    insepDegree F E * insepDegree E K = insepDegree F K := by
  simpa only [Cardinal.lift_id] using lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic F E K

/-- If `K / E / F` is a field extension tower, such that `E / F` is algebraic, then their
inseparable degrees, as natural numbers, satisfy the tower law: $[E:F]_i [K:E]_i = [K:F]_i$. -/
@[stacks 09HK "Part 2, `finInsepDegree` variant"]
/-
**Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic** 是 Mathlib 中的一个定理，位于命名
空间 `Field`。
形式化陈述：finInsepDegree_mul_finInsepDegree_of_isAlgebraic [Algebra.IsAlgebraic F E]
 : finInsepDegree F E * finInsepDegree E K = finInsepDegree F K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `Field.lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic`：lift_insepDe
gree_mul_lift_insepDegree_of_isAlgebraic [Algebra.IsAlgebraic F E] : Cardinal.li
ft.{w} (insepDegree F E) * Cardinal.lift.{v} (in…

--- 原说明 ---
If `K / E / F` is a field extension tower, such that `E / F` is algebraic, then 
their
inseparable degrees, as natural numbers, satisfy the tower law: $[E:F]_i [K:E]_i
 = [K:F]_i$.
-/
theorem finInsepDegree_mul_finInsepDegree_of_isAlgebraic [Algebra.IsAlgebraic F E] :
    finInsepDegree F E * finInsepDegree E K = finInsepDegree F K := by
  simpa only [map_mul, Cardinal.toNat_lift] using!
    congr(Cardinal.toNat $(lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic F E K))

end Field

variable {F K} in
/-- If `K / E / F` is a field extension tower, such that `E / F` is purely inseparable, then
for any subset `S` of `K` such that `F(S) / F` is algebraic, the `E(S) / E` and `F(S) / F` have
the same separable degree. -/
/-
**IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable** 
是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparabl
e (S : Set K) [Algebra.IsAlgebraic F (adjoin F S)] [IsPurelyInseparable F E] : s
epDegree E (adjoin E S) = sepDegree F (adjoin F S)
参数：S : Set K；adjoin F S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IntermediateField.restrictScalars_adjoin_of_algEquiv`：restrictScalars_ad
join_of_algEquiv {L L' : Type*} [Field L] [Field L'] [Algebra F L] [Algebra L E]
 [Algebra F L'] [Algebra L' E] [IsScalarTo…
· 使用定理 `IntermediateField.restrictScalars_adjoin`：restrictScalars_adjoin (K : In
termediateField F E) (S : Set E) : restrictScalars F (adjoin K S) = adjoin F (K 
union S)
· 使用定理 `IntermediateField.adjoin.mono`：∀ (F : Type u_1) [inst : Field F] {E : Ty
pe u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (S T : Set E),   S ⊆ T → Inter
mediateField.adjoin…
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `ExpChar.exists`：ExpChar.exists [Ring R] [IsDomain R] : exists q, ExpChar
 R q
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IntermediateField.restrictScalars_injective`：restrictScalars_injective :
 Function.Injective (restrictScalars K : IntermediateField L' L -> IntermediateF
ield K L)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IntermediateField.extendScalars_restrictScalars`：extendScalars_restrictS
calars : (extendScalars h).restrictScalars K = E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.adjoin_self`：adjoin_self (K : IntermediateField F E) :
 adjoin F K = K
· 使用定理 `IntermediateField.adjoin_adjoin_comm`：adjoin_adjoin_comm (T : Set E) : (
adjoin (adjoin F S) T).restrictScalars F = (adjoin (adjoin F T) S).restrictScala
rs F
· 使用定理 `IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem`：isPurelyInsepa
rable_adjoin_iff_pow_mem (q : Nat) [hF : ExpChar F q] {S : Set E} : IsPurelyInse
parable F (adjoin F S) ↔ forall x in S, exists…
· 使用定理 `IsPurelyInseparable.pow_mem`：IsPurelyInseparable.pow_mem [IsPurelyInsepa
rable F E] : exists n : Nat, x ^ q ^ n in (algebraMap F E).range
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
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
· 使用定理 `AlgHom.toRingHom_eq_coe`：toRingHom_eq_coe (f : A ->ₐ[R] B) : f.toRingHom
 = f
· 使用定理 `IsScalarTower.coe_toAlgHom`：coe_toAlgHom : ↑(toAlgHom R S A) = algebraMa
p S A
· 使用定理 `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`：lift_sepDegree_m
ul_lift_sepDegree_of_isAlgebraic [Algebra.IsAlgebraic F E] : Cardinal.lift.{w} (
sepDegree F E) * Cardinal.lift.{v} (sepDegre…
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
If `K / E / F` is a field extension tower, such that `E / F` is purely inseparab
le, then
for any subset `S` of `K` such that `F(S) / F` is algebraic, the `E(S) / E` and 
`F(S) / F` have
the same separable degree.
-/
theorem IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable
    (S : Set K) [Algebra.IsAlgebraic F (adjoin F S)] [IsPurelyInseparable F E] :
    sepDegree E (adjoin E S) = sepDegree F (adjoin F S) := by
  set M := adjoin F S
  set L := adjoin E S
  let E' := (IsScalarTower.toAlgHom F E K).fieldRange
  let j : E ≃ₐ[F] E' := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K)
  have hi : M ≤ L.restrictScalars F := by
    rw [restrictScalars_adjoin_of_algEquiv (E := K) j rfl, restrictScalars_adjoin]
    exact adjoin.mono _ _ _ Set.subset_union_right
  let i : M →+* L := Subsemiring.inclusion hi
  let : Algebra M L := i.toAlgebra
  let : SMul M L := Algebra.toSMul
  have : IsScalarTower F M L := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  have : IsPurelyInseparable M L := by
    change IsPurelyInseparable M (extendScalars hi)
    obtain ⟨q, _⟩ := ExpChar.exists F
    have : extendScalars hi = adjoin M (E' : Set K) := restrictScalars_injective F <| by
      conv_lhs => rw [extendScalars_restrictScalars, restrictScalars_adjoin_of_algEquiv
        (E := K) j rfl, ← adjoin_self F E', adjoin_adjoin_comm]
    rw [this, isPurelyInseparable_adjoin_iff_pow_mem _ _ q]
    rintro x ⟨y, hy⟩
    obtain ⟨n, z, hz⟩ := IsPurelyInseparable.pow_mem F q y
    refine ⟨n, algebraMap F M z, ?_⟩
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F E K, hz, ← hy, map_pow,
      AlgHom.toRingHom_eq_coe, IsScalarTower.coe_toAlgHom]
  have h := lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic F E L
  rw [IsPurelyInseparable.sepDegree_eq_one F E, Cardinal.lift_one, one_mul] at h
  rw [Cardinal.lift_injective h, ← sepDegree_mul_sepDegree_of_isAlgebraic F M L,
    IsPurelyInseparable.sepDegree_eq_one M L, mul_one]

variable {F K} in
/-- If `K / E / F` is a field extension tower, such that `E / F` is purely inseparable, then
for any intermediate field `S` of `K / F` such that `S / F` is algebraic, the `E(S) / E` and
`S / F` have the same separable degree. -/
/-
**IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable'**
 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparabl
e' (S : IntermediateField F K) [Algebra.IsAlgebraic F S] [IsPurelyInseparable F 
E] : sepDegree E (adjoin E (S : Set K)) = sepDegree F S
参数：S : IntermediateField F K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.adjoin_self`：adjoin_self (K : IntermediateField F E) :
 adjoin F K = K
· 使用定理 `IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInsepara
ble`：IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable
 (S : Set K) [Algebra.IsAlgebraic F (adjoin F S)] [IsPurelyInsepa…

--- 原说明 ---
If `K / E / F` is a field extension tower, such that `E / F` is purely inseparab
le, then
for any intermediate field `S` of `K / F` such that `S / F` is algebraic, the `E
(S) / E` and
`S / F` have the same separable degree.
-/
theorem IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable'
    (S : IntermediateField F K) [Algebra.IsAlgebraic F S] [IsPurelyInseparable F E] :
    sepDegree E (adjoin E (S : Set K)) = sepDegree F S := by
  have : Algebra.IsAlgebraic F (adjoin F (S : Set K)) := by rwa [adjoin_self]
  have := sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable (F := F) E (S : Set K)
  rwa [adjoin_self] at this

variable {F K} in
/-- If `K / E / F` is a field extension tower, such that `E / F` is purely inseparable, then
for any element `x` of `K` separable over `F`, it has the same minimal polynomials over `F` and
over `E`. -/
/-
**minpoly.map_eq_of_isSeparable_of_isPurelyInseparable** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：minpoly.map_eq_of_isSeparable_of_isPurelyInseparable (x : K) (hsep : IsSep
arable F x) [IsPurelyInseparable F E] : (minpoly F x).map (algebraMap F E) = min
poly E x
参数：x : K；hsep : IsSeparable F x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSeparable.isIntegral`：IsSeparable.isIntegral {x : K} (h : IsSeparable 
F x) : IsIntegral F x
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
· 使用引理 `Polynomial.eq_of_monic_of_dvd_of_natDegree_le`：eq_of_monic_of_dvd_of_nat
Degree_le {p q : R[X]} (hp : p.Monic) (hq : q.Monic) (hdvd : p ∣ q) (hdeg : q.na
tDegree <= p.natDegree) : q = p
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `minpoly.dvd_map_of_isScalarTower`：dvd_map_of_isScalarTower (A K : Type*)
 {R : Type*} [CommRing A] [Field K] [Ring R] [Algebra A K] [Algebra A R] [Algebr
a K R] [IsScalarTower …
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `IsSeparable.tower_top`：IsSeparable.tower_top {x : E} (h : IsSeparable F 
x) : IsSeparable L x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`：Intermediat
eField.isSeparable_adjoin_simple_iff_isSeparable {x : E} : Algebra.IsSeparable F
 F⟮x⟯ ↔ IsSeparable F x
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_map`：natDegree_map (f : R ->+* S) : (p.map f).natDe
gree = p.natDegree
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.adjoin.finrank`：∀ {K : Type u} [inst : Field K] {L : T
ype u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegral K x → M
odule.finrank K ↥K⟮x⟯ …
· 使用定理 `Field.finSepDegree_eq_finrank_of_isSeparable`：finSepDegree_eq_finrank_of
_isSeparable [Algebra.IsSeparable F E] : finSepDegree F E = finrank F E
· 使用定理 `Field.finSepDegree_eq`：finSepDegree_eq [Algebra.IsAlgebraic F E] : finSe
pDegree F E = Cardinal.toNat (sepDegree F E)
· 使用定理 `IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInsepara
ble`：IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable
 (S : Set K) [Algebra.IsAlgebraic F (adjoin F S)] [IsPurelyInsepa…

--- 原说明 ---
If `K / E / F` is a field extension tower, such that `E / F` is purely inseparab
le, then
for any element `x` of `K` separable over `F`, it has the same minimal polynomia
ls over `F` and
over `E`.
-/
theorem minpoly.map_eq_of_isSeparable_of_isPurelyInseparable (x : K)
    (hsep : IsSeparable F x) [IsPurelyInseparable F E] :
    (minpoly F x).map (algebraMap F E) = minpoly E x := by
  have hi := IsSeparable.isIntegral hsep
  have hi' : IsIntegral E x := IsIntegral.tower_top hi
  refine eq_of_monic_of_dvd_of_natDegree_le (monic hi') ((monic hi).map (algebraMap F E))
    (dvd_map_of_isScalarTower F E x) (le_of_eq ?_)
  have hsep' := IsSeparable.tower_top E hsep
  have := (isSeparable_adjoin_simple_iff_isSeparable _ _).2 hsep
  have := (isSeparable_adjoin_simple_iff_isSeparable _ _).2 hsep'
  have := Algebra.IsSeparable.isAlgebraic F F⟮x⟯
  rw [Polynomial.natDegree_map, ← adjoin.finrank hi, ← adjoin.finrank hi',
    ← finSepDegree_eq_finrank_of_isSeparable F _, ← finSepDegree_eq_finrank_of_isSeparable E _,
    finSepDegree_eq, finSepDegree_eq,
    sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable (F := F) E]

variable {F} in
/-- If `E / F` is a purely inseparable field extension, `f` is a separable irreducible polynomial
over `F`, then it is also irreducible over `E`. -/
/-
**Polynomial.Separable.map_irreducible_of_isPurelyInseparable** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：Polynomial.Separable.map_irreducible_of_isPurelyInseparable {f : F[X]} (hs
ep : f.Separable) (hirr : Irreducible f) [IsPurelyInseparable F E] : Irreducible
 (f.map (algebraMap F E))
参数：hsep : f.Separable；hirr : Irreducible f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgClosed.exists_aeval_eq_zero`：exists_aeval_eq_zero {R : Type*} [Comm
Semiring R] [IsAlgClosed k] [Algebra R k] [FaithfulSMul R k] (p : R[X]) (hp : p.
degree != 0) : exists …
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.natDegree_pos_iff_degree_pos`：natDegree_pos_iff_degree_pos : 
0 < natDegree p ↔ 0 < degree p
· 使用定理 `Irreducible.natDegree_pos`：natDegree_pos (h : Irreducible f) : 0 < f.nat
Degree
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.isUnit_C`：isUnit_C {x : R} : IsUnit (C x) ↔ IsUnit x
· 使用引理 `IsUnit.inv`：inv (h : IsUnit a) : IsUnit a⁻¹
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUnit.unit_spec`：unit_spec (h : IsUnit a) : ↑h.unit = a
· 使用定理 `minpoly.eq_of_irreducible`：eq_of_irreducible [Nontrivial B] {p : A[X]} (
hp1 : Irreducible p) (hp2 : Polynomial.aeval x p = 0) : p * C p.leadingCoeff⁻¹ =
 minpoly A x
· 使用定理 `Associated.map`：map {M N : Type*} [Monoid M] [Monoid N] {F : Type*} [Fun
Like F M N] [MonoidHomClass F M N] (f : F) {x y : M} (ha : Associated x y) : Ass
ocia…
· 使用定理 `minpoly.map_eq_of_isSeparable_of_isPurelyInseparable`：minpoly.map_eq_of_
isSeparable_of_isPurelyInseparable (x : K) (hsep : IsSeparable F x) [IsPurelyIns
eparable F E] : (minpoly F x).map (algebra…
· 使用定理 `AlgebraicClosure.instIsScalarTower`：∀ (k : Type u) [inst : Field k] {R :
 Type u_1} {S : Type u_2} [inst_1 : CommSemiring R] [inst_2 : CommSemiring S]   
[inst_3 : Algebra R S] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Associated.separable`：∀ {R : Type u} [inst : CommSemiring R] {f g : Poly
nomial R}, Associated f g → f.Separable → g.Separable
· 使用定理 `Associated.irreducible_iff`：∀ {M : Type u_1} [inst : Monoid M] {p q : M}
, Associated p q → (Irreducible p ↔ Irreducible q)
· 使用定理 `minpoly.irreducible`：irreducible (hx : IsIntegral A x) : Irreducible (mi
npoly A x)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A

--- 原说明 ---
If `E / F` is a purely inseparable field extension, `f` is a separable irreducib
le polynomial
over `F`, then it is also irreducible over `E`.
-/
theorem Polynomial.Separable.map_irreducible_of_isPurelyInseparable {f : F[X]} (hsep : f.Separable)
    (hirr : Irreducible f) [IsPurelyInseparable F E] : Irreducible (f.map (algebraMap F E)) := by
  let K := AlgebraicClosure E
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero K f
    (natDegree_pos_iff_degree_pos.1 hirr.natDegree_pos).ne'
  have ha : Associated f (minpoly F x) := by
    have := isUnit_C.2 (leadingCoeff_ne_zero.2 hirr.ne_zero).isUnit.inv
    exact ⟨this.unit, by rw [IsUnit.unit_spec, minpoly.eq_of_irreducible hirr hx]⟩
  have ha' : Associated (f.map (algebraMap F E)) ((minpoly F x).map (algebraMap F E)) :=
    ha.map (mapRingHom (algebraMap F E)).toMonoidHom
  have heq := minpoly.map_eq_of_isSeparable_of_isPurelyInseparable E x (ha.separable hsep)
  rw [ha'.irreducible_iff, heq]
  exact minpoly.irreducible (Algebra.IsIntegral.isIntegral x)

end TowerLaw

