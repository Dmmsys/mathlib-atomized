/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.BaseChange

/-!

# Locality of `Algebra.FiniteType`

In this file we show that finite-type is local on the source and the target.

## Main results

- `Algebra.FiniteType.of_span_eq_top_source`: finite-type is local on the (algebraic) source
- `Algebra.FiniteType.of_span_eq_top_target`: finite-type is local on the (algebraic) target

-/

public section

section Algebra

open scoped Pointwise TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R)
variable (R' S' : Type*) [CommRing R'] [CommRing S']
variable [Algebra R R'] [Algebra S S']

variable {S'} in
open scoped Classical in
/-- Let `S` be an `R`-algebra, `M` a submonoid of `S`, `S' = M⁻¹S`.
Suppose the image of some `x : S` falls in the adjoin of some finite `s ⊆ S'` over `R`,
and `A` is an `R`-subalgebra of `S` containing both `M` and the numerators of `s`.
Then, there exists some `m : M` such that `m • x` falls in `A`.
-/
/-
**IsLocalization.exists_smul_mem_of_mem_adjoin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.exists_smul_mem_of_mem_adjoin [Algebra R S'] [IsScalarTower
 R S S'] (M : Submonoid S) [IsLocalization M S'] (x : S) (s : Finset S') (A : Su
balgebra R S) (hA₁ : (IsLocalization.finsetIntegerMultiple M s : Set S) subseteq
 A) (hA₂ : M <= A.toSubmonoid) (hx : algebraMap S S' x in Algebra.adjoin R (s : 
Set S')) : exists m : M, m • x in A
参数：M : Submonoid S；x : S；s : Finset S'；A : Subalgebra R S；hA₁ : (IsLocalization.
finsetIntegerMultiple M s : Set S) subseteq A；hA₂ : M <= A.toSubmonoid；hx : alge
braMap S S' x in Algebra.adjoin R (s : Set S')。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.finsetIntegerMultiple_image`：finsetIntegerMultiple_image 
[DecidableEq R] (s : Finset S) : algebraMap R S '' finsetIntegerMultiple M s = c
ommonDenomOfFinset M s • (s : Se…
· 使用定理 `Algebra.pow_smul_mem_of_smul_subset_of_mem_adjoin`：pow_smul_mem_of_smul_
subset_of_mem_adjoin [CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower
 R A B] (r : A) (s : Set B) (B' : Subal…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.eq_iff_exists`：eq_iff_exists {x y} : algebraMap R S x = a
lgebraMap R S y ↔ exists c : M, ↑c * x = ↑c * y
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Submonoid.coe_mul`：coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y
· 使用定理 `SubmonoidClass.coe_pow`：coe_pow {M} [Monoid M] {A : Type*} [SetLike A M]
 [SubmonoidClass A M] {S : A} (x : S) (n : Nat) : ↑(x ^ n) = (x : M) ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Subalgebra.mul_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x

--- 原说明 ---
Let `S` be an `R`-algebra, `M` a submonoid of `S`, `S' = M⁻¹S`.
Suppose the image of some `x : S` falls in the adjoin of some finite `s ⊆ S'` ov
er `R`,
and `A` is an `R`-subalgebra of `S` containing both `M` and the numerators of `s
`.
Then, there exists some `m : M` such that `m • x` falls in `A`.
-/
theorem IsLocalization.exists_smul_mem_of_mem_adjoin [Algebra R S']
    [IsScalarTower R S S'] (M : Submonoid S) [IsLocalization M S'] (x : S) (s : Finset S')
    (A : Subalgebra R S) (hA₁ : (IsLocalization.finsetIntegerMultiple M s : Set S) ⊆ A)
    (hA₂ : M ≤ A.toSubmonoid) (hx : algebraMap S S' x ∈ Algebra.adjoin R (s : Set S')) :
    ∃ m : M, m • x ∈ A := by
  let g : S →ₐ[R] S' := IsScalarTower.toAlgHom R S S'
  let y := IsLocalization.commonDenomOfFinset M s
  have hx₁ : (y : S) • (s : Set S') = g '' _ :=
    (IsLocalization.finsetIntegerMultiple_image _ s).symm
  obtain ⟨n, hn⟩ :=
    Algebra.pow_smul_mem_of_smul_subset_of_mem_adjoin (y : S) (s : Set S') (A.map g)
      (by rw [hx₁]; exact Set.image_mono hA₁) hx (Set.mem_image_of_mem _ (hA₂ y.2))
  obtain ⟨x', hx', hx''⟩ := hn n (le_of_eq rfl)
  rw [Algebra.smul_def, ← map_mul] at hx''
  obtain ⟨a, ha₂⟩ := (IsLocalization.eq_iff_exists M S').mp hx''
  use a * y ^ n
  convert! A.mul_mem hx' (hA₂ a.prop) using 1
  rw [Submonoid.smul_def, smul_eq_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow, mul_assoc, ← ha₂,
    mul_comm]

variable {S'} in
open scoped Classical in
/-- Let `S` be an `R`-algebra, `M` a submonoid of `R`, and `S' = M⁻¹S`.
If the image of some `x : S` falls in the adjoin of some finite `s ⊆ S'` over `R`,
then there exists some `m : M` such that `m • x` falls in the
adjoin of `IsLocalization.finsetIntegerMultiple _ s` over `R`.
-/
/-
**IsLocalization.lift_mem_adjoin_finsetIntegerMultiple** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：IsLocalization.lift_mem_adjoin_finsetIntegerMultiple [Algebra R S'] [IsSca
larTower R S S'] [IsLocalization (M.map (algebraMap R S)) S'] (x : S) (s : Finse
t S') (hx : algebraMap S S' x in Algebra.adjoin R (s : Set S')) : exists m : M, 
m • x in Algebra.adjoin R (IsLocalization.finsetIntegerMultiple (M.map (algebraM
ap R S)) s : Set S)
参数：M.map (algebraMap R S)；x : S；s : Finset S'；hx : algebraMap S S' x in Algebra.
adjoin R (s : Set S')。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsLocalization.exists_smul_mem_of_mem_adjoin`：IsLocalization.exists_smul
_mem_of_mem_adjoin [Algebra R S'] [IsScalarTower R S S'] (M : Submonoid S) [IsLo
calization M S'] (x : S) (s : Fins…
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Subalgebra.algebraMap_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemir
ing R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   (r : 
R), (algebraMap…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
Let `S` be an `R`-algebra, `M` a submonoid of `R`, and `S' = M⁻¹S`.
If the image of some `x : S` falls in the adjoin of some finite `s ⊆ S'` over `R
`,
then there exists some `m : M` such that `m • x` falls in the
adjoin of `IsLocalization.finsetIntegerMultiple _ s` over `R`.
-/
theorem IsLocalization.lift_mem_adjoin_finsetIntegerMultiple [Algebra R S']
    [IsScalarTower R S S'] [IsLocalization (M.map (algebraMap R S)) S'] (x : S) (s : Finset S')
    (hx : algebraMap S S' x ∈ Algebra.adjoin R (s : Set S')) :
    ∃ m : M, m • x ∈
      Algebra.adjoin R
        (IsLocalization.finsetIntegerMultiple (M.map (algebraMap R S)) s : Set S) := by
  obtain ⟨⟨_, a, ha, rfl⟩, e⟩ :=
    IsLocalization.exists_smul_mem_of_mem_adjoin (M.map (algebraMap R S)) x s (Algebra.adjoin R _)
      Algebra.subset_adjoin (by rintro _ ⟨a, _, rfl⟩; exact Subalgebra.algebraMap_mem _ a) hx
  refine ⟨⟨a, ha⟩, ?_⟩
  simpa only [Submonoid.smul_def, algebraMap_smul] using e

/-- Finite-type can be checked on a standard covering of the target. -/
/-
**Algebra.FiniteType.of_span_eq_top_target** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.FiniteType.of_span_eq_top_target (s : Set S) (hs : Ideal.span (s :
 Set S) = ⊤) (h : forall x in s, Algebra.FiniteType R (Localization.Away x)) : A
lgebra.FiniteType R S
参数：s : Set S；hs : Ideal.span (s : Set S) = ⊤；h : forall x in s, Algebra.FiniteTy
pe R (Localization.Away x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.span_eq_top_iff_finite`：span_eq_top_iff_finite (s : Set α) : span 
s = ⊤ ↔ exists s' : Finset α, ↑s' subseteq s ∧ span (s' : Set α) = ⊤
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Algebra.FiniteType.out`：∀ {R : Type uR} {A : Type uA} {inst : CommSemiri
ng R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : Algebra.FiniteType 
R A], ⊤.FG
· 使用定理 `Finsupp.mem_span_iff_linearCombination`：mem_span_iff_linearCombination (
s : Set M) (x : M) : x in span R s ↔ exists l : s ->₀ R, linearCombination R (↑)
 l = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Subalgebra.mem_of_span_eq_top_of_smul_pow_mem`：mem_of_span_eq_top_of_smu
l_pow_mem (s : Set S) (l : s ->₀ S) (hs : Finsupp.linearCombination S ((↑) : s -
> S) l = 1) (hs' : s subseteq S') (…
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用引理 `Finset.coe_biUnion`：coe_biUnion : (s.biUnion t : Set β) = ⋃ x in (s : Se
t α), t x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsLocalization.exists_smul_mem_of_mem_adjoin`：IsLocalization.exists_smul
_mem_of_mem_adjoin [Algebra R S'] [IsScalarTower R S S'] (M : Submonoid S) [IsLo
calization M S'] (x : S) (s : Fins…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Finset.mem_attach`：mem_attach (s : Finset α) : forall x, x in s.attach
· 使用定理 `Submonoid.powers_eq_closure`：powers_eq_closure (n : M) : powers n = clos
ure {n}
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Finite-type can be checked on a standard covering of the target.
-/
lemma Algebra.FiniteType.of_span_eq_top_target (s : Set S) (hs : Ideal.span (s : Set S) = ⊤)
    (h : ∀ x ∈ s, Algebra.FiniteType R (Localization.Away x)) :
    Algebra.FiniteType R S := by
  obtain ⟨s, h₁, hs⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
  replace h (i : s) : Algebra.FiniteType R (Localization.Away i.val) := h i (h₁ i.property)
  classical
  -- Suppose `s : Finset S` spans `S`, and each `Sᵣ` is finitely generated as an `R`-algebra.
  -- Say `t r : Finset Sᵣ` generates `Sᵣ`. By assumption, we may find `lᵢ` such that
  -- `∑ lᵢ * sᵢ = 1`. I claim that all `s` and `l` and the numerators of `t` and generates `S`.
  replace h := fun r => (h r).1
  choose t ht using h
  obtain ⟨l, hl⟩ :=
    (Finsupp.mem_span_iff_linearCombination S (s : Set S) 1).mp
      (show (1 : S) ∈ Ideal.span (s : Set S) by rw [hs]; trivial)
  let sf := fun x : s => IsLocalization.finsetIntegerMultiple (Submonoid.powers (x : S)) (t x)
  use s.attach.biUnion sf ∪ s ∪ l.support.image l
  rw [_root_.eq_top_iff]
  -- We need to show that every `x` falls in the subalgebra generated by those elements.
  -- Since all `s` and `l` are in the subalgebra, it suffices to check that `sᵢ ^ nᵢ • x` falls in
  -- the algebra for each `sᵢ` and some `nᵢ`.
  rintro x -
  apply Subalgebra.mem_of_span_eq_top_of_smul_pow_mem _ (s : Set S) l hl _ _ x _
  · intro x hx
    apply Algebra.subset_adjoin
    rw [Finset.coe_union, Finset.coe_union]
    exact Or.inl (Or.inr hx)
  · intro i
    by_cases h : l i = 0; · rw [h]; exact zero_mem _
    apply Algebra.subset_adjoin
    rw [Finset.coe_union, Finset.coe_image]
    exact Or.inr (Set.mem_image_of_mem _ (Finsupp.mem_support_iff.mpr h))
  · intro r
    rw [Finset.coe_union, Finset.coe_union, Finset.coe_biUnion]
    -- Since all `sᵢ` and numerators of `t r` are in the algebra, it suffices to show that the
    -- image of `x` in `Sᵣ` falls in the `R`-adjoin of `t r`, which is of course true.
    -- Porting note: The following `obtain` fails because Lean wants to know right away what the
    -- placeholders are, so we need to provide a little more guidance
    -- obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ := IsLocalization.exists_smul_mem_of_mem_adjoin
    --   (Submonoid.powers (r : S)) x (t r) (Algebra.adjoin R _) _ _ _
    rw [show ∀ A : Set S, (∃ n, (r : S) ^ n • x ∈ Algebra.adjoin R A) ↔
      (∃ m : (Submonoid.powers (r : S)), (m : S) • x ∈ Algebra.adjoin R A) by
      { exact fun _ => by simp [Submonoid.mem_powers_iff] }]
    refine IsLocalization.exists_smul_mem_of_mem_adjoin
      (Submonoid.powers (r : S)) x (t r) (Algebra.adjoin R _) ?_ ?_ ?_
    · intro x hx
      apply Algebra.subset_adjoin
      exact Or.inl (Or.inl ⟨_, ⟨r, rfl⟩, _, ⟨s.mem_attach r, rfl⟩, hx⟩)
    · rw [Submonoid.powers_eq_closure, Submonoid.closure_le, Set.singleton_subset_iff]
      apply Algebra.subset_adjoin
      exact Or.inl (Or.inr r.2)
    · rw [ht]; trivial

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-
**Algebra.FiniteType.of_span_eq_top_source** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.FiniteType.of_span_eq_top_source (s : Set R) (hs : Ideal.span (s :
 Set R) = ⊤) (h : forall i in s, Algebra.FiniteType (Localization.Away i) (Local
ization.Away i otimes[R] S)) : Algebra.FiniteType R S
参数：s : Set R；hs : Ideal.span (s : Set R) = ⊤；h : forall i in s, Algebra.FiniteTy
pe (Localization.Away i) (Localization.Away i otimes[R] S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.span_eq_top_iff_finite`：span_eq_top_iff_finite (s : Set α) : span 
s = ⊤ ↔ exists s' : Finset α, ↑s' subseteq s ∧ span (s' : Set α) = ⊤
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Algebra.FiniteType.out`：∀ {R : Type uR} {A : Type uA} {inst : CommSemiri
ng R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : Algebra.FiniteType 
R A], ⊤.FG
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.adjoin_attach_biUnion`：adjoin_attach_biUnion [DecidableEq A] {α 
: Type*} {s : Finset α} (f : s -> Finset A) : adjoin R (s.attach.biUnion f : Set
 A) = ⨆ x, adjoin R…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.eq_top_iff`：eq_top_iff {S : Subalgebra R A} : S = ⊤ ↔ forall x :
 A, x in S
· 使用定理 `Submodule.mem_of_span_eq_top_of_smul_pow_mem`：mem_of_span_eq_top_of_smul
_pow_mem (M' : Submodule R M) (s : Set R) (hs : Ideal.span s = ⊤) (x : M) (H : f
orall r : s, exists n : Nat, ((r :…
· 使用定理 `multiple_mem_adjoin_of_mem_localization_adjoin`：multiple_mem_adjoin_of_m
em_localization_adjoin [Algebra R' S] [Algebra R S] [IsScalarTower R R' S] [IsLo
calization M R'] (s : Set S) (x : S)…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsLocalization.Away.instMapRingHomPowersOfCoe`：∀ {A : Type u_5} [inst : 
CommSemiring A] {B : Type u_6} [inst_1 : CommSemiring B] (Bₚ : Type u_8)   [inst
_2 : CommSemiring Bₚ] [inst_3 : Alg…
· 使用定理 `IsLocalization.lift_mem_adjoin_finsetIntegerMultiple`：IsLocalization.lif
t_mem_adjoin_finsetIntegerMultiple [Algebra R S'] [IsScalarTower R S S'] [IsLoca
lization (M.map (algebraMap R S)) S'] (x :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Submonoid.map_powers`：map_powers {N : Type*} {F : Type*} [Monoid N] [Fun
Like F M N] [MonoidHomClass F M N] (f : F) (m : M) : (powers m).map f = powers (
f m)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalization.finsetIntegerMultiple.congr_simp`：∀ {R : Type u_1} [inst 
: CommSemiring R] (M M_1 : Submonoid R) (e_M : M = M_1) {S : Type u_2} [inst_1 :
 CommSemiring S]   [inst_2 : Algebra …
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma Algebra.FiniteType.of_span_eq_top_source (s : Set R) (hs : Ideal.span (s : Set R) = ⊤)
    (h : ∀ i ∈ s, Algebra.FiniteType (Localization.Away i) (Localization.Away i ⊗[R] S)) :
    Algebra.FiniteType R S := by
  obtain ⟨s, h₁, hs⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
  replace h (i : s) := h i.val (h₁ i.property)
  classical
  let := fun r : s => (Localization.awayMap (algebraMap R S) r).toAlgebra
  set f := algebraMap R S
  constructor
  replace H := fun r => (h r).1
  choose s₁ s₂ using H
  let sf := fun x : s => IsLocalization.finsetIntegerMultiple (Submonoid.powers (f x)) (s₁ x)
  use s.attach.biUnion sf
  convert! (Algebra.adjoin_attach_biUnion (R := R) sf).trans _
  rw [eq_top_iff]
  rintro x -
  apply (⨆ x : s, Algebra.adjoin R (sf x : Set S)).toSubmodule.mem_of_span_eq_top_of_smul_pow_mem
    _ hs _ _
  intro r
  obtain ⟨⟨_, n₁, rfl⟩, hn₁⟩ :=
    multiple_mem_adjoin_of_mem_localization_adjoin (Submonoid.powers (r : R))
      (Localization.Away (r : R)) (s₁ r : Set (Localization.Away r.val ⊗[R] S))
      (algebraMap S _ x) (by rw [s₂ r]; trivial)
  rw [Submonoid.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply R S, ← map_mul] at hn₁
  obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ :=
    IsLocalization.lift_mem_adjoin_finsetIntegerMultiple (Submonoid.powers (r : R)) _ (s₁ r) hn₁
  rw [Submonoid.smul_def, ← Algebra.smul_def, smul_smul, ← pow_add] at hn₂
  simp_rw [Submonoid.map_powers] at hn₂
  use n₂ + n₁
  exact le_iSup (fun x : s => Algebra.adjoin R (sf x : Set S)) r hn₂

end Algebra

