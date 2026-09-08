/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Submodule
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Dimension.Subsingleton

/-!
# Lemmas about rank and `finrank` in rings satisfying strong rank condition.

## Main statements

For modules over rings satisfying the rank condition

* `Basis.le_span`:
  the cardinality of a basis is bounded by the cardinality of any spanning set

For modules over rings satisfying the strong rank condition

* `linearIndependent_le_span`:
  For any linearly independent family `v : ι → M`
  and any finite spanning set `w : Set M`,
  the cardinality of `ι` is bounded by the cardinality of `w`.
* `linearIndependent_le_basis`:
  If `b` is a basis for a module `M`,
  and `s` is a linearly independent set,
  then the cardinality of `s` is bounded by the cardinality of `b`.

For modules over rings with invariant basis number
(including all commutative rings and all Noetherian rings)

* `mk_eq_mk_of_basis`: the dimension theorem, any two bases of the same vector space have the same
  cardinality.

## Additional definition

* `Algebra.IsQuadraticExtension`: An extension of rings `R ⊆ S` is quadratic if `S` is a
  free `R`-algebra of rank `2`.

-/

@[expose] public section


noncomputable section

universe u v w w'

variable {R : Type u} {S : Type*} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
variable {ι : Type w} {ι' : Type w'}

open Cardinal Basis Submodule Function Set Module

attribute [local instance] nontrivial_of_invariantBasisNumber

section InvariantBasisNumber

variable [InvariantBasisNumber R]

/-- The dimension theorem: if `v` and `v'` are two bases, their index types
have the same cardinalities. -/
/-
**mk_eq_mk_of_basis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mk_eq_mk_of_basis (v : Basis ι R M) (v' : Basis ι' R M) : Cardinal.lift.{w
'} #ι = Cardinal.lift.{w} #ι'
参数：v : Basis ι R M；v' : Basis ι' R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用引理 `basis_finite_of_finite_spans`：basis_finite_of_finite_spans [Nontrivial R
] {s : Set M} (hs : s.Finite) (hsspan : span R s = ⊤) {ι : Type w} (b : Basis ι 
R M) : Finite ι
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `card_eq_of_linearEquiv`：card_eq_of_linearEquiv {α β : Type*} [Fintype α]
 [Fintype β] (f : (α -> R) ≃ₗ[R] β -> R) : Fintype.card α = Fintype.card β
· 使用定理 `infinite_basis_le_maximal_linearIndependent'`：infinite_basis_le_maximal_
linearIndependent' {ι : Type w} (b : Basis ι R M) [Infinite ι] {κ : Type w'} (v 
: κ -> M) (i : LinearIndependent R…
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Module.Basis.maximal`：maximal [Nontrivial R] (b : Basis ι R M) : b.linea
rIndependent.Maximal
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lift_mk_le'`：lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #
α <= lift.{u} #β ↔ Nonempty (α ↪ β)
· 使用定理 `Infinite.of_injective`：of_injective {α β} [Infinite β] (f : β -> α) (hf 
: Injective f) : Infinite α
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b

--- 原说明 ---
The dimension theorem: if `v` and `v'` are two bases, their index types
have the same cardinalities.
-/
theorem mk_eq_mk_of_basis (v : Basis ι R M) (v' : Basis ι' R M) :
    Cardinal.lift.{w'} #ι = Cardinal.lift.{w} #ι' := by
  have := nontrivial_of_invariantBasisNumber R
  cases fintypeOrInfinite ι
  · -- `v` is a finite basis, so by `basis_finite_of_finite_spans` so is `v'`.
    -- haveI : Finite (range v) := Set.finite_range v
    have := basis_finite_of_finite_spans (Set.finite_range v) v.span_eq v'
    cases nonempty_fintype ι'
    -- We clean up a little:
    rw [Cardinal.mk_fintype, Cardinal.mk_fintype]
    simp only [Cardinal.lift_natCast, Nat.cast_inj]
    -- Now we can use invariant basis number to show they have the same cardinality.
    apply card_eq_of_linearEquiv R
    exact
      (Finsupp.linearEquivFunOnFinite R R ι).symm.trans v.repr.symm ≪≫ₗ v'.repr ≪≫ₗ
        Finsupp.linearEquivFunOnFinite R R ι'
  · -- `v` is an infinite basis,
    -- so by `infinite_basis_le_maximal_linearIndependent`, `v'` is at least as big,
    -- and then applying `infinite_basis_le_maximal_linearIndependent` again
    -- we see they have the same cardinality.
    have w₁ := infinite_basis_le_maximal_linearIndependent' v _ v'.linearIndependent v'.maximal
    rcases Cardinal.lift_mk_le'.mp w₁ with ⟨f⟩
    have : Infinite ι' := Infinite.of_injective f f.2
    have w₂ := infinite_basis_le_maximal_linearIndependent' v' _ v.linearIndependent v.maximal
    exact le_antisymm w₁ w₂

/-- Given two bases indexed by `ι` and `ι'` of an `R`-module, where `R` satisfies the invariant
basis number property, an equiv `ι ≃ ι'`. -/
/-
**Module.Basis.indexEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Module.Basis.indexEquiv (v : Basis ι R M) (v' : Basis ι' R M) : ι ≃ ι'
参数：v : Basis ι R M；v' : Basis ι' R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two bases indexed by `ι` and `ι'` of an `R`-module, where `R` satisfies th
e invariant
basis number property, an equiv `ι ≃ ι'`.
-/
def Module.Basis.indexEquiv (v : Basis ι R M) (v' : Basis ι' R M) : ι ≃ ι' :=
  (Cardinal.lift_mk_eq'.1 <| mk_eq_mk_of_basis v v').some
/-
**mk_eq_mk_of_basis'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mk_eq_mk_of_basis' {ι' : Type w} (v : Basis ι R M) (v' : Basis ι' R M) : #
ι = #ι'
参数：v : Basis ι R M；v' : Basis ι' R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `mk_eq_mk_of_basis`：mk_eq_mk_of_basis (v : Basis ι R M) (v' : Basis ι' R 
M) : Cardinal.lift.{w'} #ι = Cardinal.lift.{w} #ι'
-/
theorem mk_eq_mk_of_basis' {ι' : Type w} (v : Basis ι R M) (v' : Basis ι' R M) : #ι = #ι' :=
  Cardinal.lift_inj.1 <| mk_eq_mk_of_basis v v'

end InvariantBasisNumber

section RankCondition

variable [RankCondition R]

/-- An auxiliary lemma for `Basis.le_span`.

If `R` satisfies the rank condition,
then for any finite basis `b : Basis ι R M`,
and any finite spanning set `w : Set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
/-
**Basis.le_span''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Basis.le_span'' {ι : Type*} [Fintype ι] (b : Basis ι R M) {w : Set M} [Fin
type w] (s : span R w = ⊤) : Fintype.card ι <= Fintype.card w
参数：b : Basis ι R M；s : span R w = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `card_le_of_surjective'`：card_le_of_surjective' [RankCondition R] {α β : 
Type*} [Fintype α] [Fintype β] (f : (α ->₀ R) ->ₗ[R] β ->₀ R) (i : Surjective f)
 : Fintype.c…
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Finsupp.range_linearCombination`：range_linearCombination : LinearMap.ran
ge (linearCombination R v) = span R (range v)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }

--- 原说明 ---
An auxiliary lemma for `Basis.le_span`.

If `R` satisfies the rank condition,
then for any finite basis `b : Basis ι R M`,
and any finite spanning set `w : Set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
theorem Basis.le_span'' {ι : Type*} [Fintype ι] (b : Basis ι R M) {w : Set M} [Fintype w]
    (s : span R w = ⊤) : Fintype.card ι ≤ Fintype.card w := by
  -- We construct a surjective linear map `(w → R) →ₗ[R] (ι → R)`,
  -- by expressing a linear combination in `w` as a linear combination in `ι`.
  fapply card_le_of_surjective' R
  · exact b.repr.toLinearMap.comp (Finsupp.linearCombination R (↑))
  · apply Surjective.comp (g := b.repr.toLinearMap)
    · apply LinearEquiv.surjective
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    simpa using s

/--
Another auxiliary lemma for `Basis.le_span`, which does not require assuming the basis is finite,
but still assumes we have a finite spanning set.
-/
/-
**basis_le_span'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：basis_le_span' {ι : Type*} (b : Basis ι R M) {w : Set M} [Fintype w] (s : 
span R w = ⊤) : #ι <= Fintype.card w
参数：b : Basis ι R M；s : span R w = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用引理 `basis_finite_of_finite_spans`：basis_finite_of_finite_spans [Nontrivial R
] {s : Set M} (hs : s.Finite) (hsspan : span R s = ⊤) {ι : Type w} (b : Basis ι 
R M) : Finite ι
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Basis.le_span''`：Basis.le_span'' {ι : Type*} [Fintype ι] (b : Basis ι R 
M) {w : Set M} [Fintype w] (s : span R w = ⊤) : Fintype.card ι <= Fintype.card w

--- 原说明 ---
Another auxiliary lemma for `Basis.le_span`, which does not require assuming the
 basis is finite,
but still assumes we have a finite spanning set.
-/
theorem basis_le_span' {ι : Type*} (b : Basis ι R M) {w : Set M} [Fintype w] (s : span R w = ⊤) :
    #ι ≤ Fintype.card w := by
  have := nontrivial_of_invariantBasisNumber R
  have := basis_finite_of_finite_spans w.toFinite s b
  cases nonempty_fintype ι
  rw [Cardinal.mk_fintype ι]
  simp only [Nat.cast_le]
  exact Basis.le_span'' b s

-- Note that if `R` satisfies the strong rank condition,
-- this also follows from `linearIndependent_le_span` below.
/-- If `R` satisfies the rank condition,
then the cardinality of any basis is bounded by the cardinality of any spanning set.
-/
/-
**Module.Basis.le_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Basis.le_span {J : Set M} (v : Basis ι R M) (hJ : span R J = ⊤) : #
(range v) <= #J
参数：v : Basis ι R M；hJ : span R J = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Cardinal.mk_range_eq_of_injective`：mk_range_eq_of_injective {α : Type u}
 {β : Type v} {f : α -> β} (hf : Injective f) : lift.{u} #(range f) = lift.{v} #
α
· 使用定理 `Module.Basis.injective`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [
inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b 
: Module.Bas…
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.fintypeCard_eq_ncard`：fintypeCard_eq_ncard [Fintype s] : Fintype.car
d s = s.ncard
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `basis_le_span'`：basis_le_span' {ι : Type*} (b : Basis ι R M) {w : Set M}
 [Fintype w] (s : span R w = ⊤) : #ι <= Fintype.card w
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `trivial`：True
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Finsupp.mem_supported`：mem_supported {s : Set α} (p : α ->₀ M) : p in su
pported M R s ↔ ↑p.support subseteq s
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
If `R` satisfies the rank condition,
then the cardinality of any basis is bounded by the cardinality of any spanning 
set.
-/
theorem Module.Basis.le_span {J : Set M} (v : Basis ι R M) (hJ : span R J = ⊤) :
    #(range v) ≤ #J := by
  have := nontrivial_of_invariantBasisNumber R
  cases fintypeOrInfinite J
  · rw [← Cardinal.lift_le, Cardinal.mk_range_eq_of_injective v.injective, Cardinal.mk_fintype J]
    convert! Cardinal.lift_le.{v}.2 (basis_le_span' v hJ)
    simp
  · let S : J → Set ι := fun j => ↑(v.repr j).support
    let S' : J → Set M := fun j => v '' S j
    have hs : range v ⊆ ⋃ j, S' j := by
      intro b hb
      rcases mem_range.1 hb with ⟨i, hi⟩
      have : span R J ≤ comap v.repr.toLinearMap (Finsupp.supported R R (⋃ j, S j)) :=
        span_le.2 fun j hj x hx => ⟨_, ⟨⟨j, hj⟩, rfl⟩, hx⟩
      rw [hJ] at this
      replace : v.repr (v i) ∈ Finsupp.supported R R (⋃ j, S j) := this trivial
      rw [v.repr_self, Finsupp.mem_supported, Finsupp.support_single _ one_ne_zero] at this
      · subst b
        rcases mem_iUnion.1 (this (Finset.mem_singleton_self _)) with ⟨j, hj⟩
        exact mem_iUnion.2 ⟨j, (mem_image _ _ _).2 ⟨i, hj, rfl⟩⟩
    refine le_of_not_gt fun IJ => ?_
    suffices #(⋃ j, S' j) < #(range v) by exact not_le_of_gt this ⟨Set.embeddingOfSubset _ _ hs⟩
    refine lt_of_le_of_lt (le_trans Cardinal.mk_iUnion_le_sum_mk
      (Cardinal.sum_le_sum _ (fun _ => ℵ₀) ?_)) ?_
    · exact fun j => (Cardinal.lt_aleph0_of_finite _).le
    · simpa

end RankCondition

section StrongRankCondition

variable [StrongRankCondition R]

open Submodule Finsupp

-- An auxiliary lemma for `linearIndependent_le_span'`,
-- with the additional assumption that the linearly independent family is finite.
/-
**linearIndependent_le_span_aux'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_le_span_aux' {ι : Type*} [Fintype ι] (v : ι -> M) (i : L
inearIndependent R v) (w : Set M) [Fintype w] (s : range v <= span R w) : Fintyp
e.card ι <= Fintype.card w
参数：v : ι -> M；i : LinearIndependent R v；w : Set M；s : range v <= span R w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `card_le_of_injective'`：card_le_of_injective' [StrongRankCondition R] {α 
β : Type*} [Fintype α] [Fintype β] (f : (α ->₀ R) ->ₗ[R] β ->₀ R) (i : Injective
 f) : Finty…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.linearCombination_linearCombination`：linearCombination_linearCom
bination {α β : Type*} (A : α -> M) (B : β -> α ->₀ R) (f : β ->₀ R) : linearCom
bination R A (linearCombination R…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Span.finsupp_linearCombination_repr`：Span.finsupp_linearCombination_repr
 {w : Set M} (x : span R w) : Finsupp.linearCombination R ((↑) : w -> M) (Span.r
epr R w x) = x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem linearIndependent_le_span_aux' {ι : Type*} [Fintype ι] (v : ι → M)
    (i : LinearIndependent R v) (w : Set M) [Fintype w] (s : range v ≤ span R w) :
    Fintype.card ι ≤ Fintype.card w := by
  -- We construct an injective linear map `(ι → R) →ₗ[R] (w → R)`,
  -- by thinking of `f : ι → R` as a linear combination of the finite family `v`,
  -- and expressing that (using the axiom of choice) as a linear combination over `w`.
  -- We can do this linearly by constructing the map on a basis.
  fapply card_le_of_injective' R
  · apply Finsupp.linearCombination
    exact fun i => Span.repr R w ⟨v i, s (mem_range_self i)⟩
  · intro f g h
    apply_fun linearCombination R ((↑) : w → M) at h
    simp only [linearCombination_linearCombination,
               Span.finsupp_linearCombination_repr] at h
    exact i h

/-- If `R` satisfies the strong rank condition,
then any linearly independent family `v : ι → M`
contained in the span of some finite `w : Set M`,
is itself finite.
-/
/-
**LinearIndependent.finite_of_le_span_finite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndependent.finite_of_le_span_finite {ι : Type*} (v : ι -> M) (i : L
inearIndependent R v) (w : Set M) [Finite w] (s : range v <= span R w) : Finite 
ι
参数：v : ι -> M；i : LinearIndependent R v；w : Set M；s : range v <= span R w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.finite`：∀ {α : Type u_4} (_inst : Fintype α), Finite α
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.fintypeCard_eq_ncard`：fintypeCard_eq_ncard [Fintype s] : Fintype.car
d s = s.ncard
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `linearIndependent_le_span_aux'`：linearIndependent_le_span_aux' {ι : Type
*} [Fintype ι] (v : ι -> M) (i : LinearIndependent R v) (w : Set M) [Fintype w] 
(s : range v <= span…

--- 原说明 ---
If `R` satisfies the strong rank condition,
then any linearly independent family `v : ι → M`
contained in the span of some finite `w : Set M`,
is itself finite.
-/
lemma LinearIndependent.finite_of_le_span_finite {ι : Type*} (v : ι → M) (i : LinearIndependent R v)
    (w : Set M) [Finite w] (s : range v ≤ span R w) : Finite ι :=
  letI := Fintype.ofFinite w
  Fintype.finite <| fintypeOfFinsetCardLe (Fintype.card w) fun t => by
    let v' := fun x : (t : Set ι) => v x
    have i' : LinearIndependent R v' := i.comp _ Subtype.val_injective
    have s' : range v' ≤ span R w := (range_comp_subset_range _ _).trans s
    simpa using linearIndependent_le_span_aux' v' i' w s'

/-- If `R` satisfies the strong rank condition,
then for any linearly independent family `v : ι → M`
contained in the span of some finite `w : Set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
/-
**linearIndependent_le_span'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_le_span' {ι : Type*} (v : ι -> M) (i : LinearIndependent
 R v) (w : Set M) [Fintype w] (s : range v <= span R w) : #ι <= Fintype.card w
参数：v : ι -> M；i : LinearIndependent R v；w : Set M；s : range v <= span R w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearIndependent.finite_of_le_span_finite`：LinearIndependent.finite_of_
le_span_finite {ι : Type*} (v : ι -> M) (i : LinearIndependent R v) (w : Set M) 
[Finite w] (s : range v <= span …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `linearIndependent_le_span_aux'`：linearIndependent_le_span_aux' {ι : Type
*} [Fintype ι] (v : ι -> M) (i : LinearIndependent R v) (w : Set M) [Fintype w] 
(s : range v <= span…

--- 原说明 ---
If `R` satisfies the strong rank condition,
then for any linearly independent family `v : ι → M`
contained in the span of some finite `w : Set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
theorem linearIndependent_le_span' {ι : Type*} (v : ι → M) (i : LinearIndependent R v) (w : Set M)
    [Fintype w] (s : range v ≤ span R w) : #ι ≤ Fintype.card w := by
  have : Finite ι := i.finite_of_le_span_finite v w s
  let := Fintype.ofFinite ι
  rw [Cardinal.mk_fintype]
  simp only [Nat.cast_le]
  exact linearIndependent_le_span_aux' v i w s

/-- If `R` satisfies the strong rank condition,
then for any linearly independent family `v : ι → M`
and any finite spanning set `w : Set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
/-
**linearIndependent_le_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_le_span {ι : Type*} (v : ι -> M) (i : LinearIndependent 
R v) (w : Set M) [Fintype w] (s : span R w = ⊤) : #ι <= Fintype.card w
参数：v : ι -> M；i : LinearIndependent R v；w : Set M；s : span R w = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `linearIndependent_le_span'`：linearIndependent_le_span' {ι : Type*} (v : 
ι -> M) (i : LinearIndependent R v) (w : Set M) [Fintype w] (s : range v <= span
 R w) : #ι <= Fi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_top`：le_top : a <= ⊤

--- 原说明 ---
If `R` satisfies the strong rank condition,
then for any linearly independent family `v : ι → M`
and any finite spanning set `w : Set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
theorem linearIndependent_le_span {ι : Type*} (v : ι → M) (i : LinearIndependent R v) (w : Set M)
    [Fintype w] (s : span R w = ⊤) : #ι ≤ Fintype.card w := by
  apply linearIndependent_le_span' v i w
  rw [s]
  exact le_top

/-- A version of `linearIndependent_le_span` for `Finset`. -/
/-
**linearIndependent_le_span_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_le_span_finset {ι : Type*} (v : ι -> M) (i : LinearIndep
endent R v) (w : Finset M) (s : span R (w : Set M) = ⊤) : #ι <= w.card
参数：v : ι -> M；i : LinearIndependent R v；w : Finset M；s : span R (w : Set M) = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `linearIndependent_le_span`：linearIndependent_le_span {ι : Type*} (v : ι 
-> M) (i : LinearIndependent R v) (w : Set M) [Fintype w] (s : span R w = ⊤) : #
ι <= Fintype.ca…

--- 原说明 ---
A version of `linearIndependent_le_span` for `Finset`.
-/
theorem linearIndependent_le_span_finset {ι : Type*} (v : ι → M) (i : LinearIndependent R v)
    (w : Finset M) (s : span R (w : Set M) = ⊤) : #ι ≤ w.card := by
  simpa only [Finset.coe_sort_coe, Fintype.card_coe] using linearIndependent_le_span v i w s

/-- An auxiliary lemma for `linearIndependent_le_basis`:
we handle the case where the basis `b` is infinite.
-/
/-
**linearIndependent_le_infinite_basis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_le_infinite_basis {ι : Type w} (b : Basis ι R M) [Infini
te ι] {κ : Type w} (v : κ -> M) (i : LinearIndependent R v) : #κ <= #ι
参数：b : Basis ι R M；v : κ -> M；i : LinearIndependent R v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Cardinal.exists_infinite_fiber'`：exists_infinite_fiber' {β α : Type u} (
f : β -> α) (h : #α < #β) [Infinite α] : exists a : α, Infinite (f ⁻¹' {a})
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_finset_of_infinite`：mk_finset_of_infinite (α : Type u) [Infi
nite α] : #(Finset α) = #α
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `instInfiniteFinset`：∀ {α : Type u_1} [Infinite α], Infinite (Finset α)
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用引理 `LinearIndependent.finite_of_le_span_finite`：LinearIndependent.finite_of_
le_span_finite {ι : Type*} (v : ι -> M) (i : LinearIndependent R v) (w : Set M) 
[Finite w] (s : range v <= span …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Module.Basis.mem_span_repr_support`：mem_span_repr_support (m : M) : m in
 span R (b '' (b.repr m).support)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Infinite.false`：∀ {α : Sort u_1} [Finite α], Infinite α → False

--- 原说明 ---
An auxiliary lemma for `linearIndependent_le_basis`:
we handle the case where the basis `b` is infinite.
-/
theorem linearIndependent_le_infinite_basis {ι : Type w} (b : Basis ι R M) [Infinite ι] {κ : Type w}
    (v : κ → M) (i : LinearIndependent R v) : #κ ≤ #ι := by
  classical
  by_contra h
  rw [not_le, ← Cardinal.mk_finset_of_infinite ι] at h
  let Φ := fun k : κ => (b.repr (v k)).support
  obtain ⟨s, w : Infinite ↑(Φ ⁻¹' {s})⟩ := Cardinal.exists_infinite_fiber' Φ h
  let v' := fun k : Φ ⁻¹' {s} => v k
  have i' : LinearIndependent R v' := i.comp _ Subtype.val_injective
  have w' : Finite (Φ ⁻¹' {s}) := by
    apply i'.finite_of_le_span_finite v' (s.image b)
    rintro m ⟨⟨p, ⟨rfl⟩⟩, rfl⟩
    simp only [SetLike.mem_coe, Finset.coe_image]
    apply Basis.mem_span_repr_support
  exact w.false

/-- Over any ring `R` satisfying the strong rank condition,
if `b` is a basis for a module `M`,
and `s` is a linearly independent set,
then the cardinality of `s` is bounded by the cardinality of `b`.
-/
/-
**linearIndependent_le_basis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_le_basis {ι : Type w} (b : Basis ι R M) {κ : Type w} (v 
: κ -> M) (i : LinearIndependent R v) : #κ <= #ι
参数：b : Basis ι R M；v : κ -> M；i : LinearIndependent R v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_strongRankCondition`：∀ (R : Type u) [inst : Semiring R]
 [StrongRankCondition R], RankCondition R
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `Module.Basis.injective`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [
inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b 
: Module.Bas…
· 使用定理 `linearIndependent_le_span`：linearIndependent_le_span {ι : Type*} (v : ι 
-> M) (i : LinearIndependent R v) (w : Set M) [Fintype w] (s : span R w = ⊤) : #
ι <= Fintype.ca…
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `linearIndependent_le_infinite_basis`：linearIndependent_le_infinite_basis
 {ι : Type w} (b : Basis ι R M) [Infinite ι] {κ : Type w} (v : κ -> M) (i : Line
arIndependent R v) : #κ <…

--- 原说明 ---
Over any ring `R` satisfying the strong rank condition,
if `b` is a basis for a module `M`,
and `s` is a linearly independent set,
then the cardinality of `s` is bounded by the cardinality of `b`.
-/
theorem linearIndependent_le_basis {ι : Type w} (b : Basis ι R M) {κ : Type w} (v : κ → M)
    (i : LinearIndependent R v) : #κ ≤ #ι := by
  classical
  -- We split into cases depending on whether `ι` is infinite.
  cases fintypeOrInfinite ι
  · rw [Cardinal.mk_fintype ι] -- When `ι` is finite, we have `linearIndependent_le_span`,
    have : Nontrivial R := nontrivial_of_invariantBasisNumber R
    rw [Fintype.card_congr (Equiv.ofInjective b b.injective)]
    exact linearIndependent_le_span v i (range b) b.span_eq
  · -- and otherwise we have `linearIndependent_le_infinite_basis`.
    exact linearIndependent_le_infinite_basis b v i

/-- `StrongRankCondition` implies that if there is an injective linear map `(α →₀ R) →ₗ[R] β →₀ R`,
then the cardinal of `α` is smaller than or equal to the cardinal of `β`.
-/
/-
**card_le_of_injective''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：card_le_of_injective'' {α : Type v} {β : Type v} (f : (α ->₀ R) ->ₗ[R] β -
>₀ R) (i : Injective f) : #α <= #β
参数：f : (α ->₀ R) ->ₗ[R] β ->₀ R；i : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `linearIndependent_le_basis`：linearIndependent_le_basis {ι : Type w} (b :
 Basis ι R M) {κ : Type w} (v : κ -> M) (i : LinearIndependent R v) : #κ <= #ι
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIndependent.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v
 : ι → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modu
le R M], Lin…
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`StrongRankCondition` implies that if there is an injective linear map `(α →₀ R)
 →ₗ[R] β →₀ R`,
then the cardinal of `α` is smaller than or equal to the cardinal of `β`.
-/
theorem card_le_of_injective'' {α : Type v} {β : Type v} (f : (α →₀ R) →ₗ[R] β →₀ R)
    (i : Injective f) : #α ≤ #β := by
  let b : Basis β R (β →₀ R) := ⟨1⟩
  apply linearIndependent_le_basis b (fun (i : α) ↦ f (Finsupp.single i 1))
  rw [LinearIndependent]
  have : (linearCombination R fun i ↦ f (Finsupp.single i 1)) = f := by ext a b; simp
  exact this.symm ▸ i

/-- If `R` satisfies the strong rank condition, then for any linearly independent family `v : ι → M`
and spanning set `w : Set M`, the cardinality of `ι` is bounded by the cardinality of `w`.
-/
/-
**linearIndependent_le_span''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_le_span'' {ι : Type v} {v : ι -> M} (i : LinearIndepende
nt R v) (w : Set M) (s : span R w = ⊤) : #ι <= #w
参数：i : LinearIndependent R v；w : Set M；s : span R w = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `card_le_of_injective''`：card_le_of_injective'' {α : Type v} {β : Type v}
 (f : (α ->₀ R) ->ₗ[R] β ->₀ R) (i : Injective f) : #α <= #β
· 使用定理 `trivial`：True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.linearCombination_linearCombination`：linearCombination_linearCom
bination {α β : Type*} (A : α -> M) (B : β -> α ->₀ R) (f : β ->₀ R) : linearCom
bination R A (linearCombination R…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Span.finsupp_linearCombination_repr`：Span.finsupp_linearCombination_repr
 {w : Set M} (x : span R w) : Finsupp.linearCombination R ((↑) : w -> M) (Span.r
epr R w x) = x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
If `R` satisfies the strong rank condition, then for any linearly independent fa
mily `v : ι → M`
and spanning set `w : Set M`, the cardinality of `ι` is bounded by the cardinali
ty of `w`.
-/
theorem linearIndependent_le_span'' {ι : Type v} {v : ι → M} (i : LinearIndependent R v) (w : Set M)
    (s : span R w = ⊤) : #ι ≤ #w := by
  fapply card_le_of_injective'' (R := R)
  · apply Finsupp.linearCombination
    exact fun i ↦ Span.repr R w ⟨v i, s ▸ trivial⟩
  · intro f g h
    apply_fun linearCombination R ((↑) : w → M) at h
    simp only [linearCombination_linearCombination,
               Span.finsupp_linearCombination_repr] at h
    exact i h

/-- Let `R` satisfy the strong rank condition. If `m` elements of a free rank `n` `R`-module are
linearly independent, then `m ≤ n`. -/
/-
**Basis.card_le_card_of_linearIndependent_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Basis.card_le_card_of_linearIndependent_aux {R : Type*} [Semiring R] [Stro
ngRankCondition R] (n : Nat) {m : Nat} (v : Fin m -> Fin n -> R) : LinearIndepen
dent R v -> m <= n
参数：n : Nat；v : Fin m -> Fin n -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `linearIndependent_le_basis`：linearIndependent_le_basis {ι : Type w} (b :
 Basis ι R M) {κ : Type w} (v : κ -> M) (i : LinearIndependent R v) : #κ <= #ι
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
Let `R` satisfy the strong rank condition. If `m` elements of a free rank `n` `R
`-module are
linearly independent, then `m ≤ n`.
-/
theorem Basis.card_le_card_of_linearIndependent_aux {R : Type*} [Semiring R] [StrongRankCondition R]
    (n : ℕ) {m : ℕ} (v : Fin m → Fin n → R) : LinearIndependent R v → m ≤ n := fun h => by
  simpa using linearIndependent_le_basis (Pi.basisFun R (Fin n)) v h

-- When the basis is not infinite this need not be true!
/-- Over any ring `R` satisfying the strong rank condition,
if `b` is an infinite basis for a module `M`,
then every maximal linearly independent set has the same cardinality as `b`.

This proof (along with some of the lemmas above) comes from
[Les familles libres maximales d'un module ont-elles le meme cardinal?][lazarus1973]
-/
/-
**maximal_linearIndependent_eq_infinite_basis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：maximal_linearIndependent_eq_infinite_basis {ι : Type w} (b : Basis ι R M)
 [Infinite ι] {κ : Type w} (v : κ -> M) (i : LinearIndependent R v) (m : i.Maxim
al) : #κ = #ι
参数：b : Basis ι R M；v : κ -> M；i : LinearIndependent R v；m : i.Maximal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `linearIndependent_le_basis`：linearIndependent_le_basis {ι : Type w} (b :
 Basis ι R M) {κ : Type w} (v : κ -> M) (i : LinearIndependent R v) : #κ <= #ι
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_strongRankCondition`：∀ (R : Type u) [inst : Semiring R]
 [StrongRankCondition R], RankCondition R
· 使用定理 `infinite_basis_le_maximal_linearIndependent`：infinite_basis_le_maximal_l
inearIndependent {ι : Type w} (b : Basis ι R M) [Infinite ι] {κ : Type w} (v : κ
 -> M) (i : LinearIndependent R v…

--- 原说明 ---
Over any ring `R` satisfying the strong rank condition,
if `b` is an infinite basis for a module `M`,
then every maximal linearly independent set has the same cardinality as `b`.

This proof (along with some of the lemmas above) comes from
[Les familles libres maximales d'un module ont-elles le meme cardinal?][lazarus1
973]
-/
theorem maximal_linearIndependent_eq_infinite_basis {ι : Type w} (b : Basis ι R M) [Infinite ι]
    {κ : Type w} (v : κ → M) (i : LinearIndependent R v) (m : i.Maximal) : #κ = #ι := by
  apply le_antisymm
  · exact linearIndependent_le_basis b v i
  · have : Nontrivial R := nontrivial_of_invariantBasisNumber R
    exact infinite_basis_le_maximal_linearIndependent b v i m
/-
**Module.Basis.mk_eq_rank''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Basis.mk_eq_rank'' {ι : Type v} (v : Basis ι R M) : #ι = Module.ran
k R M
参数：v : Basis ι R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_strongRankCondition`：∀ (R : Type u) [inst : Semiring R]
 [StrongRankCondition R], RankCondition R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.rank_def`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.rank R M = ⨆ ι, C
ardin…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LinearIndepOn.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v : ι
 → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] (s :…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.reindexRange_apply`：reindexRange_apply (x : range b) : b.re
indexRange x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Cardinal.mk_range_eq`：mk_range_eq (f : α -> β) (h : Injective f) : #(ran
ge f) = #α
· 使用定理 `Module.Basis.injective`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [
inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b 
: Module.Bas…
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `linearIndependent_le_basis`：linearIndependent_le_basis {ι : Type w} (b :
 Basis ι R M) {κ : Type w} (v : κ -> M) (i : LinearIndependent R v) : #κ <= #ι
-/
theorem Module.Basis.mk_eq_rank'' {ι : Type v} (v : Basis ι R M) : #ι = Module.rank R M := by
  have := nontrivial_of_invariantBasisNumber R
  rw [Module.rank_def]
  apply le_antisymm
  · trans
    swap
    · apply le_ciSup Cardinal.bddAbove_of_small
      exact
        ⟨Set.range v, by
          rw [LinearIndepOn]
          convert! v.reindexRange.linearIndependent
          simp⟩
    · exact (Cardinal.mk_range_eq v v.injective).ge
  · apply ciSup_le'
    rintro ⟨s, li⟩
    apply linearIndependent_le_basis v _ li
/-
**Module.Basis.mk_range_eq_rank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Basis.mk_range_eq_rank (v : Basis ι R M) : #(range v) = Module.rank
 R M
参数：v : Basis ι R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
-/
theorem Module.Basis.mk_range_eq_rank (v : Basis ι R M) : #(range v) = Module.rank R M :=
  v.reindexRange.mk_eq_rank''

/-- If a vector space has a finite basis, then its dimension (seen as a cardinal) is equal to the
cardinality of the basis. -/
/-
**rank_eq_card_basis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_eq_card_basis {ι : Type w} [Fintype ι] (h : Basis ι R M) : Module.ran
k R M = Fintype.card ι
参数：h : Basis ι R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_strongRankCondition`：∀ (R : Type u) [inst : Semiring R]
 [StrongRankCondition R], RankCondition R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.mk_range_eq_rank`：Module.Basis.mk_range_eq_rank (v : Basis 
ι R M) : #(range v) = Module.rank R M
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Set.card_range_of_injective`：card_range_of_injective [Fintype α] {f : α 
-> β} (hf : Injective f) [Fintype (range f)] : Fintype.card (range f) = Fintype.
card α
· 使用定理 `Module.Basis.injective`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [
inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b 
: Module.Bas…

--- 原说明 ---
If a vector space has a finite basis, then its dimension (seen as a cardinal) is
 equal to the
cardinality of the basis.
-/
theorem rank_eq_card_basis {ι : Type w} [Fintype ι] (h : Basis ι R M) :
    Module.rank R M = Fintype.card ι := by
  classical
  have := nontrivial_of_invariantBasisNumber R
  rw [← h.mk_range_eq_rank, Cardinal.mk_fintype, Set.card_range_of_injective h.injective]

namespace Module.Basis

/-
**Module.Basis.card_le_card_of_linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 `Modu
le.Basis`。
形式化陈述：card_le_card_of_linearIndependent {ι : Type*} [Fintype ι] (b : Basis ι R M
) {ι' : Type*} [Fintype ι'] {v : ι' -> M} (hv : LinearIndependent R v) : Fintype
.card ι' <= Fintype.card ι
参数：b : Basis ι R M；hv : LinearIndependent R v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `rank_eq_card_basis`：rank_eq_card_basis {ι : Type w} [Fintype ι] (h : Bas
is ι R M) : Module.rank R M = Fintype.card ι
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `LinearIndependent.cardinal_lift_le_rank`：cardinal_lift_le_rank {ι : Type
 w} {v : ι -> M} (hv : LinearIndependent R v) : Cardinal.lift.{v} #ι <= Cardinal
.lift.{w} (Module.rank R M)
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_strongRankCondition`：∀ (R : Type u) [inst : Semiring R]
 [StrongRankCondition R], RankCondition R
-/
theorem card_le_card_of_linearIndependent {ι : Type*} [Fintype ι] (b : Basis ι R M)
    {ι' : Type*} [Fintype ι'] {v : ι' → M} (hv : LinearIndependent R v) :
    Fintype.card ι' ≤ Fintype.card ι := by
  simpa [rank_eq_card_basis b, Cardinal.mk_fintype] using hv.cardinal_lift_le_rank
/-
**Module.Basis.card_le_card_of_submodule** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis
`。
形式化陈述：card_le_card_of_submodule (N : Submodule R M) [Fintype ι] (b : Basis ι R M
) [Fintype ι'] (b' : Basis ι' R N) : Fintype.card ι' <= Fintype.card ι
参数：N : Submodule R M；b : Basis ι R M；b' : Basis ι' R N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.card_le_card_of_linearIndependent`：card_le_card_of_linearIn
dependent {ι : Type*} [Fintype ι] (b : Basis ι R M) {ι' : Type*} [Fintype ι'] {v
 : ι' -> M} (hv : LinearIndependent …
· 使用定理 `LinearIndependent.map_injOn`：LinearIndependent.map_injOn (hv : LinearInd
ependent R v) (f : M ->ₗ[R] M') (hf_inj : Set.InjOn f (span R (Set.range v))) : 
LinearIndependent…
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
-/
theorem card_le_card_of_submodule (N : Submodule R M) [Fintype ι] (b : Basis ι R M)
    [Fintype ι'] (b' : Basis ι' R N) : Fintype.card ι' ≤ Fintype.card ι :=
  b.card_le_card_of_linearIndependent
    (b'.linearIndependent.map_injOn N.subtype N.injective_subtype.injOn)
/-
**Module.Basis.card_le_card_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：card_le_card_of_le {N O : Submodule R M} (hNO : N <= O) [Fintype ι] (b : B
asis ι R O) [Fintype ι'] (b' : Basis ι' R N) : Fintype.card ι' <= Fintype.card ι
参数：hNO : N <= O；b : Basis ι R O；b' : Basis ι' R N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.card_le_card_of_linearIndependent`：card_le_card_of_linearIn
dependent {ι : Type*} [Fintype ι] (b : Basis ι R M) {ι' : Type*} [Fintype ι'] {v
 : ι' -> M} (hv : LinearIndependent …
· 使用定理 `LinearIndependent.map_injOn`：LinearIndependent.map_injOn (hv : LinearInd
ependent R v) (f : M ->ₗ[R] M') (hf_inj : Set.InjOn f (span R (Set.range v))) : 
LinearIndependent…
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Submodule.inclusion_injective`：inclusion_injective (h : p <= p') : Funct
ion.Injective (inclusion h)
-/
theorem card_le_card_of_le {N O : Submodule R M} (hNO : N ≤ O) [Fintype ι]
    (b : Basis ι R O) [Fintype ι'] (b' : Basis ι' R N) : Fintype.card ι' ≤ Fintype.card ι :=
  b.card_le_card_of_linearIndependent
    (b'.linearIndependent.map_injOn (inclusion hNO) (N.inclusion_injective _).injOn)
/-
**Module.Basis.mk_eq_rank** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：mk_eq_rank (v : Basis ι R M) : Cardinal.lift.{v} #ι = Cardinal.lift.{w} (M
odule.rank R M)
参数：v : Basis ι R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_strongRankCondition`：∀ (R : Type u) [inst : Semiring R]
 [StrongRankCondition R], RankCondition R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.mk_range_eq_rank`：Module.Basis.mk_range_eq_rank (v : Basis 
ι R M) : #(range v) = Module.rank R M
· 使用定理 `Cardinal.mk_range_eq_of_injective`：mk_range_eq_of_injective {α : Type u}
 {β : Type v} {f : α -> β} (hf : Injective f) : lift.{u} #(range f) = lift.{v} #
α
· 使用定理 `Module.Basis.injective`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [
inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b 
: Module.Bas…
-/
theorem mk_eq_rank (v : Basis ι R M) :
    Cardinal.lift.{v} #ι = Cardinal.lift.{w} (Module.rank R M) := by
  have := nontrivial_of_invariantBasisNumber R
  rw [← v.mk_range_eq_rank, Cardinal.mk_range_eq_of_injective v.injective]
/-
**Module.Basis.mk_eq_rank'.** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_eq_rank'.{m} (v : Basis ι R M) :
    Cardinal.lift.{max v m} #ι = Cardinal.lift.{max w m} (Module.rank R M) :=
  Cardinal.lift_umax_eq.{w, v, m}.mpr v.mk_eq_rank

end Module.Basis

/-
**rank_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_span {v : ι -> M} (hv : LinearIndependent R v) : Module.rank R ↑(span
 R (range v)) = #(range v)
参数：hv : LinearIndependent R v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_strongRankCondition`：∀ (R : Type u) [inst : Semiring R]
 [StrongRankCondition R], RankCondition R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `Module.Basis.mk_eq_rank`：mk_eq_rank (v : Basis ι R M) : Cardinal.lift.{v
} #ι = Cardinal.lift.{w} (Module.rank R M)
· 使用定理 `Cardinal.mk_range_eq_of_injective`：mk_range_eq_of_injective {α : Type u}
 {β : Type v} {f : α -> β} (hf : Injective f) : lift.{u} #(range f) = lift.{v} #
α
· 使用定理 `LinearIndependent.injective`：LinearIndependent.injective [Nontrivial R] 
(hv : LinearIndependent R v) : Injective v
-/
theorem rank_span {v : ι → M} (hv : LinearIndependent R v) :
    Module.rank R ↑(span R (range v)) = #(range v) := by
  have := nontrivial_of_invariantBasisNumber R
  rw [← Cardinal.lift_inj, ← (Basis.span hv).mk_eq_rank,
    Cardinal.mk_range_eq_of_injective (@LinearIndependent.injective ι R M v _ _ _ _ hv)]
/-
**rank_span_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_span_set {s : Set M} (hs : LinearIndepOn R id s) : Module.rank R ↑(sp
an R s) = #s
参数：hs : LinearIndepOn R id s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ofPred_mem_eq`：∀ {α : Type u} {s : Set α}, {x | x ∈ s} = s
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `rank_span`：rank_span {v : ι -> M} (hv : LinearIndependent R v) : Module.
rank R ↑(span R (range v)) = #(range v)
-/
theorem rank_span_set {s : Set M} (hs : LinearIndepOn R id s) : Module.rank R ↑(span R s) = #s := by
  rw [← @ofPred_mem_eq _ s, ← Subtype.range_coe_subtype]
  exact rank_span hs
/-
**toENat_rank_span_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toENat_rank_span_set {v : ι -> M} {s : Set ι} (hs : LinearIndepOn R v s) :
 (Module.rank R <| span R <| v '' s).toENat = s.encard
参数：hs : LinearIndepOn R v s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.InjOn.encard_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f :
 α → β}, Set.InjOn f s → (f '' s).encard = s.encard
· 使用定理 `LinearIndepOn.injOn`：LinearIndepOn.injOn [Nontrivial R] (hv : LinearInde
pOn R v s) : InjOn v s
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_strongRankCondition`：∀ (R : Type u) [inst : Semiring R]
 [StrongRankCondition R], RankCondition R
· 使用定理 `Set.toENat_cardinalMk`：∀ {α : Type u_1} (s : Set α), Cardinal.toENat (Ca
rdinal.mk ↑s) = s.encard
· 使用定理 `rank_span`：rank_span {v : ι -> M} (hv : LinearIndependent R v) : Module.
rank R ↑(span R (range v)) = #(range v)
· 使用定理 `LinearIndepOn.linearIndependent`：LinearIndepOn.linearIndependent {s : Se
t ι} (h : LinearIndepOn R v s) : LinearIndependent R (fun x : s => v x)
-/
theorem toENat_rank_span_set {v : ι → M} {s : Set ι} (hs : LinearIndepOn R v s) :
    (Module.rank R <| span R <| v '' s).toENat = s.encard := by
  rw [image_eq_range, ← hs.injOn.encard_image, ← toENat_cardinalMk, image_eq_range,
    ← rank_span hs.linearIndependent]

/-- An induction (and recursion) principle for proving results about all submodules of a fixed
finite free module `M`. A property is true for all submodules of `M` if it satisfies the following
"inductive step": the property is true for a submodule `N` if it's true for all submodules `N'`
of `N` with the property that there exists `0 ≠ x ∈ N` such that the sum `N' + Rx` is direct. -/
/-
**Submodule.inductionOnRank** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.inductionOnRank {R M} [Ring R] [StrongRankCondition R] [AddCommG
roup M] [Module R M] [IsDomain R] [Finite ι] (b : Basis ι R M) (P : Submodule R 
M -> Sort*) (ih : forall N : Submodule R M, (forall N' <= N, forall x in N, (for
all (c : R), forall y in N', c • x + y = (0 : M) -> c = 0) -> P N') -> P N) (N :
 Submodule R M) : P N
参数：b : Basis ι R M；P : Submodule R M -> Sort*；ih : forall N : Submodule R M, (fo
rall N' <= N, forall x in N, (forall (c : R), forall y in N', c • x + y = (0 : M
) -> c = 0) -> P N') -> P N；N : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An induction (and recursion) principle for proving results about all submodules 
of a fixed
finite free module `M`. A property is true for all submodules of `M` if it satis
fies the following
"inductive step": the property is true for a submodule `N` if it's true for all 
submodules `N'`
of `N` with the property that there exists `0 ≠ x ∈ N` such that the sum `N' + R
x` is direct.
-/
def Submodule.inductionOnRank {R M} [Ring R] [StrongRankCondition R] [AddCommGroup M] [Module R M]
    [IsDomain R] [Finite ι] (b : Basis ι R M) (P : Submodule R M → Sort*)
    (ih : ∀ N : Submodule R M,
      (∀ N' ≤ N, ∀ x ∈ N, (∀ (c : R), ∀ y ∈ N', c • x + y = (0 : M) → c = 0) → P N') → P N)
    (N : Submodule R M) : P N :=
  letI := Fintype.ofFinite ι
  Submodule.inductionOnRankAux b P ih (Fintype.card ι) N fun hs hli => by
    simpa using b.card_le_card_of_linearIndependent hli

/-- If `S` a module-finite free `R`-algebra, then the `R`-rank of a nonzero `R`-free
ideal `I` of `S` is the same as the rank of `S`. -/
/-
**Ideal.rank_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.rank_eq {R S : Type*} [CommRing R] [StrongRankCondition R] [Ring S] 
[IsDomain S] [Algebra R S] {n m : Type*} [Fintype n] [Fintype m] (b : Basis n R 
S) {I : Ideal S} (hI : I != ⊥) (c : Basis m R I) : Fintype.card m = Fintype.card
 n
参数：b : Basis n R S；hI : I != ⊥；c : Basis m R I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.nonzero_mem_of_bot_lt`：nonzero_mem_of_bot_lt {p : Submodule R 
M} (bot_lt : ⊥ < p) : exists a : p, a != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.linearIndependent_iff`：Fintype.linearIndependent_iff [Fintype ι]
 : LinearIndependent R v ↔ forall g : ι -> R, ∑ i, g i • v i = 0 -> forall i, g 
i = 0
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Ideal.instIsTorsionFreeSubtypeMemSubmodule`：∀ {R : Type u} [inst : Semir
ing R] {S : Type u_1} {A : Type u_2} [inst_1 : Semiring S] [inst_2 : SMul R S]  
 [inst_3 : AddCommMonoid A] [ins…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `NoZeroDivisors.toNoZeroSMulDivisors`：∀ {R : Type u_1} [inst : Zero R] [i
nst_1 : Mul R] [NoZeroDivisors R], NoZeroSMulDivisors R R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Module.Basis.card_le_card_of_linearIndependent`：card_le_card_of_linearIn
dependent {ι : Type*} [Fintype ι] (b : Basis ι R M) {ι' : Type*} [Fintype ι'] {v
 : ι' -> M} (hv : LinearIndependent …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `LinearIndependent.map'`：LinearIndependent.map' (hv : LinearIndependent R
 v) (f : M ->ₗ[R] M') (hf_inj : LinearMap.ker f = ⊥) : LinearIndependent R (f ∘ 
v)
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))

--- 原说明 ---
If `S` a module-finite free `R`-algebra, then the `R`-rank of a nonzero `R`-free
ideal `I` of `S` is the same as the rank of `S`.
-/
theorem Ideal.rank_eq {R S : Type*} [CommRing R] [StrongRankCondition R] [Ring S] [IsDomain S]
    [Algebra R S] {n m : Type*} [Fintype n] [Fintype m] (b : Basis n R S) {I : Ideal S}
    (hI : I ≠ ⊥) (c : Basis m R I) : Fintype.card m = Fintype.card n := by
  obtain ⟨a, ha⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hI)
  have : LinearIndependent R fun i => b i • a := by
    have hb := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hb ⊢
    intro g hg
    apply hb g
    simp only [← smul_assoc, ← Finset.sum_smul, smul_eq_zero] at hg
    exact hg.resolve_right ha
  exact le_antisymm
    (b.card_le_card_of_linearIndependent (c.linearIndependent.map' (Submodule.subtype I)
      ((LinearMap.ker_eq_bot (f := (Submodule.subtype I : I →ₗ[R] S))).mpr Subtype.coe_injective)))
    (c.card_le_card_of_linearIndependent this)

namespace Module

omit [StrongRankCondition R] in
/-
**Module.rank_pos_of_free** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：rank_pos_of_free [Module.Free R M] [Nontrivial M] : 0 < Module.rank R M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.nontrivial`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZer
o R] [Nontrivial M] [inst_2 : Zero M] [MulActionWithZero R M],   Nontrivial R
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `pos_of_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1
 : Zero α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Cardinal.mk_ne_zero`：mk_ne_zero (α : Type u) [Nonempty α] : #α != 0
· 使用定理 `Module.Free.instNonemptyChooseBasisIndexOfNontrivial`：∀ (R : Type u) (M 
: Type v) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module
 R M]   [inst_3 : Module.Free R M] [Nontri…
· 使用定理 `LinearIndependent.cardinal_le_rank`：cardinal_le_rank {ι : Type v} {v : ι
 -> M} (hv : LinearIndependent R v) : #ι <= Module.rank R M
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
-/
theorem rank_pos_of_free [Module.Free R M] [Nontrivial M] :
    0 < Module.rank R M :=
  have := Module.nontrivial R M
  (pos_of_ne_zero <| Cardinal.mk_ne_zero _).trans_le
    (Free.chooseBasis R M).linearIndependent.cardinal_le_rank
/-
**Module.rank_pos_iff_of_free** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：rank_pos_iff_of_free [Module.Free R M] : 0 < Module.rank R M ↔ Nontrivial 
M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `not_subsingleton_iff_nontrivial`：not_subsingleton_iff_nontrivial : ¬Subs
ingleton α ↔ Nontrivial α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `rank_subsingleton'`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] 
[inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial R] [Subsin
gleton M…
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_strongRankCondition`：∀ (R : Type u) [inst : Semiring R]
 [StrongRankCondition R], RankCondition R
· 使用定理 `Module.rank_pos_of_free`：rank_pos_of_free [Module.Free R M] [Nontrivial 
M] : 0 < Module.rank R M
-/
theorem rank_pos_iff_of_free [Module.Free R M] :
    0 < Module.rank R M ↔ Nontrivial M := by
  refine ⟨fun h ↦ ?_, fun _ ↦ rank_pos_of_free⟩
  rw [← not_subsingleton_iff_nontrivial]
  intro h'
  simp only [rank_subsingleton', lt_self_iff_false] at h
/-
**Module.rank_zero_iff_of_free** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：rank_zero_iff_of_free [Module.Free R M] : Module.rank R M = 0 ↔ Subsinglet
on M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_nontrivial_iff_subsingleton`：not_nontrivial_iff_subsingleton : ¬Nont
rivial α ↔ Subsingleton α
· 使用定理 `iff_not_comm`：iff_not_comm : (a ↔ ¬b) ↔ (b ↔ ¬a)
· 使用定理 `Module.rank_pos_iff_of_free`：rank_pos_iff_of_free [Module.Free R M] : 0 
< Module.rank R M ↔ Nontrivial M
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rank_zero_iff_of_free [Module.Free R M] :
    Module.rank R M = 0 ↔ Subsingleton M := by
  rw [← not_nontrivial_iff_subsingleton, iff_not_comm,
    ← Module.rank_pos_iff_of_free (R := R), pos_iff_ne_zero]
/-
**Module.finrank_eq_nat_card_basis** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finrank_eq_nat_card_basis (h : Basis ι R M) : finrank R M = Nat.card ι
参数：h : Basis ι R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card.eq_1`：∀ (α : Type u_3), Nat.card α = Cardinal.toNat (Cardinal.m
k α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `Module.Basis.mk_eq_rank`：mk_eq_rank (v : Basis ι R M) : Cardinal.lift.{v
} #ι = Cardinal.lift.{w} (Module.rank R M)
· 使用定理 `Module.finrank.eq_1`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.finrank R M =
 Cardinal…
-/
theorem finrank_eq_nat_card_basis (h : Basis ι R M) :
    finrank R M = Nat.card ι := by
  rw [Nat.card, ← toNat_lift.{v}, h.mk_eq_rank, toNat_lift, finrank]

/-- If a vector space (or module) has a finite basis, then its dimension (or rank) is equal to the
cardinality of the basis. -/
/-
**Module.finrank_eq_card_basis** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finrank_eq_card_basis {ι : Type w} [Fintype ι] (h : Basis ι R M) : finrank
 R M = Fintype.card ι
参数：h : Basis ι R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_eq_of_rank_eq`：finrank_eq_of_rank_eq {n : Nat} (h : Modul
e.rank R M = ↑n) : finrank R M = n
· 使用定理 `rank_eq_card_basis`：rank_eq_card_basis {ι : Type w} [Fintype ι] (h : Bas
is ι R M) : Module.rank R M = Fintype.card ι

--- 原说明 ---
If a vector space (or module) has a finite basis, then its dimension (or rank) i
s equal to the
cardinality of the basis.
-/
theorem finrank_eq_card_basis {ι : Type w} [Fintype ι] (h : Basis ι R M) :
    finrank R M = Fintype.card ι :=
  finrank_eq_of_rank_eq (rank_eq_card_basis h)

/-- If a free module is of finite rank, then the cardinality of any basis is equal to its
`finrank`. -/
/-
**Module.mk_finrank_eq_card_basis** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：mk_finrank_eq_card_basis [Module.Finite R M] {ι : Type w} (h : Basis ι R M
) : (finrank R M : Cardinal.{w}) = #ι
参数：h : Basis ι R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用引理 `Module.Finite.finite_basis`：finite_basis [Nontrivial R] {ι} [Module.Fini
te R M] (b : Basis ι R M) : _root_.Finite ι
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_strongRankCondition`：∀ (R : Type u) [inst : Semiring R]
 [StrongRankCondition R], RankCondition R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι

--- 原说明 ---
If a free module is of finite rank, then the cardinality of any basis is equal t
o its
`finrank`.
-/
theorem mk_finrank_eq_card_basis [Module.Finite R M] {ι : Type w} (h : Basis ι R M) :
    (finrank R M : Cardinal.{w}) = #ι := by
  cases @nonempty_fintype _ (Module.Finite.finite_basis h)
  rw [Cardinal.mk_fintype, finrank_eq_card_basis h]

/-- If a vector space (or module) has a finite basis, then its dimension (or rank) is equal to the
cardinality of the basis. This lemma uses a `Finset` instead of indexed types. -/
/-
**Module.finrank_eq_card_finset_basis** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finrank_eq_card_finset_basis {ι : Type w} {b : Finset ι} (h : Basis b R M)
 : finrank R M = Finset.card b
参数：h : Basis b R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s

--- 原说明 ---
If a vector space (or module) has a finite basis, then its dimension (or rank) i
s equal to the
cardinality of the basis. This lemma uses a `Finset` instead of indexed types.
-/
theorem finrank_eq_card_finset_basis {ι : Type w} {b : Finset ι} (h : Basis b R M) :
    finrank R M = Finset.card b := by rw [finrank_eq_card_basis h, Fintype.card_coe]

variable (R)

@[simp]
/-
**Module.rank_self** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：rank_self : Module.rank R R = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `Module.Basis.mk_eq_rank`：mk_eq_rank (v : Basis ι R M) : Cardinal.lift.{v
} #ι = Cardinal.lift.{w} (Module.rank R M)
· 使用定理 `Cardinal.mk_punit`：mk_punit : #PUnit = 1
-/
theorem rank_self : Module.rank R R = 1 := by
  rw [← Cardinal.lift_inj, ← (Basis.singleton PUnit R).mk_eq_rank, Cardinal.mk_punit]

/-- A ring satisfying `StrongRankCondition` (such as a `DivisionRing`) is one-dimensional as a
module over itself. -/
@[simp]
/-
**Module.finrank_self** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finrank_self : finrank R R = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_eq_of_rank_eq`：finrank_eq_of_rank_eq {n : Nat} (h : Modul
e.rank R M = ↑n) : finrank R M = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.rank_self`：rank_self : Module.rank R R = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A ring satisfying `StrongRankCondition` (such as a `DivisionRing`) is one-dimens
ional as a
module over itself.
-/
theorem finrank_self : finrank R R = 1 :=
  finrank_eq_of_rank_eq (by simp)

variable {R} in
/-
**Module.finrank_of_bijective_toSpanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `Module`
。
形式化陈述：finrank_of_bijective_toSpanSingleton {x : M} (h : Bijective (LinearMap.toS
panSingleton R M x)) : finrank R M = 1
参数：h : Bijective (LinearMap.toSpanSingleton R M x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `Module.finrank_self`：finrank_self : finrank R R = 1
-/
theorem finrank_of_bijective_toSpanSingleton {x : M}
    (h : Bijective (LinearMap.toSpanSingleton R M x)) : finrank R M = 1 := by
  rw [← (LinearEquiv.ofBijective _ h).finrank_eq, finrank_self]

variable {R} in
/-
**Module.rank_of_bijective_toSpanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：rank_of_bijective_toSpanSingleton {x : M} (h : Bijective (LinearMap.toSpan
Singleton R M x)) : Module.rank R M = 1
参数：h : Bijective (LinearMap.toSpanSingleton R M x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.rank_eq_one_iff_finrank_eq_one`：rank_eq_one_iff_finrank_eq_one : 
Module.rank R M = 1 ↔ finrank R M = 1
· 使用定理 `Module.finrank_of_bijective_toSpanSingleton`：finrank_of_bijective_toSpan
Singleton {x : M} (h : Bijective (LinearMap.toSpanSingleton R M x)) : finrank R 
M = 1
-/
theorem rank_of_bijective_toSpanSingleton {x : M}
    (h : Bijective (LinearMap.toSpanSingleton R M x)) : Module.rank R M = 1 := by
  rw [rank_eq_one_iff_finrank_eq_one, finrank_of_bijective_toSpanSingleton h]
/-
**Module.finrank_of_bijective_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finrank_of_bijective_algebraMap {R S : Type*} [CommSemiring R] [Semiring S
] [Algebra R S] [StrongRankCondition R] (h : Bijective (algebraMap R S)) : finra
nk R S = 1
参数：h : Bijective (algebraMap R S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `Module.finrank_self`：finrank_self : finrank R R = 1
-/
theorem finrank_of_bijective_algebraMap {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    [StrongRankCondition R] (h : Bijective (algebraMap R S)) : finrank R S = 1 := by
  rw [← (AlgEquiv.ofBijective (Algebra.ofId R S) h).toLinearEquiv.finrank_eq, finrank_self]
/-
**Module.rank_of_bijective_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：rank_of_bijective_algebraMap {R S : Type*} [CommSemiring R] [Semiring S] [
Algebra R S] [StrongRankCondition R] (h : Bijective (algebraMap R S)) : Module.r
ank R S = 1
参数：h : Bijective (algebraMap R S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.rank_eq_one_iff_finrank_eq_one`：rank_eq_one_iff_finrank_eq_one : 
Module.rank R M = 1 ↔ finrank R M = 1
· 使用定理 `Module.finrank_of_bijective_algebraMap`：finrank_of_bijective_algebraMap 
{R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] [StrongRankCondition R
] (h : Bijective (algebraMap…
-/
theorem rank_of_bijective_algebraMap {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    [StrongRankCondition R] (h : Bijective (algebraMap R S)) : Module.rank R S = 1 := by
  rw [rank_eq_one_iff_finrank_eq_one, finrank_of_bijective_algebraMap h]

/-- Given a basis of a ring over itself indexed by a type `ι`, then `ι` is `Unique`. -/
@[instance_reducible]
/-
**Module._root_.Module.Basis.unique** 是 Mathlib 中的一个定义，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a basis of a ring over itself indexed by a type `ι`, then `ι` is `Unique`.
-/
noncomputable def _root_.Module.Basis.unique {ι : Type*} (b : Basis ι R R) : Unique ι := by
  have : Cardinal.mk ι = ↑(Module.finrank R R) := (Module.mk_finrank_eq_card_basis b).symm
  have : Subsingleton ι ∧ Nonempty ι := by simpa [Cardinal.eq_one_iff_unique]
  exact Nonempty.some ((unique_iff_subsingleton_and_nonempty _).2 this)

variable (M)

/-- The rank of a finite module is finite. -/
/-
**Module.rank_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：rank_lt_aleph0 [Module.Finite R M] : Module.rank R M < ℵ₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.rank_def`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.rank R M = ⨆ ι, C
ardin…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.finite_def`：finite_def {R M} [Semiring R] [AddCommMonoid M] [Modu
le R M] : Module.Finite R M ↔ (⊤ : Submodule R M).FG
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `linearIndependent_le_span_finset`：linearIndependent_le_span_finset {ι : 
Type*} (v : ι -> M) (i : LinearIndependent R v) (w : Finset M) (s : span R (w : 
Set M) = ⊤) : #ι <= w.…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0

--- 原说明 ---
The rank of a finite module is finite.
-/
theorem rank_lt_aleph0 [Module.Finite R M] : Module.rank R M < ℵ₀ := by
  simp only [Module.rank_def]
  obtain ⟨S, hS⟩ := Module.finite_def.mp ‹_›
  exact (ciSup_le' fun i => linearIndependent_le_span_finset _ i.prop S hS).trans_lt
    natCast_lt_aleph0
/-
**Module.** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance {R M : Type*} [DivisionRing R] [AddCommGroup M] [Module R M]
    {s t : Set M} [Module.Finite R (span R t)]
    (hs : LinearIndepOn R id s) (hst : s ⊆ t) :
    Fintype (hs.extend hst) := by
  refine Classical.choice (Cardinal.lt_aleph0_iff_fintype.1 ?_)
  rw [← rank_span_set (hs.linearIndepOn_extend hst), hs.span_extend_eq_span]
  exact Module.rank_lt_aleph0 ..

/-- If `M` is finite, `finrank M = rank M`. -/
@[simp]
/-
**Module.finrank_eq_rank** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finrank_eq_rank [Module.Finite R M] : ↑(finrank R M) = Module.rank R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank.eq_1`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.finrank R M =
 Cardinal…
· 使用定理 `Cardinal.cast_toNat_of_lt_aleph0`：cast_toNat_of_lt_aleph0 {c : Cardinal}
 (h : c < ℵ₀) : ↑(toNat c) = c
· 使用定理 `Module.rank_lt_aleph0`：rank_lt_aleph0 [Module.Finite R M] : Module.rank 
R M < ℵ₀

--- 原说明 ---
If `M` is finite, `finrank M = rank M`.
-/
theorem finrank_eq_rank [Module.Finite R M] : ↑(finrank R M) = Module.rank R M := by
  rw [Module.finrank, cast_toNat_of_lt_aleph0 (rank_lt_aleph0 R M)]
/-
**Module.finrank_eq_zero_iff_of_free** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finrank_eq_zero_iff_of_free [Module.Free R M] [Module.Finite R M] : Module
.finrank R M = 0 ↔ Subsingleton M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.rank_lt_aleph0`：rank_lt_aleph0 [Module.Finite R M] : Module.rank 
R M < ℵ₀
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem finrank_eq_zero_iff_of_free [Module.Free R M] [Module.Finite R M] :
    Module.finrank R M = 0 ↔ Subsingleton M := by
  have := Module.rank_lt_aleph0 R M
  rw [← not_le] at this
  simp [Module.finrank, this, Module.rank_zero_iff_of_free]

@[nontriviality]
/-
**Module.finrank_eq_zero_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finrank_eq_zero_of_subsingleton [Module.Free R M] [Subsingleton M] : Modul
e.finrank R M = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.finrank_eq_zero_iff_of_free`：finrank_eq_zero_iff_of_free [Module.
Free R M] [Module.Finite R M] : Module.finrank R M = 0 ↔ Subsingleton M
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
-/
theorem finrank_eq_zero_of_subsingleton [Module.Free R M] [Subsingleton M] :
    Module.finrank R M = 0 :=
  (finrank_eq_zero_iff_of_free R M).mpr inferInstance
/-
**Module.finrank_pos_iff_of_free** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finrank_pos_iff_of_free [Module.Free R M] [Module.Finite R M] : 0 < Module
.finrank R M ↔ Nontrivial M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `not_subsingleton_iff_nontrivial`：not_subsingleton_iff_nontrivial : ¬Subs
ingleton α ↔ Nontrivial α
· 使用定理 `iff_not_comm`：iff_not_comm : (a ↔ ¬b) ↔ (b ↔ ¬a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem finrank_pos_iff_of_free [Module.Free R M] [Module.Finite R M] :
    0 < Module.finrank R M ↔ Nontrivial M := by
  rw [← not_subsingleton_iff_nontrivial, ← iff_not_comm]
  simp [Module.finrank_eq_zero_iff_of_free]

/-- If `M` is finite, then `finrank N = rank N` for all `N : Submodule M`. Note that
such an `N` need not be finitely generated. -/
/-
**Module._root_.Submodule.finrank_eq_rank** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is finite, then `finrank N = rank N` for all `N : Submodule M`. Note that
such an `N` need not be finitely generated.
-/
protected theorem _root_.Submodule.finrank_eq_rank [Module.Finite R M] (N : Submodule R M) :
    finrank R N = Module.rank R N := by
  rw [finrank, Cardinal.cast_toNat_of_lt_aleph0]
  exact lt_of_le_of_lt (Submodule.rank_le N) (rank_lt_aleph0 R M)

end Module

variable {M'} [AddCommMonoid M'] [Module R M']

/-
**LinearMap.finrank_le_finrank_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.finrank_le_finrank_of_injective [Module.Finite R M'] {f : M ->ₗ[
R] M'} (hf : Function.Injective f) : finrank R M <= finrank R M'
参数：hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_le_finrank_of_rank_le_rank`：finrank_le_finrank_of_rank_le
_rank (h : lift.{w} (Module.rank R M) <= Cardinal.lift.{v} (Module.rank R N)) (h
' : Module.rank R N < ℵ₀) : fin…
· 使用定理 `LinearMap.lift_rank_le_of_injective`：LinearMap.lift_rank_le_of_injective
 (f : M ->ₗ[R] M') (i : Injective f) : Cardinal.lift.{v'} (Module.rank R M) <= C
ardinal.lift.{v} (Module.…
· 使用定理 `Module.rank_lt_aleph0`：rank_lt_aleph0 [Module.Finite R M] : Module.rank 
R M < ℵ₀
-/
theorem LinearMap.finrank_le_finrank_of_injective [Module.Finite R M'] {f : M →ₗ[R] M'}
    (hf : Function.Injective f) : finrank R M ≤ finrank R M' :=
  finrank_le_finrank_of_rank_le_rank (lift_rank_le_of_injective _ hf) (rank_lt_aleph0 _ _)
/-
**LinearMap.finrank_le_finrank_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.finrank_le_finrank_of_surjective [Module.Finite R M] {f : M ->ₗ[
R] M'} (hf : Function.Surjective f) : Module.finrank R M' <= Module.finrank R M
参数：hf : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_le_finrank_of_rank_le_rank`：finrank_le_finrank_of_rank_le
_rank (h : lift.{w} (Module.rank R M) <= Cardinal.lift.{v} (Module.rank R N)) (h
' : Module.rank R N < ℵ₀) : fin…
· 使用定理 `LinearMap.lift_rank_le_of_surjective`：LinearMap.lift_rank_le_of_surjecti
ve (f : M ->ₗ[R] M') (h : Surjective f) : lift.{v} (Module.rank R M') <= lift.{v
'} (Module.rank R M)
· 使用定理 `Module.rank_lt_aleph0`：rank_lt_aleph0 [Module.Finite R M] : Module.rank 
R M < ℵ₀
-/
theorem LinearMap.finrank_le_finrank_of_surjective [Module.Finite R M] {f : M →ₗ[R] M'}
    (hf : Function.Surjective f) : Module.finrank R M' ≤ Module.finrank R M :=
  finrank_le_finrank_of_rank_le_rank (lift_rank_le_of_surjective _ hf) (rank_lt_aleph0 _ _)
/-
**LinearMap.finrank_range_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.finrank_range_le [Module.Finite R M] (f : M ->ₗ[R] M') : finrank
 R (LinearMap.range f) <= finrank R M
参数：f : M ->ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_le_finrank_of_rank_le_rank`：finrank_le_finrank_of_rank_le
_rank (h : lift.{w} (Module.rank R M) <= Cardinal.lift.{v} (Module.rank R N)) (h
' : Module.rank R N < ℵ₀) : fin…
· 使用定理 `lift_rank_range_le`：lift_rank_range_le (f : M ->ₗ[R] M') : Cardinal.lift
.{v} (Module.rank R (LinearMap.range f)) <= Cardinal.lift.{v'} (Module.rank R M)
· 使用定理 `Module.rank_lt_aleph0`：rank_lt_aleph0 [Module.Finite R M] : Module.rank 
R M < ℵ₀
-/
theorem LinearMap.finrank_range_le [Module.Finite R M] (f : M →ₗ[R] M') :
    finrank R (LinearMap.range f) ≤ finrank R M :=
  finrank_le_finrank_of_rank_le_rank (lift_rank_range_le f) (rank_lt_aleph0 _ _)
/-
**LinearMap.finrank_le_of_isSMulRegular** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.finrank_le_of_isSMulRegular {S : Type*} [CommSemiring S] [Algebr
a S R] [Module S M] [IsScalarTower S R M] (L L' : Submodule R M) [Module.Finite 
R L'] {s : S} (hr : IsSMulRegular M s) (h : forall x in L, s • x in L') : Module
.finrank R L <= Module.finrank R L'
参数：L L' : Submodule R M；hr : IsSMulRegular M s；h : forall x in L, s • x in L'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_le_finrank_of_rank_le_rank`：finrank_le_finrank_of_rank_le
_rank (h : lift.{w} (Module.rank R M) <= Cardinal.lift.{v} (Module.rank R N)) (h
' : Module.rank R N < ℵ₀) : fin…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用引理 `rank_le_of_isSMulRegular`：rank_le_of_isSMulRegular {S : Type*} [CommSemi
ring S] [Algebra S R] [Module S M] [IsScalarTower S R M] (L L' : Submodule R M) 
{s : S} (hr : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
-/
theorem LinearMap.finrank_le_of_isSMulRegular {S : Type*} [CommSemiring S] [Algebra S R]
    [Module S M] [IsScalarTower S R M] (L L' : Submodule R M) [Module.Finite R L'] {s : S}
    (hr : IsSMulRegular M s) (h : ∀ x ∈ L, s • x ∈ L') :
    Module.finrank R L ≤ Module.finrank R L' := by
  refine finrank_le_finrank_of_rank_le_rank (lift_le.mpr <| rank_le_of_isSMulRegular L L' hr h) ?_
  rw [← Module.finrank_eq_rank R L']
  exact natCast_lt_aleph0

variable (R S M) in
/-- Also see `Module.finrank_top_le_finrank_of_isScalarTower_of_free`
for a version with different typeclass constraints. -/
/-
**Module.finrank_top_le_finrank_of_isScalarTower** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.finrank_top_le_finrank_of_isScalarTower [Module.Finite R M] [Semiri
ng S] [Module S M] [Module R S] [IsScalarTower R S S] [FaithfulSMul R S] [IsScal
arTower R S M] : finrank S M <= finrank R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank.eq_1`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.finrank R M =
 Cardinal…
· 使用定理 `Cardinal.toNat_le_iff_le_of_lt_aleph0`：toNat_le_iff_le_of_lt_aleph0 (hc 
: c < ℵ₀) (hd : d < ℵ₀) : toNat c <= toNat d ↔ c <= d
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `Module.rank_top_le_rank_of_isScalarTower`：Module.rank_top_le_rank_of_isS
calarTower [Module R' M] [SMulWithZero R R'] [IsScalarTower R R' M] [FaithfulSMu
l R R'] [IsScalarTower R R' R'…
· 使用定理 `Module.rank_lt_aleph0`：rank_lt_aleph0 [Module.Finite R M] : Module.rank 
R M < ℵ₀

--- 原说明 ---
Also see `Module.finrank_top_le_finrank_of_isScalarTower_of_free`
for a version with different typeclass constraints.
-/
lemma Module.finrank_top_le_finrank_of_isScalarTower [Module.Finite R M] [Semiring S]
    [Module S M] [Module R S] [IsScalarTower R S S] [FaithfulSMul R S] [IsScalarTower R S M] :
    finrank S M ≤ finrank R M := by
  rw [finrank, finrank, Cardinal.toNat_le_iff_le_of_lt_aleph0]
  · exact rank_top_le_rank_of_isScalarTower R S M
  · exact lt_of_le_of_lt (rank_top_le_rank_of_isScalarTower R S M) (Module.rank_lt_aleph0 R M)
  · exact Module.rank_lt_aleph0 _ _

variable (R) in
/-- Also see `Module.finrank_bot_le_finrank_of_isScalarTower_of_free`
for a version with different typeclass constraints. -/
/-
**Module.finrank_bot_le_finrank_of_isScalarTower** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.finrank_bot_le_finrank_of_isScalarTower (S T : Type*) [Semiring S] 
[Semiring T] [Module R T] [Module S T] [Module R S] [IsScalarTower R S T] [IsSca
larTower S T T] [FaithfulSMul S T] [Module.Finite R T] : finrank R S <= finrank 
R T
参数：S T : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_le_finrank_of_rank_le_rank`：finrank_le_finrank_of_rank_le
_rank (h : lift.{w} (Module.rank R M) <= Cardinal.lift.{v} (Module.rank R N)) (h
' : Module.rank R N < ℵ₀) : fin…
· 使用引理 `Module.lift_rank_bot_le_lift_rank_of_isScalarTower`：Module.lift_rank_bot
_le_lift_rank_of_isScalarTower (T : Type w) [Module R R'] [NonAssocSemiring T] [
Module R T] [Module R' T] [IsScalarTower…
· 使用定理 `Module.rank_lt_aleph0`：rank_lt_aleph0 [Module.Finite R M] : Module.rank 
R M < ℵ₀

--- 原说明 ---
Also see `Module.finrank_bot_le_finrank_of_isScalarTower_of_free`
for a version with different typeclass constraints.
-/
lemma Module.finrank_bot_le_finrank_of_isScalarTower (S T : Type*) [Semiring S] [Semiring T]
    [Module R T] [Module S T] [Module R S] [IsScalarTower R S T]
    [IsScalarTower S T T] [FaithfulSMul S T] [Module.Finite R T] :
    finrank R S ≤ finrank R T :=
  finrank_le_finrank_of_rank_le_rank (lift_rank_bot_le_lift_rank_of_isScalarTower R S T)
    (Module.rank_lt_aleph0 _ _)

omit [StrongRankCondition R]
/-
**strongRankCondition_iff_forall_rank_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strongRankCondition_iff_forall_rank_lt_aleph0 [Nontrivial R] : StrongRankC
ondition R ↔ forall n : Nat, Module.rank R (Fin n -> R) < ℵ₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `strongRankCondition_iff_succ`：strongRankCondition_iff_succ : StrongRankC
ondition R ↔ forall (n : Nat) (f : (Fin (n + 1) -> R) ->ₗ[R] Fin n -> R), ¬Funct
ion.Injective f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearMap.exists_finsupp_nat_of_fin_fun_injective`：exists_finsupp_nat_of
_fin_fun_injective {n : Nat} {f : (Fin (n + 1) -> P) ->ₗ[R] Fin n -> P} (inj : I
njective f) : exists g : (Nat ->₀ P) ->…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Cardinal.lift_uzero`：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearIndependent.cardinal_lift_le_rank`：cardinal_lift_le_rank {ι : Type
 w} {v : ι -> M} (hv : LinearIndependent R v) : Cardinal.lift.{v} #ι <= Cardinal
.lift.{w} (Module.rank R M)
· 使用定理 `LinearIndependent.map_injOn`：LinearIndependent.map_injOn (hv : LinearInd
ependent R v) (f : M ->ₗ[R] M') (hf_inj : Set.InjOn f (span R (Set.range v))) : 
LinearIndependent…
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Module.le_rank_iff_exists_linearMap`：le_rank_iff_exists_linearMap {n : N
at} : n <= Module.rank R M ↔ exists f : (Fin n -> R) ->ₗ[R] M, Injective f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.natCast_le_aleph0`：∀ {n : ℕ}, ↑n ≤ Cardinal.aleph0
-/
theorem strongRankCondition_iff_forall_rank_lt_aleph0 [Nontrivial R] :
    StrongRankCondition R ↔ ∀ n : ℕ, Module.rank R (Fin n → R) < ℵ₀ :=
  (strongRankCondition_iff_succ R).trans <| not_iff_not.mp <| by
    push Not
    refine ⟨fun ⟨n, f, inj⟩ ↦ ⟨n, ?_⟩, fun ⟨n, le⟩ ↦
      ⟨n, le_rank_iff_exists_linearMap.mp (natCast_le_aleph0.trans le)⟩⟩
    have ⟨g, hg⟩ := f.exists_finsupp_nat_of_fin_fun_injective inj
    convert! (Finsupp.basisSingleOne.linearIndependent.map_injOn _ hg.injOn).cardinal_lift_le_rank
    simp
/-
**strongRankCondition_iff_forall_zero_lt_finrank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strongRankCondition_iff_forall_zero_lt_finrank [Nontrivial R] : StrongRank
Condition R ↔ forall n > 0, 0 < finrank R (Fin n -> R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `strongRankCondition_iff_forall_rank_lt_aleph0`：strongRankCondition_iff_f
orall_rank_lt_aleph0 [Nontrivial R] : StrongRankCondition R ↔ forall n : Nat, Mo
dule.rank R (Fin n -> R) < ℵ₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LinearMap.rank_le_of_injective`：LinearMap.rank_le_of_injective (f : M ->
ₗ[R] M₁) (i : Injective f) : Module.rank R M <= Module.rank R M₁
· 使用定理 `Function.extend_injective`：extend_injective (hf : Injective f) (e' : β -
> γ) : Injective fun g => extend f g e'
· 使用引理 `Fin.castSucc_injective`：castSucc_injective (n : Nat) : Injective (@Fin.c
astSucc n)
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `Module.one_le_rank_iff`：Module.one_le_rank_iff : 1 <= Module.rank R M ↔ 
exists f : R ->ₗ[R] M, Injective f
· 使用定理 `Cardinal.one_le_iff_ne_zero`：∀ {c : Cardinal.{u_1}}, 1 ≤ c ↔ c ≠ 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Pi.single_injective`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] (i : ι),   Function.Injective (Pi.single
 i)
-/
theorem strongRankCondition_iff_forall_zero_lt_finrank [Nontrivial R] :
    StrongRankCondition R ↔ ∀ n > 0, 0 < finrank R (Fin n → R) := by
  rw [strongRankCondition_iff_forall_rank_lt_aleph0, ← not_iff_not]
  push Not
  simp_rw [finrank, Nat.le_zero, toNat_eq_zero]
  refine ⟨fun ⟨n, le⟩ ↦ ⟨n + 1, n.succ_pos, ?_⟩, fun ⟨n, pos, eq⟩ ↦ ⟨n, ?_⟩⟩
  · exact .inr <| le.trans <| LinearMap.rank_le_of_injective
      (ExtendByZero.linearMap R _) <| extend_injective (Fin.castSucc_injective n) _
  · rw [or_iff_not_imp_left, ← Ne, ← Cardinal.one_le_iff_ne_zero, one_le_rank_iff] at eq
    rw [← n.succ_pred_eq_of_pos pos] at eq ⊢
    exact eq ⟨.single R (fun _ ↦ _) 0, Pi.single_injective (M := fun _ ↦ _) _⟩

/-- If each `Rⁿ` is a Noetherian `R`-module, then `R` satisfies the strong rank condition.
Not an instance for performance reasons.

If `R` is a ring, the assumption is equivalent to `R` being a left-Noetherian ring, but this
is not necessarily the case for semirings: `ℕ` is a Noetherian semiring but `ℕ²` is not a
Noetherian `ℕ`-module. (`ℕ` does satisfy the strong rank condition.) -/
/-
**StrongRankCondition.of_isNoetherian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrongRankCondition.of_isNoetherian [Nontrivial R] [forall n, IsNoetherian
 R (Fin n -> R)] : StrongRankCondition R
参数：Fin n -> R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `strongRankCondition_iff_succ`：strongRankCondition_iff_succ : StrongRankC
ondition R ↔ forall (n : Nat) (f : (Fin (n + 1) -> R) ->ₗ[R] Fin n -> R), ¬Funct
ion.Injective f
· 使用定理 `not_subsingleton`：not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α
· 使用定理 `IsNoetherian.subsingleton_of_injective`：IsNoetherian.subsingleton_of_inj
ective {P : Type*} [AddCommMonoid P] [Module R P] {f : P × M ->ₗ[R] M} (inj : In
jective f) : Subsingleton P
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…

--- 原说明 ---
If each `Rⁿ` is a Noetherian `R`-module, then `R` satisfies the strong rank cond
ition.
Not an instance for performance reasons.

If `R` is a ring, the assumption is equivalent to `R` being a left-Noetherian ri
ng, but this
is not necessarily the case for semirings: `ℕ` is a Noetherian semiring but `ℕ²`
 is not a
Noetherian `ℕ`-module. (`ℕ` does satisfy the strong rank condition.)
-/
theorem StrongRankCondition.of_isNoetherian [Nontrivial R] [∀ n, IsNoetherian R (Fin n → R)] :
    StrongRankCondition R :=
  (strongRankCondition_iff_succ R).2 fun n f hf ↦
    have e := LinearEquiv.piCongrLeft R (fun _ ↦ R) (finSuccEquiv n) ≪≫ₗ .piOptionEquivProd _
    not_subsingleton R <| IsNoetherian.subsingleton_of_injective
      (f := f ∘ₗ e.symm.toLinearMap) (hf.comp e.symm.injective)

end StrongRankCondition

namespace Submodule

variable {K M : Type*} [DivisionRing K] [AddCommGroup M] [Module K M] {s : Set M} {x : M}
  [Module.Finite K (span K s)]

variable (K s) in
/-- This is a version of `exists_linearIndependent`
with an upper estimate on the size of the finite set we choose. -/
/-
**Submodule.exists_finset_span_eq_linearIndepOn** 是 Mathlib 中的一个定理，位于命名空间 `Submo
dule`。
形式化陈述：exists_finset_span_eq_linearIndepOn : exists t : Finset M, ↑t subseteq s ∧
 t.card = finrank K (span K s) ∧ span K t = span K s ∧ LinearIndepOn K id (t : S
et M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_linearIndependent`：exists_linearIndependent : exists b subseteq t
, span K b = span K t ∧ LinearIndependent K ((↑) : b -> V)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_set_eq_nat_iff_finset`：mk_set_eq_nat_iff_finset {α} {s : Set
 α} {n : Nat} : #s = n ↔ exists t : Finset α, (t : Set α) = s ∧ t.card = n
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `rank_span_set`：rank_span_set {s : Set M} (hs : LinearIndepOn R id s) : M
odule.rank R ↑(span R s) = #s

--- 原说明 ---
This is a version of `exists_linearIndependent`
with an upper estimate on the size of the finite set we choose.
-/
theorem exists_finset_span_eq_linearIndepOn :
    ∃ t : Finset M, ↑t ⊆ s ∧ t.card = finrank K (span K s) ∧
      span K t = span K s ∧ LinearIndepOn K id (t : Set M) := by
  rcases exists_linearIndependent K s with ⟨t, ht_sub, ht_span, ht_indep⟩
  obtain ⟨t, rfl, ht_card⟩ : ∃ u : Finset M, ↑u = t ∧ u.card = finrank K (span K s) := by
    rw [← Cardinal.mk_set_eq_nat_iff_finset, finrank_eq_rank, ← ht_span, rank_span_set ht_indep]
  exact ⟨t, ht_sub, ht_card, ht_span, ht_indep⟩

variable (K s) in
/-
**Submodule.exists_fun_fin_finrank_span_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`
。
形式化陈述：exists_fun_fin_finrank_span_eq : exists f : Fin (finrank K (span K s)) -> 
M, (forall i, f i in s) ∧ span K (range f) = span K s ∧ LinearIndependent K f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_finset_span_eq_linearIndepOn`：exists_finset_span_eq_lin
earIndepOn : exists t : Finset M, ↑t subseteq s ∧ t.card = finrank K (span K s) 
∧ span K t = span K s ∧ LinearIndep…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EquivLike.range_comp`：∀ {ι : Sort u_1} {ι' : Sort u_2} {E : Type u_3} [i
nst : EquivLike E ι ι'] {α : Type u_4} (f : ι' → α) (e : E),   Set.range (f ∘ ⇑e
) = Set.ra…
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem exists_fun_fin_finrank_span_eq :
    ∃ f : Fin (finrank K (span K s)) → M, (∀ i, f i ∈ s) ∧ span K (range f) = span K s ∧
      LinearIndependent K f := by
  rcases exists_finset_span_eq_linearIndepOn K s with ⟨t, hts, ht_card, ht_span, ht_indep⟩
  set e := (Finset.equivFinOfCardEq ht_card).symm
  exact ⟨(↑) ∘ e, fun i ↦ hts (e i).2, by simpa, ht_indep.comp _ e.injective⟩

/-- This is a version of `mem_span_set` with an estimate on the number of terms in the sum. -/
/-
**Submodule.mem_span_set_iff_exists_finsupp_le_finrank** 是 Mathlib 中的一个定理，位于命名空间
 `Submodule`。
形式化陈述：mem_span_set_iff_exists_finsupp_le_finrank : x in span K s ↔ exists c : M 
->₀ K, c.support.card <= finrank K (span K s) ∧ ↑c.support subseteq s ∧ c.sum (f
un mi r => r • mi) = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_finset_span_eq_linearIndepOn`：exists_finset_span_eq_lin
earIndepOn : exists t : Finset M, ↑t subseteq s ∧ t.card = finrank K (span K s) 
∧ span K t = span K s ∧ LinearIndep…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_span_set`：Submodule.mem_span_set {m : M} {s : Set M} : m i
n Submodule.span R s ↔ exists c : M ->₀ R, (c.support : Set M) subseteq s ∧ (c.s
um fun mi r …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_mono`：card_mono : Monotone (@card α)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
This is a version of `mem_span_set` with an estimate on the number of terms in t
he sum.
-/
theorem mem_span_set_iff_exists_finsupp_le_finrank :
    x ∈ span K s ↔ ∃ c : M →₀ K, c.support.card ≤ finrank K (span K s) ∧
      ↑c.support ⊆ s ∧ c.sum (fun mi r ↦ r • mi) = x := by
  constructor
  · intro h
    rcases exists_finset_span_eq_linearIndepOn K s with ⟨t, ht_sub, ht_card, ht_span, ht_indep⟩
    rcases mem_span_set.mp (ht_span ▸ h) with ⟨c, hct, hx⟩
    refine ⟨c, ?_, hct.trans ht_sub, hx⟩
    exact ht_card ▸ Finset.card_mono hct
  · rintro ⟨c, -, hcs, hx⟩
    exact mem_span_set.mpr ⟨c, hcs, hx⟩

end Submodule

namespace Algebra

/--
An extension of rings `R ⊆ S` is quadratic if `S` is a free `R`-algebra of rank `2`.
-/
-- TODO. use this in connection with `NumberTheory.Zsqrtd`
/-
**Algebra.IsQuadraticExtension** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type u_2) →   (S : Type u_3) → [inst : CommSemiring R] → [StrongRankC
ondition R] → [inst_2 : Semiring S] → [Algebra R S] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class IsQuadraticExtension (R S : Type*) [CommSemiring R] [StrongRankCondition R] [Semiring S]
    [Algebra R S] extends Module.Free R S where
  finrank_eq_two' : Module.finrank R S = 2
/-
**Algebra.IsQuadraticExtension.finrank_eq_two** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
.IsQuadraticExtension`。
形式化陈述：∀ (R : Type u_2) (S : Type u_3) [inst : CommSemiring R] [inst_1 : StrongRa
nkCondition R] [inst_2 : Semiring S]   [inst_3 : Algebra R S] [Algebra.IsQuadrat
icExtension R S], Module.finrank R S = 2
参数：R : Type u_2；S : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsQuadraticExtension.finrank_eq_two'`：∀ {R : Type u_2} {S : Type
 u_3} {inst : CommSemiring R} {inst_1 : StrongRankCondition R} {inst_2 : Semirin
g S}   {inst_3 : Algebra R S} [sel…
-/
theorem IsQuadraticExtension.finrank_eq_two (R S : Type*) [CommSemiring R] [StrongRankCondition R]
    [Semiring S] [Algebra R S] [IsQuadraticExtension R S] :
    Module.finrank R S = 2 := finrank_eq_two'

end Algebra

