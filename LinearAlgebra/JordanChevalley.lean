/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Dynamics.Newton
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Jordan-Chevalley-Dunford decomposition

Given a finite-dimensional linear endomorphism `f`, the Jordan-Chevalley-Dunford theorem provides a
sufficient condition for there to exist a nilpotent endomorphism `n` and a semisimple endomorphism
`s`, such that `f = n + s` and both `n` and `s` are polynomial expressions in `f`.

The condition is that there exists a separable polynomial `P` such that the endomorphism `P(f)` is
nilpotent. This condition is always satisfied when the coefficient field is perfect.

The proof given here uses Newton's method and is taken from Chambert-Loir's notes:
[Algèbre](http://webusers.imj-prg.fr/~antoine.chambert-loir/enseignement/2022-23/agreg/algebre.pdf)

## Main definitions / results:

* `Module.End.exists_isNilpotent_isSemisimple`: an endomorphism of a finite-dimensional vector
  space over a perfect field may be written as a sum of nilpotent and semisimple endomorphisms.
  Moreover these nilpotent and semisimple components are polynomial expressions in the original
  endomorphism.
* `Module.End.isNilpotent_isSemisimple_unique`: the Jordan-Chevalley-Dunford decomposition is
  unique: if `n₁ + s₁ = n₂ + s₂` with `nᵢ` nilpotent, `sᵢ` semisimple, and `nᵢ`, `sᵢ` commuting,
  then `n₁ = n₂` and `s₁ = s₂`.

-/

public section

open Algebra Polynomial

namespace Module.End

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {f : End K V}

/-
**Module.End.exists_isNilpotent_isSemisimple_of_separable_of_dvd_pow** 是 Mathlib
 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：exists_isNilpotent_isSemisimple_of_separable_of_dvd_pow {P : K[X]} {k : Na
t} (sep : P.Separable) (nil : minpoly K f ∣ P ^ k) : existsᵉ (n in adjoin K {f})
 (s in adjoin K {f}), IsNilpotent n ∧ IsSemisimple s ∧ f = n + s
参数：sep : P.Separable；nil : minpoly K f ∣ P ^ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.self_mem_adjoin_singleton`：self_mem_adjoin_singleton (x : A) : x
 in R[x]
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Polynomial.coe_aeval_mk_apply`：coe_aeval_mk_apply {S : Subalgebra R A} (
h : x in S) : (aeval (⟨x, h⟩ : S) p : A) = aeval x p
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsCoprime.pow_left`：IsCoprime.pow_left (H : IsCoprime x y) : IsCoprime (
x ^ m) y
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `minpoly.dvd_iff`：dvd_iff {p : A[X]} : minpoly A x ∣ p ↔ Polynomial.aeval
 x p = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
（共 44 条，此处仅展示前 30 条）
-/
theorem exists_isNilpotent_isSemisimple_of_separable_of_dvd_pow {P : K[X]} {k : ℕ}
    (sep : P.Separable) (nil : minpoly K f ∣ P ^ k) :
    ∃ᵉ (n ∈ adjoin K {f}) (s ∈ adjoin K {f}), IsNilpotent n ∧ IsSemisimple s ∧ f = n + s := by
  set ff : adjoin K {f} := ⟨f, self_mem_adjoin_singleton K f⟩
  set P' := derivative P
  have nil' : IsNilpotent (aeval ff P) := by
    use k
    obtain ⟨q, hq⟩ := nil
    rw [← map_pow, Subtype.ext_iff]
    simp [ff, hq]
  have sep' : IsUnit (aeval ff P') := by
    obtain ⟨a, b, h⟩ : IsCoprime (P ^ k) P' := sep.pow_left
    replace h : (aeval f b) * (aeval f P') = 1 := by
      simpa only [map_add, map_mul, map_one, minpoly.dvd_iff.mp nil, mul_zero, zero_add]
        using (aeval f).congr_arg h
    refine .of_mul_eq_one_right (aeval ff b) (Subtype.ext_iff.mpr ?_)
    simpa [ff, coe_aeval_mk_apply] using h
  obtain ⟨⟨s, mem⟩, ⟨⟨k, hk⟩, hss⟩, -⟩ := existsUnique_nilpotent_sub_and_aeval_eq_zero nil' sep'
  refine ⟨f - s, ?_, s, mem, ⟨k, ?_⟩, ?_, (sub_add_cancel f s).symm⟩
  · exact sub_mem (self_mem_adjoin_singleton K f) mem
  · rw [Subtype.ext_iff] at hk
    simpa using hk
  · replace hss : aeval s P = 0 := by rwa [Subtype.ext_iff, coe_aeval_mk_apply] at hss
    exact isSemisimple_of_squarefree_aeval_eq_zero sep.squarefree hss

variable [FiniteDimensional K V]

/-- **Jordan-Chevalley-Dunford decomposition**: an endomorphism of a finite-dimensional vector space
over a perfect field may be written as a sum of nilpotent and semisimple endomorphisms. Moreover
these nilpotent and semisimple components are polynomial expressions in the original endomorphism.
-/
/-
**Module.End.exists_isNilpotent_isSemisimple** 是 Mathlib 中的一个定理，位于命名空间 `Module.E
nd`。
形式化陈述：exists_isNilpotent_isSemisimple [PerfectField K] : existsᵉ (n in adjoin K 
{f}) (s in adjoin K {f}), IsNilpotent n ∧ IsSemisimple s ∧ f = n + s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_squarefree_dvd_pow_of_ne_zero`：∀ {R : Type u_1} [inst : CommMonoi
dWithZero R] [UniqueFactorizationMonoid R] {x : R},   x ≠ 0 → ∃ y n, Squarefree 
y ∧ y ∣ x ∧ x ∣ y ^ n
· 使用定理 `Polynomial.uniqueFactorizationMonoid`：∀ {D : Type u} [inst : CommRing D]
 [UniqueFactorizationMonoid D], UniqueFactorizationMonoid (Polynomial D)
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `minpoly.ne_zero_of_finite`：ne_zero_of_finite (e : B) [FiniteDimensional 
A B] : minpoly A e != 0
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Module.End.exists_isNilpotent_isSemisimple_of_separable_of_dvd_pow`：exis
ts_isNilpotent_isSemisimple_of_separable_of_dvd_pow {P : K[X]} {k : Nat} (sep : 
P.Separable) (nil : minpoly K f ∣ P ^ k) : existsᵉ (n in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PerfectField.separable_iff_squarefree`：separable_iff_squarefree {g : K[X
]} : g.Separable ↔ Squarefree g

--- 原说明 ---
**Jordan-Chevalley-Dunford decomposition**: an endomorphism of a finite-dimensio
nal vector space
over a perfect field may be written as a sum of nilpotent and semisimple endomor
phisms. Moreover
these nilpotent and semisimple components are polynomial expressions in the orig
inal endomorphism.
-/
theorem exists_isNilpotent_isSemisimple [PerfectField K] :
    ∃ᵉ (n ∈ adjoin K {f}) (s ∈ adjoin K {f}), IsNilpotent n ∧ IsSemisimple s ∧ f = n + s := by
  obtain ⟨g, k, sep, -, nil⟩ := exists_squarefree_dvd_pow_of_ne_zero (minpoly.ne_zero_of_finite K f)
  rw [← PerfectField.separable_iff_squarefree] at sep
  exact exists_isNilpotent_isSemisimple_of_separable_of_dvd_pow sep nil

/-- **Uniqueness of Jordan-Chevalley-Dunford decomposition**: if `n₁ + s₁ = n₂ + s₂` with `nᵢ`
nilpotent, `sᵢ` semisimple, and `nᵢ`, `sᵢ` commuting, then `n₁ = n₂` and `s₁ = s₂`. -/
/-
**Module.End.isNilpotent_isSemisimple_unique** 是 Mathlib 中的一个定理，位于命名空间 `Module.E
nd`。
形式化陈述：isNilpotent_isSemisimple_unique [PerfectField K] {n₁ s₁ n₂ s₂ : End K V} (
hn₁ : IsNilpotent n₁) (hs₁ : s₁.IsSemisimple) (hn₂ : IsNilpotent n₂) (hs₂ : s₂.I
sSemisimple) (hc₁ : Commute n₁ s₁) (hc₂ : Commute n₂ s₂) (h : n₁ + s₁ = n₂ + s₂)
 : n₁ = n₂ ∧ s₁ = s₂
参数：hn₁ : IsNilpotent n₁；hs₁ : s₁.IsSemisimple；hn₂ : IsNilpotent n₂；hs₂ : s₂.IsSe
misimple；hc₁ : Commute n₁ s₁；hc₂ : Commute n₂ s₂；h : n₁ + s₁ = n₂ + s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.exists_isNilpotent_isSemisimple`：exists_isNilpotent_isSemisim
ple [PerfectField K] : existsᵉ (n in adjoin K {f}) (s in adjoin K {f}), IsNilpot
ent n ∧ IsSemisimple s ∧ f = n +…
· 使用定理 `Commute.add_right`：add_right [Distrib R] {a b c : R} : Commute a b -> Co
mmute a c -> Commute a (b + c)
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.isNilpotent_sub`：isNilpotent_sub (h_comm : Commute x y) (hx : Is
Nilpotent x) (hy : IsNilpotent y) : IsNilpotent (x - y)
· 使用引理 `Algebra.commute_of_mem_adjoin_singleton_of_commute`：commute_of_mem_adjoi
n_singleton_of_commute {a b c : A} (hc : c in R[b]) (h : Commute a b) : Commute 
a c
· 使用定理 `Module.End.IsSemisimple.sub_of_commute`：∀ {M : Type u_2} [inst : AddComm
Group M] {K : Type u_3} [inst_1 : Field K] [inst_2 : _root_.Module K M]   {f g :
 Module.End K M} [FiniteDime…

--- 原说明 ---
**Uniqueness of Jordan-Chevalley-Dunford decomposition**: if `n₁ + s₁ = n₂ + s₂`
 with `nᵢ`
nilpotent, `sᵢ` semisimple, and `nᵢ`, `sᵢ` commuting, then `n₁ = n₂` and `s₁ = s
₂`.
-/
theorem isNilpotent_isSemisimple_unique [PerfectField K]
    {n₁ s₁ n₂ s₂ : End K V}
    (hn₁ : IsNilpotent n₁) (hs₁ : s₁.IsSemisimple)
    (hn₂ : IsNilpotent n₂) (hs₂ : s₂.IsSemisimple)
    (hc₁ : Commute n₁ s₁) (hc₂ : Commute n₂ s₂)
    (h : n₁ + s₁ = n₂ + s₂) :
    n₁ = n₂ ∧ s₁ = s₂ := by
  obtain ⟨n₀, hn₀, s₀, hs₀, hn₀_nil, hs₀_ss, h₀⟩ := (n₁ + s₁).exists_isNilpotent_isSemisimple
  suffices ∀ {n s}, IsNilpotent n → s.IsSemisimple → Commute n s → n₁ + s₁ = n + s → s = s₀ by grind
  intro n s hn hs hc heq
  have hsf : Commute s (n₁ + s₁) := heq ▸ hc.symm.add_right (Commute.refl s)
  have hnf : Commute n (n₁ + s₁) := heq ▸ (Commute.refl n).add_right hc
  have hnil : IsNilpotent (s - s₀) := by
    rw [show s - s₀ = n₀ - n by grind]
    exact (commute_of_mem_adjoin_singleton_of_commute hn₀ hnf).symm.isNilpotent_sub hn₀_nil hn
  have hss : (s - s₀).IsSemisimple :=
    hs.sub_of_commute (commute_of_mem_adjoin_singleton_of_commute hs₀ hsf) hs₀_ss
  grind [eq_zero_of_isNilpotent_isSemisimple hnil hss]

end Module.End

