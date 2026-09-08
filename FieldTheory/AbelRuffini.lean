/-
Copyright (c) 2020 Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# The Abel-Ruffini Theorem

This file proves one direction of the Abel-Ruffini theorem, namely that if an element is solvable
by radicals, then its minimal polynomial has solvable Galois group.

## Main definitions

* `solvableByRad F E` : the intermediate field of solvable-by-radicals elements

## Main results

* The Abel-Ruffini Theorem `isSolvable_gal_of_irreducible`: An irreducible polynomial with a root
  that is solvable by radicals has a solvable Galois group.
-/

public section

open Polynomial

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-
**gal_zero_isSolvable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gal_zero_isSolvable : Group.IsSolvable (0 : F[X]).Gal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.instIsSolvableOfSubsingleton`：∀ (G : Type u_1) [inst : Group G] [S
ubsingleton G], Group.IsSolvable G
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem gal_zero_isSolvable : Group.IsSolvable (0 : F[X]).Gal := by infer_instance
/-
**gal_one_isSolvable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gal_one_isSolvable : Group.IsSolvable (1 : F[X]).Gal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.instIsSolvableOfSubsingleton`：∀ (G : Type u_1) [inst : Group G] [S
ubsingleton G], Group.IsSolvable G
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem gal_one_isSolvable : Group.IsSolvable (1 : F[X]).Gal := by infer_instance
/-
**gal_C_isSolvable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gal_C_isSolvable (x : F) : Group.IsSolvable (C x).Gal
参数：x : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.instIsSolvableOfSubsingleton`：∀ (G : Type u_1) [inst : Group G] [S
ubsingleton G], Group.IsSolvable G
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem gal_C_isSolvable (x : F) : Group.IsSolvable (C x).Gal := by infer_instance
/-
**gal_X_isSolvable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gal_X_isSolvable : Group.IsSolvable (X : F[X]).Gal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.instIsSolvableOfSubsingleton`：∀ (G : Type u_1) [inst : Group G] [S
ubsingleton G], Group.IsSolvable G
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem gal_X_isSolvable : Group.IsSolvable (X : F[X]).Gal := by infer_instance
/-
**gal_X_sub_C_isSolvable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gal_X_sub_C_isSolvable (x : F) : Group.IsSolvable (X - C x).Gal
参数：x : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.instIsSolvableOfSubsingleton`：∀ (G : Type u_1) [inst : Group G] [S
ubsingleton G], Group.IsSolvable G
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem gal_X_sub_C_isSolvable (x : F) : Group.IsSolvable (X - C x).Gal := by infer_instance
/-
**gal_X_pow_isSolvable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gal_X_pow_isSolvable (n : Nat) : Group.IsSolvable (X ^ n : F[X]).Gal
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.instIsSolvableOfSubsingleton`：∀ (G : Type u_1) [inst : Group G] [S
ubsingleton G], Group.IsSolvable G
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem gal_X_pow_isSolvable (n : ℕ) : Group.IsSolvable (X ^ n : F[X]).Gal := by infer_instance
/-
**gal_mul_isSolvable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gal_mul_isSolvable {p q : F[X]} (_ : Group.IsSolvable p.Gal) (_ : Group.Is
Solvable q.Gal) : Group.IsSolvable (p * q).Gal
参数：_ : Group.IsSolvable p.Gal；_ : Group.IsSolvable q.Gal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.isSolvable_of_isSolvable_injective`：isSolvable_of_isSolvable_injec
tive (hf : Function.Injective f) [IsSolvable G'] : IsSolvable G
· 使用定理 `Polynomial.Gal.restrictProd_injective`：restrictProd_injective : Function
.Injective (restrictProd p q)
· 使用定理 `Group.instIsSolvableProd`：∀ {G : Type u_1} [inst : Group G] {G' : Type u
_3} [inst_1 : Group G'] [Group.IsSolvable G] [Group.IsSolvable G'],   Group.IsSo
lvable (G × G'…
-/
theorem gal_mul_isSolvable {p q : F[X]} (_ : Group.IsSolvable p.Gal) (_ : Group.IsSolvable q.Gal) :
    Group.IsSolvable (p * q).Gal :=
  Group.isSolvable_of_isSolvable_injective (Gal.restrictProd_injective p q)
/-
**gal_prod_isSolvable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gal_prod_isSolvable {s : Multiset F[X]} (hs : forall p in s, Group.IsSolva
ble (Gal p)) : Group.IsSolvable s.prod.Gal
参数：hs : forall p in s, Group.IsSolvable (Gal p)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on'`：induction_on' {p : Multiset α -> Prop} (S : Mult
iset α) (h₁ : p 0) (h₂ : forall {a s}, a in S -> s subseteq S -> p s -> p (inser
t a s)) : p …
· 使用定理 `gal_one_isSolvable`：gal_one_isSolvable : Group.IsSolvable (1 : F[X]).Gal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.insert_eq_cons`：insert_eq_cons (a : α) (s : Multiset α) : inser
t a s = a ::ₘ s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `gal_mul_isSolvable`：gal_mul_isSolvable {p q : F[X]} (_ : Group.IsSolvabl
e p.Gal) (_ : Group.IsSolvable q.Gal) : Group.IsSolvable (p * q).Gal
-/
theorem gal_prod_isSolvable {s : Multiset F[X]} (hs : ∀ p ∈ s, Group.IsSolvable (Gal p)) :
    Group.IsSolvable s.prod.Gal := by
  apply Multiset.induction_on' s
  · exact gal_one_isSolvable
  · intro p t hps _ ht
    rw [Multiset.insert_eq_cons, Multiset.prod_cons]
    exact gal_mul_isSolvable (hs p hps) ht
/-
**gal_isSolvable_of_splits** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gal_isSolvable_of_splits {p q : F[X]} (_ : Fact ((p.map (algebraMap F q.Sp
littingField)).Splits)) (hq : Group.IsSolvable q.Gal) : Group.IsSolvable p.Gal
参数：_ : Fact ((p.map (algebraMap F q.SplittingField)).Splits)；hq : Group.IsSolvab
le q.Gal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.isSolvable_of_surjective`：isSolvable_of_surjective (hf : Function.
Surjective f) [IsSolvable G] : IsSolvable G'
· 使用定理 `Polynomial.Gal.instIsScalarTowerSplittingField`：∀ {F : Type u_1} [inst :
 Field F] (p : Polynomial F) (E : Type u_2) [inst_1 : Field E] [inst_2 : Algebra
 F E]   [h : Fact (Polynomial.map (a…
· 使用定理 `AlgEquiv.restrictNormalHom_surjective`：AlgEquiv.restrictNormalHom_surjec
tive [Normal F K₁] [Normal F E] : Function.Surjective (AlgEquiv.restrictNormalHo
m K₁ : Gal(E/F) -> K₁ ≃ₐ[F]…
-/
theorem gal_isSolvable_of_splits {p q : F[X]}
    (_ : Fact ((p.map (algebraMap F q.SplittingField)).Splits)) (hq : Group.IsSolvable q.Gal) :
    Group.IsSolvable p.Gal :=
  haveI : Group.IsSolvable (q.SplittingField ≃ₐ[F] q.SplittingField) := hq
  Group.isSolvable_of_surjective (AlgEquiv.restrictNormalHom_surjective q.SplittingField)
/-
**gal_isSolvable_tower** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gal_isSolvable_tower (p q : F[X]) (hpq : (p.map (algebraMap F q.SplittingF
ield)).Splits) (hp : Group.IsSolvable p.Gal) (hq : Group.IsSolvable (q.map (alge
braMap F p.SplittingField)).Gal) : Group.IsSolvable q.Gal
参数：p q : F[X]；hpq : (p.map (algebraMap F q.SplittingField)).Splits；hp : Group.Is
Solvable p.Gal；hq : Group.IsSolvable (q.map (algebraMap F p.SplittingField)).Gal
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Gal.instIsScalarTowerSplittingField`：∀ {F : Type u_1} [inst :
 Field F] (p : Polynomial F) (E : Type u_2) [inst_1 : Field E] [inst_2 : Algebra
 F E]   [h : Fact (Polynomial.map (a…
· 使用定理 `Polynomial.IsSplittingField.splittingField`：∀ {K : Type v} [inst : Field
 K] (f : Polynomial K), Polynomial.IsSplittingField K f.SplittingField f
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
· 使用定理 `Group.isSolvable_of_isSolvable_injective`：isSolvable_of_isSolvable_injec
tive (hf : Function.Injective f) [IsSolvable G'] : IsSolvable G
· 使用定理 `isSolvable_of_isScalarTower`：isSolvable_of_isScalarTower [Normal F K₁] [
h1 : Group.IsSolvable (K₁ ≃ₐ[F] K₁)] [h2 : Group.IsSolvable (E ≃ₐ[K₁] E)] : Grou
p.IsSolvable Gal(…
-/
theorem gal_isSolvable_tower (p q : F[X]) (hpq : (p.map (algebraMap F q.SplittingField)).Splits)
    (hp : Group.IsSolvable p.Gal)
    (hq : Group.IsSolvable (q.map (algebraMap F p.SplittingField)).Gal) :
    Group.IsSolvable q.Gal := by
  let K := p.SplittingField
  let L := q.SplittingField
  have : Fact ((p.map (algebraMap F L)).Splits) := ⟨hpq⟩
  let ϕ : Gal(L/K) ≃* (q.map (algebraMap F K)).Gal :=
    (IsSplittingField.algEquiv L (q.map (algebraMap F K))).autCongr
  have ϕ_inj : Function.Injective ϕ.toMonoidHom := ϕ.injective
  have : Group.IsSolvable Gal(K/F) := hp
  have : Group.IsSolvable Gal(L/K) := Group.isSolvable_of_isSolvable_injective ϕ_inj
  exact isSolvable_of_isScalarTower F p.SplittingField q.SplittingField

section GalXPowSubC

set_option backward.isDefEq.respectTransparency false in
/-
**gal_X_pow_sub_one_isSolvable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gal_X_pow_sub_one_isSolvable (n : Nat) : Group.IsSolvable (X ^ n - 1 : F[X
]).Gal
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `gal_zero_isSolvable`：gal_zero_isSolvable : Group.IsSolvable (0 : F[X]).G
al
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Polynomial.X_pow_sub_C_ne_zero`：X_pow_sub_C_ne_zero {n : Nat} (hn : 0 < 
n) (a : R) : (X : R[X]) ^ n - C a != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Group.isSolvable_of_comm`：isSolvable_of_comm {G : Type*} [hG : Group G] 
(h : forall a b : G, a * b = b * a) : IsSolvable G
· 使用定理 `Polynomial.Gal.ext`：ext {σ τ : p.Gal} (h : forall x in p.rootSet p.Split
tingField, σ x = τ x) : σ = τ
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `map_rootsOfUnity_eq_pow_self`：map_rootsOfUnity_eq_pow_self [FunLike F R 
R] [MonoidHomClass F R R] (σ : F) (ζ : rootsOfUnity k R) : exists m : Nat, σ (ζ 
: Rˣ) = ((ζ : Rˣ) …
· 使用定理 `NeZero.pnat`：∀ {a : ℕ+}, NeZero ↑a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Polynomial.mem_rootSet_of_ne`：mem_rootSet_of_ne {p : T[X]} {S : Type*} [
IsDomain T] [CommRing S] [IsDomain S] [Algebra T S] [Module.IsTorsionFree T S] (
hp : p != 0) {a : …
· 使用定理 `Polynomial.IsSplittingField.instIsTorsionFreeSplittingField`：∀ {K : Type
 v} [inst : Field K] (f : Polynomial K), Module.IsTorsionFree K f.SplittingField
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.aeval_X_pow`：aeval_X_pow {n : Nat} : aeval x ((X : R[X]) ^ n)
 = x ^ n
· 使用定理 `Polynomial.aeval_one`：aeval_one : aeval x (1 : R[X]) = 1
（共 37 条，此处仅展示前 30 条）
-/
theorem gal_X_pow_sub_one_isSolvable (n : ℕ) : Group.IsSolvable (X ^ n - 1 : F[X]).Gal := by
  by_cases hn : n = 0
  · rw [hn, pow_zero, sub_self]
    exact gal_zero_isSolvable
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn
  have hn'' : (X ^ n - 1 : F[X]) ≠ 0 := X_pow_sub_C_ne_zero hn' 1
  apply Group.isSolvable_of_comm
  intro σ τ
  ext a ha
  simp only [mem_rootSet_of_ne hn'', map_sub, aeval_X_pow, aeval_one, sub_eq_zero] at ha
  have key : ∀ σ : (X ^ n - 1 : F[X]).Gal, ∃ m : ℕ, σ a = a ^ m := by
    intro σ
    lift n to ℕ+ using hn'
    exact map_rootsOfUnity_eq_pow_self σ.toAlgHom (rootsOfUnity.mkOfPowEq a ha)
  obtain ⟨c, hc⟩ := key σ
  obtain ⟨d, hd⟩ := key τ
  rw [σ.mul_apply, τ.mul_apply, hc, map_pow, hd, map_pow, hc, ← pow_mul, pow_mul']

set_option backward.isDefEq.respectTransparency false in
/-
**gal_X_pow_sub_C_isSolvable_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gal_X_pow_sub_C_isSolvable_aux (n : Nat) (a : F) (h : ((X ^ n - 1 : F[X]).
map (RingHom.id F)).Splits) : Group.IsSolvable (X ^ n - C a).Gal
参数：n : Nat；a : F；h : ((X ^ n - 1 : F[X]).map (RingHom.id F)).Splits。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `gal_X_pow_isSolvable`：gal_X_pow_isSolvable (n : Nat) : Group.IsSolvable 
(X ^ n : F[X]).Gal
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Polynomial.C_sub`：C_sub : C (a - b) = C a - C b
· 使用定理 `gal_C_isSolvable`：gal_C_isSolvable (x : F) : Group.IsSolvable (C x).Gal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Polynomial.X_pow_sub_C_ne_zero`：X_pow_sub_C_ne_zero {n : Nat} (hn : 0 < 
n) (a : R) : (X : R[X]) ^ n - C a != 0
· 使用定理 `RingHom.mem_range`：mem_range {f : R ->+* S} {y : S} : y in f.range ↔ exi
sts x, f x = y
· 使用定理 `minpoly.mem_range_of_degree_eq_one`：mem_range_of_degree_eq_one (hx : (mi
npoly A x).degree = 1) : x in (algebraMap A B).range
· 使用定理 `Polynomial.Splits.degree_eq_one_of_irreducible`：∀ {R : Type u_1} [inst :
 Field R] {f : Polynomial R}, f.Splits → Irreducible f → f.degree = 1
· 使用定理 `Polynomial.Splits.of_dvd`：∀ {R : Type u_1} [inst : CommRing R] {f g : Po
lynomial R} [IsDomain R], g.Splits → g ≠ 0 → f ∣ g → f.Splits
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.map_ne_zero`：map_ne_zero {f : R ->+* S} (hp : p != 0) : p.map
 f != 0
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p
· 使用定理 `Polynomial.map_id`：map_id : p.map (RingHom.id _) = p
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
（共 63 条，此处仅展示前 30 条）
-/
theorem gal_X_pow_sub_C_isSolvable_aux (n : ℕ) (a : F)
    (h : ((X ^ n - 1 : F[X]).map (RingHom.id F)).Splits) : Group.IsSolvable (X ^ n - C a).Gal := by
  by_cases ha : a = 0
  · rw [ha, C_0, sub_zero]
    exact gal_X_pow_isSolvable n
  have ha' : algebraMap F (X ^ n - C a).SplittingField a ≠ 0 :=
    mt ((injective_iff_map_eq_zero _).mp (RingHom.injective _) a) ha
  by_cases hn : n = 0
  · rw [hn, pow_zero, ← C_1, ← C_sub]
    exact gal_C_isSolvable (1 - a)
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn
  have hn'' : X ^ n - C a ≠ 0 := X_pow_sub_C_ne_zero hn' a
  have hn''' : (X ^ n - 1 : F[X]) ≠ 0 := X_pow_sub_C_ne_zero hn' 1
  have mem_range : ∀ {c : (X ^ n - C a).SplittingField},
      (c ^ n = 1 → (∃ d, algebraMap F (X ^ n - C a).SplittingField d = c)) := fun {c} hc =>
    RingHom.mem_range.mp (minpoly.mem_range_of_degree_eq_one F c
      (Splits.degree_eq_one_of_irreducible (h.of_dvd (map_ne_zero hn''')
        (minpoly.dvd F c (by rwa [map_id, map_sub, sub_eq_zero, aeval_X_pow, aeval_one])))
          (minpoly.irreducible ((SplittingField.instNormal (X ^ n - C a)).isIntegral c))))
  apply Group.isSolvable_of_comm
  intro σ τ
  ext b hb
  rw [mem_rootSet_of_ne hn'', map_sub, aeval_X_pow, aeval_C, sub_eq_zero] at hb
  have hb' : b ≠ 0 := by
    intro hb'
    rw [hb', zero_pow hn] at hb
    exact ha' hb.symm
  have key : ∀ σ : (X ^ n - C a).Gal, ∃ c, σ b = b * algebraMap F _ c := by
    intro σ
    have key : (σ b / b) ^ n = 1 := by rw [div_pow, ← map_pow, hb, σ.commutes, div_self ha']
    obtain ⟨c, hc⟩ := mem_range key
    use c
    rw [hc, mul_div_cancel₀ (σ b) hb']
  obtain ⟨c, hc⟩ := key σ
  obtain ⟨d, hd⟩ := key τ
  rw [σ.mul_apply, τ.mul_apply, hc, map_mul, τ.commutes, hd, map_mul, σ.commutes, hc,
    mul_assoc, mul_assoc, mul_right_inj' hb', mul_comm]
/-
**splits_X_pow_sub_one_of_X_pow_sub_C** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：splits_X_pow_sub_one_of_X_pow_sub_C {F : Type*} [Field F] {E : Type*} [Fie
ld E] (i : F ->+* E) (n : Nat) {a : F} (ha : a != 0) (h : ((X ^ n - C a).map i).
Splits) : ((X ^ n - 1 : F[X]).map i).Splits
参数：i : F ->+* E；n : Nat；ha : a != 0；h : ((X ^ n - C a).map i).Splits。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `ne_of_eq_of_ne`：ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ 
: b != c) : a != c
· 使用定理 `Polynomial.degree_X_pow_sub_C`：degree_X_pow_sub_C {n : Nat} (hn : 0 < n)
 (a : R) : degree ((X : R[X]) ^ n - C a) = n
· 使用定理 `WithBot.coe_eq_coe`：coe_eq_coe : (a : WithBot α) = b ↔ a = b
· 使用定理 `Polynomial.Splits.exists_eval_eq_zero`：∀ {R : Type u_1} [inst : CommRing
 R] {f : Polynomial R}, f.Splits → f.degree ≠ 0 → ∃ a, Polynomial.eval a f = 0
· 使用定理 `Polynomial.degree_map`：degree_map (p : R[X]) (f : R ->+* S) : (p.map f).
degree = p.degree
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Polynomial.eval₂_C`：eval₂_C : (C a).eval₂ f x = f a
· 使用定理 `Polynomial.eval₂_X_pow`：eval₂_X_pow {n : Nat} : (X ^ n).eval₂ f x = x ^ 
n
· 使用定理 `Polynomial.eval₂_sub`：eval₂_sub {S} [Ring S] (f : R ->+* S) {x : S} : (p
 - q).eval₂ f x = p.eval₂ f x - q.eval₂ f x
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
（共 70 条，此处仅展示前 30 条）
-/
theorem splits_X_pow_sub_one_of_X_pow_sub_C {F : Type*} [Field F] {E : Type*} [Field E]
    (i : F →+* E) (n : ℕ) {a : F} (ha : a ≠ 0) (h : ((X ^ n - C a).map i).Splits) :
    ((X ^ n - 1 : F[X]).map i).Splits := by
  have ha' : i a ≠ 0 := mt ((injective_iff_map_eq_zero i).mp i.injective a) ha
  by_cases hn : n = 0
  · simp [hn]
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn
  have hn'' : (X ^ n - C a).degree ≠ 0 :=
    ne_of_eq_of_ne (degree_X_pow_sub_C hn' a) (mt WithBot.coe_eq_coe.mp hn)
  obtain ⟨b, hb⟩ := Splits.exists_eval_eq_zero h (by rwa [degree_map])
  rw [eval_map, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at hb
  have hb' : b ≠ 0 := by
    intro hb'
    rw [hb', zero_pow hn] at hb
    exact ha' hb.symm
  let s := ((X ^ n - C a).map i).roots
  have hs : _ = _ * (s.map _).prod := h.eq_prod_roots
  rw [leadingCoeff_map, leadingCoeff_X_pow_sub_C hn', RingHom.map_one, C_1, one_mul] at hs
  have hs' : Multiset.card s = n := by
    rw [← h.natDegree_eq_card_roots, natDegree_map, natDegree_X_pow_sub_C]
  rw [splits_iff_exists_multiset, leadingCoeff_map]
  use (s.map fun c ↦ c / b)
  rw [leadingCoeff_X_pow_sub_one hn', map_one, C_1, one_mul, Multiset.map_map]
  have C_mul_C : C (i a⁻¹) * C (i a) = 1 := by
    rw [← C_mul, ← i.map_mul, inv_mul_cancel₀ ha, i.map_one, C_1]
  have key1 : (X ^ n - 1 : F[X]).map i = C (i a⁻¹) * ((X ^ n - C a).map i).comp (C b * X) := by
    rw [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C,
      Polynomial.map_one, sub_comp, pow_comp, X_comp, C_comp, mul_pow, ← C_pow, hb, mul_sub, ←
      mul_assoc, C_mul_C, one_mul]
  have key2 : ((fun q : E[X] => q.comp (C b * X)) ∘ fun c : E => X - C c) = fun c : E =>
      C b * (X - C (c / b)) := by
    ext1 c
    dsimp only [Function.comp_apply]
    rw [sub_comp, X_comp, C_comp, mul_sub, ← C_mul, mul_div_cancel₀ c hb']
  rw [key1, hs, multiset_prod_comp, Multiset.map_map, key2, Multiset.prod_map_mul,
    Function.const_def (α := E) (y := C b), Multiset.map_const, Multiset.prod_replicate,
    hs', ← C_pow, hb, ← mul_assoc, C_mul_C, one_mul]
  rfl
/-
**gal_X_pow_sub_C_isSolvable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gal_X_pow_sub_C_isSolvable (n : Nat) (x : F) : Group.IsSolvable (X ^ n - C
 x).Gal
参数：n : Nat；x : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `gal_X_pow_isSolvable`：gal_X_pow_isSolvable (n : Nat) : Group.IsSolvable 
(X ^ n : F[X]).Gal
· 使用定理 `gal_isSolvable_tower`：gal_isSolvable_tower (p q : F[X]) (hpq : (p.map (a
lgebraMap F q.SplittingField)).Splits) (hp : Group.IsSolvable p.Gal) (hq : Group
.IsSolvabl…
· 使用定理 `splits_X_pow_sub_one_of_X_pow_sub_C`：splits_X_pow_sub_one_of_X_pow_sub_C
 {F : Type*} [Field F] {E : Type*} [Field E] (i : F ->+* E) (n : Nat) {a : F} (h
a : a != 0) (h : ((X ^ n …
· 使用定理 `Polynomial.SplittingField.splits`：∀ {K : Type v} [inst : Field K] (f : P
olynomial K), (Polynomial.map (algebraMap K f.SplittingField) f).Splits
· 使用定理 `gal_X_pow_sub_one_isSolvable`：gal_X_pow_sub_one_isSolvable (n : Nat) : G
roup.IsSolvable (X ^ n - 1 : F[X]).Gal
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `gal_X_pow_sub_C_isSolvable_aux`：gal_X_pow_sub_C_isSolvable_aux (n : Nat)
 (a : F) (h : ((X ^ n - 1 : F[X]).map (RingHom.id F)).Splits) : Group.IsSolvable
 (X ^ n - C a).Gal
· 使用定理 `Polynomial.map_id`：map_id : p.map (RingHom.id _) = p
· 使用定理 `Polynomial.map_one`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S), Polynomial.map f 1 = 1
-/
theorem gal_X_pow_sub_C_isSolvable (n : ℕ) (x : F) : Group.IsSolvable (X ^ n - C x).Gal := by
  by_cases hx : x = 0
  · rw [hx, C_0, sub_zero]
    exact gal_X_pow_isSolvable n
  apply gal_isSolvable_tower (X ^ n - 1) (X ^ n - C x)
  · exact splits_X_pow_sub_one_of_X_pow_sub_C _ n hx (SplittingField.splits _)
  · exact gal_X_pow_sub_one_isSolvable n
  · rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
    apply gal_X_pow_sub_C_isSolvable_aux
    rw [map_id]
    have key := SplittingField.splits (X ^ n - 1 : F[X])
    rwa [Polynomial.map_sub, Polynomial.map_pow, map_X,
      Polynomial.map_one] at key

end GalXPowSubC

variable (F E) in
/-- The intermediate field of elements solvable by radicals, defined as the smallest subfield which
is closed under `n`-th roots. -/
/-
**solvableByRad** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：solvableByRad : IntermediateField F E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intermediate field of elements solvable by radicals, defined as the smallest
 subfield which
is closed under `n`-th roots.
-/
def solvableByRad : IntermediateField F E :=
  sInf {s | ∀ x, ∀ n ≠ 0, x ^ n ∈ s → x ∈ s}

variable (F) in
/-- Inductive definition of solvable by radicals -/
@[deprecated solvableByRad (since := "2026-02-28")]
/-
**IsSolvableByRad** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) → {E : Type u_2} → [inst : Field F] → [inst_1 : Field E] → 
[Algebra F E] → E → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inductive definition of solvable by radicals
-/
inductive IsSolvableByRad : E → Prop
  | base (α : F) : IsSolvableByRad (algebraMap F E α)
  | add (α β : E) : IsSolvableByRad α → IsSolvableByRad β → IsSolvableByRad (α + β)
  | neg (α : E) : IsSolvableByRad α → IsSolvableByRad (-α)
  | mul (α β : E) : IsSolvableByRad α → IsSolvableByRad β → IsSolvableByRad (α * β)
  | inv (α : E) : IsSolvableByRad α → IsSolvableByRad α⁻¹
  | rad (α : E) (n : ℕ) (hn : n ≠ 0) : IsSolvableByRad (α ^ n) → IsSolvableByRad α
/-
**solvableByRad_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：solvableByRad_le {s : IntermediateField F E} (H : forall x, forall n != 0,
 x ^ n in s -> x in s) : solvableByRad F E <= s
参数：H : forall x, forall n != 0, x ^ n in s -> x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
-/
theorem solvableByRad_le {s : IntermediateField F E} (H : ∀ x, ∀ n ≠ 0, x ^ n ∈ s → x ∈ s) :
    solvableByRad F E ≤ s :=
  sInf_le H
/-
**solvableByRad.rad_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：solvableByRad.rad_mem {x : E} {n : Nat} (hn : n != 0) (hx : x ^ n in solva
bleByRad F E) : x in solvableByRad F E
参数：hn : n != 0；hx : x ^ n in solvableByRad F E。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem solvableByRad.rad_mem {x : E} {n : ℕ} (hn : n ≠ 0) (hx : x ^ n ∈ solvableByRad F E) :
    x ∈ solvableByRad F E := by
  grind [solvableByRad]

variable (F E) in
/-
**solvableByRad_le_algClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：solvableByRad_le_algClosure : solvableByRad F E <= algebraicClosure F E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `solvableByRad_le`：solvableByRad_le {s : IntermediateField F E} (H : fora
ll x, forall n != 0, x ^ n in s -> x in s) : solvableByRad F E <= s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_algebraicClosure_iff`：mem_algebraicClosure_iff {x : E} : x in algebr
aicClosure F E ↔ IsAlgebraic F x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Polynomial.leadingCoeff_X_pow`：leadingCoeff_X_pow (n : Nat) : leadingCoe
ff ((X : R[X]) ^ n) = 1
· 使用定理 `Polynomial.leadingCoeff_comp`：leadingCoeff_comp (hq : natDegree q != 0) 
: leadingCoeff (p.comp q) = leadingCoeff p * leadingCoeff q ^ natDegree p
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.natDegree_X_pow`：natDegree_X_pow : natDegree ((X : R[X]) ^ n)
 = n
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.aeval_comp`：aeval_comp {A : Type*} [Semiring A] [Algebra R A]
 (x : A) : aeval x (p.comp q) = aeval (aeval x q) p
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
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
-/
theorem solvableByRad_le_algClosure : solvableByRad F E ≤ algebraicClosure F E := by
  refine solvableByRad_le fun x n hn hx ↦ ?_
  rw [mem_algebraicClosure_iff] at hx ⊢
  obtain ⟨p, h1, h2⟩ := hx
  refine ⟨p.comp (X ^ n), ⟨fun h ↦ h1 (leadingCoeff_eq_zero.mp ?_), ?_⟩⟩
  · rwa [← leadingCoeff_eq_zero, leadingCoeff_comp, leadingCoeff_X_pow, one_pow, mul_one] at h
    rwa [natDegree_X_pow]
  · simpa [aeval_comp]
/-
**isAlgebraic_solvableByRad** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAlgebraic_solvableByRad : (solvableByRad F E).IsAlgebraic
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_algebraicClosure_iff`：mem_algebraicClosure_iff {x : E} : x in algebr
aicClosure F E ↔ IsAlgebraic F x
· 使用定理 `solvableByRad_le_algClosure`：solvableByRad_le_algClosure : solvableByRad
 F E <= algebraicClosure F E
-/
theorem isAlgebraic_solvableByRad : (solvableByRad F E).IsAlgebraic :=
  fun _ hx ↦ mem_algebraicClosure_iff.1 (solvableByRad_le_algClosure _ _ hx)
/-
**isIntegral_of_mem_solvableByRad** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegral_of_mem_solvableByRad {x : E} (hx : x in solvableByRad F E) : Is
Integral F x
参数：hx : x in solvableByRad F E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Field K] [in
st_1 : Ring A] [inst_2 : Algebra K A] {x : A},   IsAlgebraic K x → IsIntegral K 
x
· 使用定理 `isAlgebraic_solvableByRad`：isAlgebraic_solvableByRad : (solvableByRad F 
E).IsAlgebraic
-/
theorem isIntegral_of_mem_solvableByRad {x : E} (hx : x ∈ solvableByRad F E) : IsIntegral F x :=
  (isAlgebraic_solvableByRad _ hx).isIntegral

@[deprecated (since := "2026-02-28")]
alias solvableByRad.isIntegral := isIntegral_of_mem_solvableByRad

/-- An induction principle for `solvableByRad`. -/
@[elab_as_elim]
/-
**solvableByRad.induction** 是 Mathlib 中的一个定理，位于命名空间 `solvableByRad`。
形式化陈述：∀ {F : Type u_1} {E : Type u_2} [inst : Field F] [inst_1 : Field E] [inst_
2 : Algebra F E]   (motive : (x : E) → x ∈ solvableByRad F E → Prop),   (∀ (x : 
F), motive ((algebraMap F E) x) ⋯) →     (∀ (x y : E) (hx : x ∈ solvableByRad F 
E) (hy : y ∈ solvableByRad F E),         motive x hx → motive y hy → motive (x +
 y) ⋯) →       (∀ (x y : E) (hx : x ∈ solvableByRad F E) (hy : y ∈ solvableByRad
 F E),           motive x hx → motive y hy → motive (x * y) ⋯) →         (∀ (n :
 ℕ) (x : E) (hn : n ≠ 0) (hx : x ^ n ∈ solvableByRad F E), motive (x ^ n) hx → m
otive x ⋯) →           ∀ {x : E} (hx : x ∈ solvableByRad F E), motive x hx
参数：motive : (x : E) → x ∈ solvableByRad F E → Prop；∀ (x : F), motive ((algebraMa
p F E) x) ⋯；∀ (x y : E) (hx : x ∈ solvableByRad F E) (hy : y ∈ solvableByRad F E
),         motive x hx → motive y hy → motive (x + y) ⋯；∀ (x y : E) (hx : x ∈ so
lvableByRad F E) (hy : y ∈ solvableByRad F E),           motive x hx → motive y 
hy → motive (x * y) ⋯；∀ (n : ℕ) (x : E) (hn : n ≠ 0) (hx : x ^ n ∈ solvableByRad
 F E), motive (x ^ n) hx → motive x ⋯；hx : x ∈ solvableByRad F E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `algebraMap_mem`：∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : SetLike 
S A]…
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `solvableByRad.rad_mem`：solvableByRad.rad_mem {x : E} {n : Nat} (hn : n !
= 0) (hx : x ^ n in solvableByRad F E) : x in solvableByRad F E
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `isAlgebraic_solvableByRad`：isAlgebraic_solvableByRad : (solvableByRad F 
E).IsAlgebraic
· 使用定理 `solvableByRad_le`：solvableByRad_le {s : IntermediateField F E} (H : fora
ll x, forall n != 0, x ^ n in s -> x in s) : solvableByRad F E <= s

--- 原说明 ---
An induction principle for `solvableByRad`.
-/
protected theorem solvableByRad.induction (motive : ∀ x, x ∈ solvableByRad F E → Prop)
    (mem : ∀ x, motive (algebraMap F E x) (algebraMap_mem _ _))
    (add : ∀ x y (hx : x ∈ solvableByRad F E) (hy : y ∈ solvableByRad F E),
      motive x hx → motive y hy → motive (x + y) (add_mem hx hy))
    (mul : ∀ x y (hx : x ∈ solvableByRad F E) (hy : y ∈ solvableByRad F E),
      motive x hx → motive y hy → motive (x * y) (mul_mem hx hy))
    (rad : ∀ n x (hn : n ≠ 0) (hx : x ^ n ∈ solvableByRad F E),
      motive (x ^ n) hx → motive x (rad_mem hn hx))
    {x : E} (hx : x ∈ solvableByRad F E) : motive x hx := by
  let s : Subalgebra F E :=
  { carrier := {x | ∃ hx : x ∈ solvableByRad F E, motive x hx}
    algebraMap_mem' a := ⟨algebraMap_mem _ a, mem a⟩
    add_mem' := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ ↦ ⟨add_mem ha hb, add _ _ ha hb ha' hb'⟩
    mul_mem' := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ ↦ ⟨mul_mem ha hb, mul _ _ ha hb ha' hb'⟩ }
  let t : IntermediateField F E := Subalgebra.IsAlgebraic.toIntermediateField (S := s) <| by
    rintro x ⟨hx, hx'⟩
    apply isAlgebraic_solvableByRad
    exact hx
  have ht (x n) (hn : n ≠ 0) : x ^ n ∈ t → x ∈ t := by
    rintro ⟨hx, hx'⟩
    exact ⟨rad_mem hn hx, rad _ _ hn hx hx'⟩
  obtain ⟨_, h⟩ := solvableByRad_le (s := t) ht hx
  exact h
/-
**induction_rad** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem induction_rad {x : E} (hx : x ∈ solvableByRad F E) {n : ℕ} (hn : n ≠ 0)
    (hα : Group.IsSolvable (minpoly F (x ^ n)).Gal) : Group.IsSolvable (minpoly F x).Gal := by
  let p := minpoly F (x ^ n)
  have hp : p.comp (X ^ n) ≠ 0 := by
    intro h
    rcases comp_eq_zero_iff.mp h with h' | h'
    · exact minpoly.ne_zero (isIntegral_of_mem_solvableByRad (pow_mem hx n)) h'
    · exact hn (by rw [← @natDegree_C F, ← h'.2, natDegree_X_pow])
  apply gal_isSolvable_of_splits
  · exact ⟨(SplittingField.splits (p.comp (X ^ n))).of_dvd (map_ne_zero hp)
      ((map_dvd_map' _).mpr (minpoly.dvd F x (by rw [aeval_comp, aeval_X_pow, minpoly.aeval])))⟩
  · refine gal_isSolvable_tower p (p.comp (X ^ n)) ?_ hα ?_
    · exact Gal.splits_in_splittingField_of_comp _ _ (by rwa [natDegree_X_pow])
    · obtain ⟨s, hs⟩ := splits_iff_exists_multiset.1 (SplittingField.splits p)
      rw [map_comp, Polynomial.map_pow, map_X, hs, mul_comp, C_comp]
      apply gal_mul_isSolvable (gal_C_isSolvable _)
      rw [multiset_prod_comp]
      apply gal_prod_isSolvable
      intro q hq
      rw [Multiset.mem_map] at hq
      obtain ⟨q, hq, rfl⟩ := hq
      rw [Multiset.mem_map] at hq
      obtain ⟨q, _, rfl⟩ := hq
      rw [sub_comp, X_comp, C_comp]
      exact gal_X_pow_sub_C_isSolvable n q

open IntermediateField
/-
**induction_step** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem induction_step {x y z : E}
    (hx : x ∈ solvableByRad F E) (hy : y ∈ solvableByRad F E) (hz : z ∈ solvableByRad F E)
    (hx' : Group.IsSolvable (minpoly F x).Gal) (hy' : Group.IsSolvable (minpoly F y).Gal)
    (hz' : z ∈ F⟮x, y⟯) : Group.IsSolvable (minpoly F z).Gal := by
  let p := minpoly F x
  let q := minpoly F y
  have hpq := SplittingField.splits (p * q)
  rw [Polynomial.map_mul,
    splits_mul (map_ne_zero (minpoly.ne_zero (isIntegral_of_mem_solvableByRad hx)))
      (map_ne_zero (minpoly.ne_zero (isIntegral_of_mem_solvableByRad hy)))] at hpq
  have f : ↥F⟮x, y⟯ →ₐ[F] (p * q).SplittingField :=
    Classical.choice <| nonempty_algHom_adjoin_of_splits <| by
      rintro a (rfl | rfl)
      · exact ⟨isIntegral_of_mem_solvableByRad hx, hpq.1⟩
      · exact ⟨isIntegral_of_mem_solvableByRad hy, hpq.2⟩
  have key : minpoly F z = minpoly F (f ⟨z, hz'⟩) := by
    refine minpoly.eq_of_irreducible_of_monic
      (minpoly.irreducible (isIntegral_of_mem_solvableByRad hz)) ?_
      (minpoly.monic (isIntegral_of_mem_solvableByRad hz))
    rw [aeval_algHom_apply, map_eq_zero]
    apply (algebraMap (↥F⟮x, y⟯) E).injective
    simp [← aeval_algebraMap_apply]
  rw [key]
  refine gal_isSolvable_of_splits ⟨Normal.splits ?_ (f ⟨z, hz'⟩)⟩ (gal_mul_isSolvable hx' hy')
  infer_instance
/-
**isSolvable_gal_minpoly** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSolvable_gal_minpoly {x : E} (hx : x in solvableByRad F E) : Group.IsSol
vable (minpoly F x).Gal
参数：hx : x in solvableByRad F E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `solvableByRad.induction`：∀ {F : Type u_1} {E : Type u_2} [inst : Field F
] [inst_1 : Field E] [inst_2 : Algebra F E]   (motive : (x : E) → x ∈ solvableBy
Rad F E → Pro…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minpoly.eq_X_sub_C`：eq_X_sub_C (a : A) : minpoly A (algebraMap A B a) = 
X - C a
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Group.instIsSolvableOfSubsingleton`：∀ (G : Type u_1) [inst : Group G] [S
ubsingleton G], Group.IsSolvable G
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `_private.Mathlib.FieldTheory.AbelRuffini.0.induction_step`：∀ {F : Type u
_1} {E : Type u_2} [inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] {x
 y z : E},   x ∈ solvableByRad F E →     y ∈ so…
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `_private.Mathlib.FieldTheory.AbelRuffini.0.induction_rad`：∀ {F : Type u_
1} {E : Type u_2} [inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] {x 
: E},   x ∈ solvableByRad F E →     ∀ {n : ℕ},…
· 使用定理 `solvableByRad.rad_mem`：solvableByRad.rad_mem {x : E} {n : Nat} (hn : n !
= 0) (hx : x ^ n in solvableByRad F E) : x in solvableByRad F E
-/
theorem isSolvable_gal_minpoly {x : E} (hx : x ∈ solvableByRad F E) :
    Group.IsSolvable (minpoly F x).Gal := by
  induction hx using solvableByRad.induction with
  | mem y => rw [minpoly.eq_X_sub_C E]; infer_instance
  | add y z hy hz hy' hz' =>
    apply induction_step hy hz (add_mem hy hz) hy' hz' (add_mem ..) <;> apply subset_adjoin <;> simp
  | mul y z hy hz hy' hz' =>
    apply induction_step hy hz (mul_mem hy hz) hy' hz' (mul_mem ..) <;> apply subset_adjoin <;> simp
  | rad n y hn hy hy' => exact induction_rad (solvableByRad.rad_mem hn hy) hn hy'

@[deprecated (since := "2026-02-28")]
alias solvableByRad.isSolvable := isSolvable_gal_minpoly

/-- **Abel-Ruffini Theorem** (one direction): An irreducible polynomial with a `solvableByRad` root
has a solvable Galois group. -/
/-
**isSolvable_gal_of_irreducible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSolvable_gal_of_irreducible {x : E} (hx : x in solvableByRad F E) {q : F
[X]} (q_irred : Irreducible q) (q_aeval : aeval x q = 0) : Group.IsSolvable q.Ga
l
参数：hx : x in solvableByRad F E；q_irred : Irreducible q；q_aeval : aeval x q = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `minpoly.eq_of_irreducible`：eq_of_irreducible [Nontrivial B] {p : A[X]} (
hp1 : Irreducible p) (hp2 : Polynomial.aeval x p = 0) : p * C p.leadingCoeff⁻¹ =
 minpoly A x
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `isSolvable_gal_minpoly`：isSolvable_gal_minpoly {x : E} (hx : x in solvab
leByRad F E) : Group.IsSolvable (minpoly F x).Gal
· 使用定理 `Group.isSolvable_of_surjective`：isSolvable_of_surjective (hf : Function.
Surjective f) [IsSolvable G] : IsSolvable G'
· 使用定理 `Polynomial.Gal.restrictDvd_surjective`：restrictDvd_surjective (hpq : p ∣
 q) (hq : q != 0) : Function.Surjective (restrictDvd hpq)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
**Abel-Ruffini Theorem** (one direction): An irreducible polynomial with a `solv
ableByRad` root
has a solvable Galois group.
-/
theorem isSolvable_gal_of_irreducible {x : E} (hx : x ∈ solvableByRad F E) {q : F[X]}
    (q_irred : Irreducible q) (q_aeval : aeval x q = 0) : Group.IsSolvable q.Gal := by
  have : Group.IsSolvable (q * C q.leadingCoeff⁻¹).Gal := by
    rw [minpoly.eq_of_irreducible q_irred q_aeval]
    exact isSolvable_gal_minpoly hx
  refine Group.isSolvable_of_surjective (Gal.restrictDvd_surjective ⟨C q.leadingCoeff⁻¹, rfl⟩ ?_)
  aesop

@[deprecated (since := "2026-02-28")]
alias solvableByRad.isSolvable' := isSolvable_gal_of_irreducible
