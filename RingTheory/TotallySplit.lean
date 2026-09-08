/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Flat.Rank
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Totally split algebras

An `R`-algebra `S` is finite (totally) split if it is isomorphic to `Fin n → R` for some `n`.
Geometrically, this corresponds to a trivial covering.

Every totally split algebra is finite étale and conversely, every finite étale covering is étale
locally totally split.

## Main results

- `Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`: If `S` is finite étale over `R` of
  some constant rank, there exists a faithfully flat, finite étale `R`-algebra `T` such that
  `T ⊗[R] S` is finite split.
-/

universe u

public section

open TensorProduct

/-- `S` is a finite, totally split `R`-algebra if `S` is isomorphic to `Fin n → R` for some `n`.
Geometrically, this is a trivial cover of degree `n`. -/
/-
**Algebra.IsFiniteSplit** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type u_1) → (S : Type u_2) → [inst : CommRing R] → [inst_1 : CommRing
 S] → [Algebra R S] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`S` is a finite, totally split `R`-algebra if `S` is isomorphic to `Fin n → R` f
or some `n`.
Geometrically, this is a trivial cover of degree `n`.
-/
class Algebra.IsFiniteSplit (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  nonempty_algEquiv_fun (R S) : ∃ n : ℕ, Nonempty (S ≃ₐ[R] Fin n → R)

namespace Algebra.IsFiniteSplit

variable {k R S : Type*} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra R S]

/-
**Algebra.IsFiniteSplit.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.IsFiniteSplit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {T : Type*} [CommRing T] [Algebra R T] [IsFiniteSplit R S] :
    IsFiniteSplit T (T ⊗[R] S) := by
  obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun R S
  refine ⟨n, ⟨?_⟩⟩
  exact (TensorProduct.congr AlgEquiv.refl e).trans
    ((TensorProduct.piRight R T T (fun _ : Fin n ↦ R)).trans <|
      AlgEquiv.piCongrRight fun i ↦ TensorProduct.rid R T T)
/-
**Algebra.IsFiniteSplit.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.IsFiniteSplit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} [Finite ι] : IsFiniteSplit R (ι → R) where
  nonempty_algEquiv_fun := by
    cases nonempty_fintype ι
    exact ⟨_, ⟨AlgEquiv.piCongrLeft' _ _ (Fintype.equivFin ι)⟩⟩
/-
**Algebra.IsFiniteSplit.of_algEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.IsFiniteS
plit`。
形式化陈述：of_algEquiv {S' : Type*} [CommRing S'] [Algebra R S'] (e : S ≃ₐ[R] S') [Is
FiniteSplit R S] : IsFiniteSplit R S'
参数：e : S ≃ₐ[R] S'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsFiniteSplit.nonempty_algEquiv_fun`：∀ (R : Type u_1) (S : Type 
u_2) {inst : CommRing R} {inst_1 : CommRing S} {inst_2 : Algebra R S}   [self : 
Algebra.IsFiniteSplit R S], ∃ n, …
-/
lemma of_algEquiv {S' : Type*} [CommRing S'] [Algebra R S'] (e : S ≃ₐ[R] S') [IsFiniteSplit R S] :
    IsFiniteSplit R S' := by
  obtain ⟨n, ⟨f⟩⟩ := nonempty_algEquiv_fun R S
  exact ⟨n, ⟨e.symm.trans f⟩⟩
/-
**Algebra.IsFiniteSplit.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.IsFiniteSplit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsFiniteSplit R R :=
  .of_algEquiv (AlgEquiv.funUnique (ι := Fin 1) _ _)
/-
**Algebra.IsFiniteSplit.of_subsingleton_top** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.I
sFiniteSplit`。
形式化陈述：of_subsingleton_top [Subsingleton S] : IsFiniteSplit R S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma of_subsingleton_top [Subsingleton S] : IsFiniteSplit R S :=
  ⟨0, ⟨default⟩⟩
/-
**Algebra.IsFiniteSplit.of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.IsFin
iteSplit`。
形式化陈述：of_subsingleton [Subsingleton R] : IsFiniteSplit R S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.codomain_trivial`：codomain_trivial (f : α ->+* β) [h : Subsingle
ton α] : Subsingleton β
· 使用引理 `Algebra.IsFiniteSplit.of_subsingleton_top`：of_subsingleton_top [Subsingl
eton S] : IsFiniteSplit R S
-/
lemma of_subsingleton [Subsingleton R] : IsFiniteSplit R S := by
  have : Subsingleton S := RingHom.codomain_trivial (algebraMap R S)
  exact of_subsingleton_top
/-
**Algebra.IsFiniteSplit.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.IsFiniteSplit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsFiniteSplit R S] : Module.Free R S := by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun R S
  exact Module.Free.of_equiv e.symm.toLinearEquiv
/-
**Algebra.IsFiniteSplit.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.IsFiniteSplit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsFiniteSplit R S] : Module.FinitePresentation R S := by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun R S
  apply Module.FinitePresentation.of_equiv e.symm.toLinearEquiv
/-
**Algebra.IsFiniteSplit.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.IsFiniteSplit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsFiniteSplit R S] : Etale R S := by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun R S
  exact .of_equiv e.symm

open Ideal in
variable (k) in
/-
**Algebra.IsFiniteSplit.bijective_algebraMap_quotient** 是 Mathlib 中的一个引理，位于命名空间 
`Algebra.IsFiniteSplit`。
形式化陈述：bijective_algebraMap_quotient [IsFiniteSplit k R] (p : Ideal R) [p.IsPrime
] : Function.Bijective (algebraMap k (R ⧸ p))
参数：p : Ideal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsFiniteSplit.nonempty_algEquiv_fun`：∀ (R : Type u_1) (S : Type 
u_2) {inst : CommRing R} {inst_1 : CommRing S} {inst_2 : Algebra R S}   [self : 
Algebra.IsFiniteSplit R S], ∃ n, …
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用引理 `PrimeSpectrum.exists_comap_evalRingHom_eq`：exists_comap_evalRingHom_eq {
ι : Type*} {R : ι -> Type*} [forall i, CommRing (R i)] [Finite ι] (p : PrimeSpec
trum (Π i, R i)) : exists (i : …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.comap_symm`：comap_symm {I : Ideal R} (f : R ≃+* S) : I.comap f.sym
m = I.map f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.surjective_eval`：surjective_eval {α : Sort u} {β : α -> Sort v}
 [h : forall a, Nonempty (β a)] (a : α) : Surjective (eval a : (forall a, β a) -
> β a)
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `AlgEquiv.bijective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma bijective_algebraMap_quotient [IsFiniteSplit k R] (p : Ideal R) [p.IsPrime] :
    Function.Bijective (algebraMap k (R ⧸ p)) := by
  obtain ⟨n, ⟨e⟩⟩ := nonempty_algEquiv_fun k R
  let p' : Ideal (Fin n → k) := p.comap e.symm
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq ⟨p', inferInstance⟩
  obtain rfl : q = ⊥ := Subsingleton.elim _ _
  let g : (R ⧸ p) ≃ₐ[k] k :=
    (quotientEquivAlg _ p' e <| comap_symm e.toRingEquiv).trans <|
    (quotientEquivAlgOfEq k congr($(hq).asIdeal).symm).trans <|
    quotientKerAlgEquivOfSurjective (f := Pi.evalAlgHom k (fun _ ↦ k) i)
      (Function.surjective_eval _)
  simpa [← g.symm.toAlgHom.comp_algebraMap] using g.symm.bijective

set_option backward.isDefEq.respectTransparency.types false in
variable (k R) in
/-- If `R` is finite split over a field `k`, the `k`-rational points of `R`
are in one-to-one correspondence with its prime spectrum. -/
@[expose]
noncomputable
/-
**Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum** 是 Mathlib 中的一个定义，位于命名空间 `Alge
bra.IsFiniteSplit`。
形式化陈述：algHomEquivPrimeSpectrum [IsFiniteSplit k R] : (R ->ₐ[k] k) ≃ PrimeSpectru
m R where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def algHomEquivPrimeSpectrum [IsFiniteSplit k R] : (R →ₐ[k] k) ≃ PrimeSpectrum R where
  toFun f := ⟨RingHom.ker f, RingHom.ker_isPrime f⟩
  invFun p := AlgHom.comp
    (AlgEquiv.ofBijective (Algebra.ofId _ _) (bijective_algebraMap_quotient _ _)).symm.toAlgHom
    (Ideal.Quotient.mkₐ _ p.asIdeal)
  left_inv f := by
    ext
    dsimp
    have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
    apply (AlgEquiv.ofBijective (ofId k (R ⧸ RingHom.ker f))
      (bijective_algebraMap_quotient _ _)).injective
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.coe_ofBijective, ofId_apply,
      IsScalarTower.algebraMap_apply k R]
    simp [-Ideal.Quotient.mk_algebraMap, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  right_inv p := by
    ext : 1
    dsimp
    rw [← AlgHom.comap_ker, ← RingHom.ker_coe_toRingHom, AlgEquiv.toAlgHom_toRingHom,
      AlgHom.ker_coe_equiv, ← RingHom.ker_eq_comap_bot, ← RingHom.ker_coe_toRingHom,
      Ideal.Quotient.mkₐ_ker]

@[simp]
/-
**Algebra.IsFiniteSplit.coe_algHomEquivPrimeSpectrum** 是 Mathlib 中的一个引理，位于命名空间 `
Algebra.IsFiniteSplit`。
形式化陈述：coe_algHomEquivPrimeSpectrum [IsFiniteSplit k R] (f : R ->ₐ[k] k) : algHom
EquivPrimeSpectrum k R f = RingHom.ker f
参数：f : R ->ₐ[k] k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_algHomEquivPrimeSpectrum [IsFiniteSplit k R] (f : R →ₐ[k] k) :
    algHomEquivPrimeSpectrum k R f = RingHom.ker f :=
  rfl
/-
**Algebra.IsFiniteSplit.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.IsFiniteSplit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsSepClosed k] [EssFiniteType k R] [FormallyEtale k R] : IsFiniteSplit k R := by
  have := FormallyUnramified.finite_of_free k R
  have : IsArtinianRing R := isArtinian_of_tower k inferInstance
  exact .of_algEquiv (Algebra.FormallyEtale.equivPiOfIsSepClosed k R).symm

variable {n : ℕ} {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/--
If `S` is finite étale over `R` of (constant) rank `n`, there exists
a finite faithfully flat, étale `R`-algebra `T` such that `T ⊗[R] S` is split of rank `n`
over `T`.
This is the commutative algebra version of
[Lenstra, Galois theory for schemes, 5.10][lenstraGSchemes].
-/
/-
**Algebra.IsFiniteSplit.exists_tensorProduct_of_etale** 是 Mathlib 中的一个引理，位于命名空间 
`Algebra.IsFiniteSplit`。
形式化陈述：exists_tensorProduct_of_etale [Etale R S] [Module.Finite R S] {n : Nat} (h
n : Module.rankAtStalk (R
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.IsFiniteSplit.instEtale`：∀ {R : Type u_2} {S : Type u_3} [inst :
 CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.IsFiniteSpl
it R S], Algebra.Etal…
· 使用定理 `Algebra.IsFiniteSplit.inst`：∀ {R : Type u_2} [inst : CommRing R], Algebr
a.IsFiniteSplit R R
· 使用引理 `Algebra.IsFiniteSplit.of_subsingleton_top`：of_subsingleton_top [Subsingl
eton S] : IsFiniteSplit R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.rankAtStalk_eq_zero_iff_subsingleton`：rankAtStalk_eq_zero_iff_sub
singleton : rankAtStalk (R
· 使用定理 `Algebra.Smooth.flat`：∀ (R : Type u_1) (A : Type u_2) [inst : CommRing R]
 [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.Smooth R A],   Module.Fla
t R A
· 使用定理 `Algebra.Etale.instSmooth`：∀ {R : Type u} {A : Type v} [inst : CommRing R
] [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.Etale R A],   Algebra.Sm
ooth R A
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `Algebra.IsFiniteSplit.of_algEquiv`：of_algEquiv {S' : Type*} [CommRing S'
] [Algebra R S'] (e : S ≃ₐ[R] S') [IsFiniteSplit R S] : IsFiniteSplit R S'
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用引理 `Algebra.IsFiniteSplit.of_subsingleton`：of_subsingleton [Subsingleton R] 
: IsFiniteSplit R S
· 使用引理 `Module.nontrivial_of_rankAtStalk_pos`：nontrivial_of_rankAtStalk_pos (h :
 0 < rankAtStalk (R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Pi.instCanonicallyOrderedAddForall`：∀ {ι : Type u_6} {Z : ι → Type u_7} 
[inst : (i : ι) → AddMonoid (Z i)] [inst_1 : (i : ι) → PartialOrder (Z i)]   [∀ 
(i : ι), CanonicallyOrde…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `PrimeSpectrum.instNonemptyOfNontrivial`：∀ {R : Type u} [inst : CommSemir
ing R] [Nontrivial R], Nonempty (PrimeSpectrum R)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用引理 `Algebra.FormallyUnramified.exists_algEquiv_prod`：exists_algEquiv_prod (R
 S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
 [Algebra.FormallyUnramified R S] : e…
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用定理 `Algebra.Unramified.finiteType`：∀ {R : Type u_1} {inst : CommRing R} {A :
 Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Unrami
fied R A], Algebra.…
· 使用定理 `Algebra.Etale.instUnramified`：∀ {R : Type u} {A : Type v} [inst : CommRi
ng R] [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.Etale R A],   Algebr
a.Unramified R A
· 使用定理 `Algebra.Unramified.formallyUnramified`：∀ {R : Type u_1} {inst : CommRing
 R} {A : Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebr
a.Unramified R A], Algebra.…
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Algebra.Etale.of_equiv`：of_equiv [Etale R A] (e : A ≃ₐ[R] B) : Etale R B
 where formallyEtale
· 使用定理 `Algebra.Etale.baseChange`：∀ (R : Type u) (A : Type v) (B : Type u_1) [in
st : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [inst_3 : CommRi
ng B] [inst_4 …
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
If `S` is finite étale over `R` of (constant) rank `n`, there exists
a finite faithfully flat, étale `R`-algebra `T` such that `T ⊗[R] S` is split of
 rank `n`
over `T`.
This is the commutative algebra version of
[Lenstra, Galois theory for schemes, 5.10][lenstraGSchemes].
-/
lemma exists_tensorProduct_of_etale [Etale R S] [Module.Finite R S] {n : ℕ}
    (hn : Module.rankAtStalk (R := R) S = n) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T)
      (_ : Module.FaithfullyFlat R T) (_ : Module.Finite R T) (_ : Algebra.Etale R T),
      IsFiniteSplit T (T ⊗[R] S) := by
  induction n generalizing R S with
  | zero =>
    use R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance
    let e : R ⊗[R] S ≃ₐ[R] S := TensorProduct.lid R S
    have : IsFiniteSplit R S := by
      rw [Nat.cast_zero, Module.rankAtStalk_eq_zero_iff_subsingleton] at hn
      exact of_subsingleton_top
    apply IsFiniteSplit.of_algEquiv e.symm
  | succ n ih =>
    cases subsingleton_or_nontrivial R
    · use R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance
      have : IsFiniteSplit R S := .of_subsingleton
      exact .of_algEquiv (TensorProduct.lid R S).symm
    have : Nontrivial S := by
      apply Module.nontrivial_of_rankAtStalk_pos (R := R)
      simp [hn]
    /- Because `S` is unramified over `R`, there exists an `S`-algebra `U` such that
    `S ⊗[R] S ≃ₐ[S] S × U`. -/
    obtain ⟨U, _, _, ⟨e⟩⟩ := Algebra.FormallyUnramified.exists_algEquiv_prod R S
    algebraize [RingHom.snd S U]
    have : IsScalarTower S (S × U) U := IsScalarTower.of_algebraMap_eq' rfl
    have : Etale S U := by
      have : Etale S (S × U) := Etale.of_equiv e
      exact .comp S (S × U) U
    have : Module.Finite S U := by
      have : Module.Finite S (S × U) := Module.Finite.equiv e.toLinearEquiv
      have : Module.Finite (S × U) U :=
        Module.Finite.of_surjective (Algebra.linearMap (S × U) U) (RingHom.snd S U).surjective
      exact Module.Finite.trans (S × U) _
    have (p : PrimeSpectrum S) : Module.rankAtStalk (R := S) (S × U) p = n + 1 := by
      simp [Module.rankAtStalk_eq_of_equiv e.symm.toLinearEquiv, Module.rankAtStalk_baseChange, hn]
    simp_rw [Module.rankAtStalk_prod , Module.rankAtStalk_self, Pi.add_apply, Pi.one_apply] at this
    /- Since the `S`-rank of `S × U = S ⊗[R] S` is `n + 1`, the `S`-rank of `U` is `n`,
    so we may apply the induction hypothesis on `U`. -/
    have : Module.rankAtStalk (R := S) U = n := by
      ext p
      simp only [Pi.natCast_def, Nat.cast_id]
      grind
    /- We obtain a finite étale, faithfully flat `S`-algebra `V` such that `V ⊗[S] U` is finite
    split. We claim that `V` viewed as an `R`-algebra works. -/
    obtain ⟨V, _, _, _, _, _, hV⟩ := ih this
    obtain ⟨n, ⟨f⟩⟩ := hV.nonempty_algEquiv_fun
    algebraize [(algebraMap S V).comp (algebraMap R S)]
    let e : V ⊗[R] S ≃ₐ[V] Unit ⊕ Fin n → V :=
      (Algebra.TensorProduct.cancelBaseChange R S V V S).symm.trans <|
        (TensorProduct.congr AlgEquiv.refl e).trans <|
        (TensorProduct.prodRight S V V S U).trans <|
        (AlgEquiv.prodCongr (TensorProduct.rid S V V) f).trans <|
        (AlgEquiv.prodCongr (AlgEquiv.funUnique _ _ _).symm AlgEquiv.refl).trans
        (AlgEquiv.sumArrowEquivProdArrow Unit (Fin n) V V).symm
    refine ⟨V, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
    · have : Module.FaithfullyFlat R S := by
        apply Module.FaithfullyFlat.of_comap_surjective
        rw [← PrimeSpectrum.rankAtStalk_pos_iff_comap_surjective]
        intro p
        simp [hn]
      exact Module.FaithfullyFlat.trans R S V
    · exact Module.Finite.trans S V
    · exact Algebra.Etale.comp R S V
    · exact .of_algEquiv e.symm

end IsFiniteSplit

end Algebra

