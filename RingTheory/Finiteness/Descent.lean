/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Descent of finiteness conditions under faithfully flat maps

In this file we show that

- `Algebra.FiniteType`:
- `Algebra.FinitePresentation`:
- `Module.Finite`:

descend along faithfully flat base change.
-/

public section

universe u v w

open TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (T : Type*) [CommRing T] [Algebra R T]

/-
**Module.Finite.of_finite_tensorProduct_of_faithfullyFlat** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：Module.Finite.of_finite_tensorProduct_of_faithfullyFlat {M : Type*} [AddCo
mmGroup M] [Module R M] [Module.FaithfullyFlat R T] [Module.Finite T (T otimes[R
] M)] : Module.Finite R M
参数：T otimes[R] M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Module.Finite.exists_fin`：exists_fin [Module.Finite R M] : exists (n : N
at) (s : Fin n -> M), span R (range s) = ⊤
· 使用定理 `Finite.instSigma`：∀ {α : Type u_1} {β : α → Type u_2} [Finite α] [∀ (a :
 α), Finite (β a)], Finite ((a : α) × β a)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.constr_apply_fintype`：constr_apply_fintype [Fintype ι] (b :
 Basis ι R M) (f : ι -> M') (x : M) : (constr (M'
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.equivFun_self`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_
6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M]
 [inst_3 : Finit…
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
（共 35 条，此处仅展示前 30 条）
-/
lemma Module.Finite.of_finite_tensorProduct_of_faithfullyFlat {M : Type*} [AddCommGroup M]
    [Module R M] [Module.FaithfullyFlat R T] [Module.Finite T (T ⊗[R] M)] :
    Module.Finite R M := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := T) (M := T ⊗[R] M)
  choose k t m h using fun i : Fin n ↦ TensorProduct.exists_sum_tmul_eq (s i)
  let f₀ : ((Σ i, Fin (k i)) → R) →ₗ[R] M := (Pi.basisFun R _).constr R fun ⟨i, j⟩ ↦ m i j
  apply of_surjective f₀
  have : Function.Surjective (AlgebraTensorModule.lTensor T T f₀) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le, Set.range_subset_iff]
    intro i
    use ∑ (j : Fin (k i)), t i j ⊗ₜ Pi.basisFun R _ ⟨i, j⟩
    simp [f₀, -Pi.basisFun_equivFun, -Pi.basisFun_apply, h i]
  rwa [← Module.FaithfullyFlat.lTensor_surjective_iff_surjective _ T]
/-
**Ideal.FG.of_FG_map_of_faithfullyFlat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.FG.of_FG_map_of_faithfullyFlat [Module.FaithfullyFlat R S] {I : Idea
l R} (hI : (I.map (algebraMap R S)).FG) : I.FG
参数：hI : (I.map (algebraMap R S)).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Algebra.mul_smul_comm`：∀ {R : Type u} {A : Type w} [inst : CommSemiring 
R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : R) (x y : A),   x * s • y =
 s • (x * y…
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Module.Finite.equiv_iff`：equiv_iff (e : M ≃ₗ[R] N) : Module.Finite R M ↔
 Module.Finite R N
（共 31 条，此处仅展示前 30 条）
-/
lemma Ideal.FG.of_FG_map_of_faithfullyFlat [Module.FaithfullyFlat R S] {I : Ideal R}
    (hI : (I.map (algebraMap R S)).FG) : I.FG := by
  change Submodule.FG I
  rw [← Module.Finite.iff_fg]
  let f : S ⊗[R] I →ₗ[S] S :=
    (AlgebraTensorModule.rid _ _ _).toLinearMap ∘ₗ AlgebraTensorModule.lTensor S S I.subtype
  have hf : Function.Injective f := by simp [f]
  have : I.map (algebraMap R S) = LinearMap.range f := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      use 1 ⊗ₜ ⟨x, hx⟩
      simp [f, Algebra.smul_def]
    · rintro - ⟨x, rfl⟩
      induction x with
      | zero => simp
      | add _ _ _ _ => simp_all [Ideal.add_mem]
      | tmul s x =>
        have : f (s ⊗ₜ[R] x) = s • f (1 ⊗ₜ x) := by simp [f]
        rw [this]
        apply Ideal.mul_mem_left
        simpa [f, Algebra.smul_def] using Ideal.mem_map_of_mem _ x.2
  let e : S ⊗[R] I ≃ₗ[S] I.map (algebraMap R S) := .ofInjective _ hf ≪≫ₗ .ofEq _ _ this.symm
  have : Module.Finite S (S ⊗[R] ↥I) := by
    rwa [Module.Finite.equiv_iff e, Module.Finite.iff_fg]
  apply Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S

namespace Algebra

/-- If `T ⊗[R] S` is of finite type over `T` and `T` is `R`-faithfully flat,
then `S` is of finite type over `R` -/
/-
**Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat** 是 Mathlib 中
的一个定理，位于命名空间 `Algebra.FiniteType`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (T : Type u_3)   [inst_3 : CommRing T] [inst_4 : Algebra 
R T] [Module.FaithfullyFlat R T] [Algebra.FiniteType T (TensorProduct R T S)],  
 Algebra.FiniteType R S
参数：T : Type u_3；TensorProduct R T S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.FiniteType.out`：∀ {R : Type uR} {A : Type uA} {inst : CommSemiri
ng R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : Algebra.FiniteType 
R A], ⊤.FG
· 使用引理 `TensorProduct.exists_sum_tmul_eq`：exists_sum_tmul_eq (x : M otimes[R] N)
 : exists (k : Nat) (m : Fin k -> M) (n : Fin k -> N), x = ∑ j, m j otimesₜ n j
· 使用定理 `Algebra.FiniteType.of_surjective`：of_surjective [FiniteType R A] (f : A 
->ₐ[R] B) (hf : Surjective f) : FiniteType R B
· 使用定理 `Algebra.FiniteType.instMvPolynomialOfFinite`：∀ {R : Type uR} {S : Type u
S} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S] {ι :
 Type u_1}   [Finite ι] [Algebra.…
· 使用定理 `Finite.instSigma`：∀ {α : Type u_1} {β : α → Type u_2} [Finite α] [∀ (a :
 α), Finite (β a)], Finite ((a : α) × β a)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.range_eq_top`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Co
mmSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring 
B] [inst_…
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Module.FaithfullyFlat.lTensor_surjective_iff_surjective`：lTensor_surject
ive_iff_surjective [Module.FaithfullyFlat R M] : Function.Surjective (f.lTensor 
M) ↔ Function.Surjective f
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If `T ⊗[R] S` is of finite type over `T` and `T` is `R`-faithfully flat,
then `S` is of finite type over `R`
-/
lemma FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat
    [Module.FaithfullyFlat R T] [Algebra.FiniteType T (T ⊗[R] S)] :
    Algebra.FiniteType R S := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := T) (A := T ⊗[R] S)
  have (x : s) := TensorProduct.exists_sum_tmul_eq x.1
  choose k t m h using this
  let f : MvPolynomial (Σ x : s, Fin (k x)) R →ₐ[R] S := MvPolynomial.aeval (fun ⟨x, i⟩ ↦ m x i)
  apply Algebra.FiniteType.of_surjective f
  have hf : Function.Surjective (Algebra.TensorProduct.map (.id T T) f) := by
    rw [← AlgHom.range_eq_top, _root_.eq_top_iff, ← hs, adjoin_le_iff]
    intro x hx
    let i : s := ⟨x, hx⟩
    use ∑ (j : Fin (k i)), t i j ⊗ₜ MvPolynomial.X ⟨i, j⟩
    simp [f, ← h, i]
  exact (Module.FaithfullyFlat.lTensor_surjective_iff_surjective _ T _).mp hf

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- If `T ⊗[R] S` is of finite presentation over `T` and `T` is `R`-faithfully flat,
then `S` is of finite presentation over `R` -/
/-
**Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFl
at** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FinitePresentation`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (T : Type u_3)   [inst_3 : CommRing T] [inst_4 : Algebra 
R T] [Module.FaithfullyFlat R T]   [Algebra.FinitePresentation T (TensorProduct 
R T S)], Algebra.FinitePresentation R S
参数：T : Type u_3；TensorProduct R T S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat`：∀ {R :
 Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Al
gebra R S] (T : Type u_3)   [inst_3 : CommRing T] [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FiniteType.iff_quotient_mvPolynomial''`：iff_quotient_mvPolynomia
l'' : FiniteType R S ↔ exists (n : Nat) (f : MvPolynomial (Fin n) R ->ₐ[R] S), S
urjective f
· 使用引理 `Module.FaithfullyFlat.of_linearEquiv`：of_linearEquiv {N : Type*} [AddCom
mGroup N] [Module R N] [FaithfullyFlat R M] (e : N ≃ₗ[R] M) : FaithfullyFlat R N
· 使用定理 `Module.FaithfullyFlat.instTensorProduct`：∀ (R : Type u) (M : Type v) [in
st : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] (S : Typ
e u_1)   [inst_3 : CommRing S…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.FinitePresentation.of_surjective`：of_surjective {f : A ->ₐ[R] B}
 (hf : Function.Surjective f) (hker : (RingHom.ker f.toRingHom).FG) [FinitePrese
ntation R A] : FinitePresentat…
· 使用引理 `Ideal.FG.of_FG_map_of_faithfullyFlat`：Ideal.FG.of_FG_map_of_faithfullyFl
at [Module.FaithfullyFlat R S] {I : Ideal R} (hI : (I.map (algebraMap R S)).FG) 
: I.FG
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.TensorProduct.lTensor_ker`：Algebra.TensorProduct.lTensor_ker (hg
 : Function.Surjective g) : RingHom.ker (map (AlgHom.id R A) g) = (RingHom.ker g
).map (Algebra.TensorPr…
· 使用定理 `Algebra.FinitePresentation.ker_fG_of_surjective`：ker_fG_of_surjective (f
 : A ->ₐ[R] B) (hf : Function.Surjective f) [FinitePresentation R A] [FinitePres
entation R B] : (RingHom.ker f.toRing…
· 使用定理 `Algebra.FiniteType.baseChangeAux_surj`：baseChangeAux_surj {σ : Type*} {f
 : MvPolynomial σ R ->ₐ[R] A} (hf : Function.Surjective f) : Function.Surjective
 (Algebra.TensorProduct.map…
· 使用定理 `Algebra.FinitePresentation.mvPolynomial`：∀ (R : Type w₁) (A : Type w₂) [
inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Finit
ePresentation R A] (ι : Type …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `T ⊗[R] S` is of finite presentation over `T` and `T` is `R`-faithfully flat,
then `S` is of finite presentation over `R`
-/
lemma FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
    [Module.FaithfullyFlat R T] [Algebra.FinitePresentation T (T ⊗[R] S)] :
    Algebra.FinitePresentation R S := by
  have : Algebra.FiniteType R S := .of_finiteType_tensorProduct_of_faithfullyFlat T
  rw [Algebra.FiniteType.iff_quotient_mvPolynomial''] at this
  obtain ⟨n, f, hf⟩ := this
  have : Module.FaithfullyFlat (MvPolynomial (Fin n) R) (T ⊗[R] MvPolynomial (Fin n) R) :=
    .of_linearEquiv _ _ (Algebra.TensorProduct.commRight _ _ _).symm.toLinearEquiv
  let fT := Algebra.TensorProduct.map (.id T T) f
  refine .of_surjective hf (.of_FG_map_of_faithfullyFlat (S := T ⊗[R] MvPolynomial (Fin n) R) ?_)
  have : (RingHom.ker f.toRingHom).map
      (algebraMap (MvPolynomial (Fin n) R) (T ⊗[R] MvPolynomial (Fin n) R)) = RingHom.ker fT :=
    (Algebra.TensorProduct.lTensor_ker f hf).symm
  rw [this]
  apply ker_fG_of_surjective
  exact FiniteType.baseChangeAux_surj T hf

end Algebra

namespace RingHom

/-
**RingHom.FiniteType.codescendsAlong_faithfullyFlat** 是 Mathlib 中的一个定理，位于命名空间 `R
ingHom.FiniteType`。
形式化陈述：RingHom.CodescendsAlong (fun {R S} [CommRing R] [CommRing S] => RingHom.Fi
niteType)   fun {R S} [CommRing R] [CommRing S] => RingHom.FaithfullyFlat
参数：fun {R S} [CommRing R] [CommRing S] => RingHom.FiniteType。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.CodescendsAlong.mk`：∀ {P : {R S : Type u} → [inst : CommRing R] 
→ [inst_1 : CommRing S] → (R →+* S) → Prop}   (Q : {R S : Type u} → [inst : Comm
Ring R] → [inst_…
· 使用定理 `RingHom.finiteType_respectsIso`：finiteType_respectsIso : RingHom.Respect
sIso @RingHom.FiniteType
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.finiteType_algebraMap`：finiteType_algebraMap [Algebra A B] : (al
gebraMap A B).FiniteType ↔ Algebra.FiniteType A B
· 使用定理 `Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat`：∀ {R :
 Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Al
gebra R S] (T : Type u_3)   [inst_3 : CommRing T] [ins…
· 使用引理 `RingHom.faithfullyFlat_algebraMap_iff`：faithfullyFlat_algebraMap_iff [Al
gebra R S] : (algebraMap R S).FaithfullyFlat ↔ Module.FaithfullyFlat R S
-/
lemma FiniteType.codescendsAlong_faithfullyFlat :
    CodescendsAlong FiniteType FaithfullyFlat := by
  refine .mk _ finiteType_respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [finiteType_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_finiteType_tensorProduct_of_faithfullyFlat S
/-
**RingHom.FinitePresentation.codescendsAlong_faithfullyFlat** 是 Mathlib 中的一个定理，位
于命名空间 `RingHom.FinitePresentation`。
形式化陈述：RingHom.CodescendsAlong (fun {R S} [CommRing R] [CommRing S] => RingHom.Fi
nitePresentation)   fun {R S} [CommRing R] [CommRing S] => RingHom.FaithfullyFla
t
参数：fun {R S} [CommRing R] [CommRing S] => RingHom.FinitePresentation。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.CodescendsAlong.mk`：∀ {P : {R S : Type u} → [inst : CommRing R] 
→ [inst_1 : CommRing S] → (R →+* S) → Prop}   (Q : {R S : Type u} → [inst : Comm
Ring R] → [inst_…
· 使用定理 `RingHom.finitePresentation_respectsIso`：finitePresentation_respectsIso :
 RingHom.RespectsIso @RingHom.FinitePresentation
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.finitePresentation_algebraMap`：finitePresentation_algebraMap [Al
gebra A B] : (algebraMap A B).FinitePresentation ↔ Algebra.FinitePresentation A 
B
· 使用定理 `Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithf
ullyFlat`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing
 S] [inst_2 : Algebra R S] (T : Type u_3)   [inst_3 : CommRing T] [ins…
· 使用引理 `RingHom.faithfullyFlat_algebraMap_iff`：faithfullyFlat_algebraMap_iff [Al
gebra R S] : (algebraMap R S).FaithfullyFlat ↔ Module.FaithfullyFlat R S
-/
lemma FinitePresentation.codescendsAlong_faithfullyFlat :
    CodescendsAlong FinitePresentation FaithfullyFlat := by
  refine .mk _ finitePresentation_respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [finitePresentation_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_finitePresentation_tensorProduct_of_faithfullyFlat S
/-
**RingHom.Finite.codescendsAlong_faithfullyFlat** 是 Mathlib 中的一个定理，位于命名空间 `RingH
om.Finite`。
形式化陈述：RingHom.CodescendsAlong (fun {R S} [CommRing R] [CommRing S] => RingHom.Fi
nite) fun {R S} [CommRing R] [CommRing S] =>   RingHom.FaithfullyFlat
参数：fun {R S} [CommRing R] [CommRing S] => RingHom.Finite。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.CodescendsAlong.mk`：∀ {P : {R S : Type u} → [inst : CommRing R] 
→ [inst_1 : CommRing S] → (R →+* S) → Prop}   (Q : {R S : Type u} → [inst : Comm
Ring R] → [inst_…
· 使用定理 `RingHom.finite_respectsIso`：finite_respectsIso : RespectsIso @Finite
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.finite_algebraMap`：finite_algebraMap [Algebra A B] : (algebraMap
 A B).Finite ↔ Module.Finite A B
· 使用引理 `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`：Module.Finite.o
f_finite_tensorProduct_of_faithfullyFlat {M : Type*} [AddCommGroup M] [Module R 
M] [Module.FaithfullyFlat R T] [Module.Finite…
· 使用引理 `RingHom.faithfullyFlat_algebraMap_iff`：faithfullyFlat_algebraMap_iff [Al
gebra R S] : (algebraMap R S).FaithfullyFlat ↔ Module.FaithfullyFlat R S
-/
lemma Finite.codescendsAlong_faithfullyFlat :
    CodescendsAlong Finite FaithfullyFlat := by
  refine .mk _ finite_respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [finite_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_finite_tensorProduct_of_faithfullyFlat S

end RingHom

