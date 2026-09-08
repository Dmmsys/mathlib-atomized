/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Ideal.IdempotentFG
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Flat.Stability

/-!
# Various results about unramified algebras

We prove various theorems about unramified algebras. In fact we work in the more general setting
of formally unramified algebras which are essentially of finite type.

## Main results

- `Algebra.FormallyUnramified.iff_exists_tensorProduct`:
  A finite-type `R`-algebra `S` is (formally) unramified iff
  there exists a `t : S ⊗[R] S` satisfying
  1. `t` annihilates every `1 ⊗ s - s ⊗ 1`.
  2. the image of `t` is `1` under the map `S ⊗[R] S → S`.
- `Algebra.FormallyUnramified.finite_of_free`: An unramified free algebra is finitely generated.
- `Algebra.FormallyUnramified.flat_of_restrictScalars`:
  If `S` is an unramified `R`-algebra, then `R`-flat implies `S`-flat.

## References

- [B. Iversen, *Generic Local Structure of the Morphisms in Commutative Algebra*][iversen]

-/

@[expose] public section

open Algebra Module
open scoped TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

namespace Algebra.FormallyUnramified

/--
Proposition I.2.3 + I.2.6 of [iversen]
A finite-type `R`-algebra `S` is (formally) unramified iff there exists a `t : S ⊗[R] S` satisfying
1. `t` annihilates every `1 ⊗ s - s ⊗ 1`.
2. the image of `t` is `1` under the map `S ⊗[R] S → S`.
-/
/-
**Algebra.FormallyUnramified.iff_exists_tensorProduct** 是 Mathlib 中的一个定理，位于命名空间 
`Algebra.FormallyUnramified`。
形式化陈述：iff_exists_tensorProduct [EssFiniteType R S] : FormallyUnramified R S ↔ ex
ists t : S otimes[R] S, (forall s, ((1 : S) otimesₜ[R] s - s otimesₜ[R] (1 : S))
 * t = 0) ∧ TensorProduct.lmul' R t = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.formallyUnramified_iff`：∀ (R : Type v) (A : Type u) [inst : Comm
Ring R] [inst_1 : CommRing A] [inst_2 : Algebra R A],   Algebra.FormallyUnramifi
ed R A ↔ Subsingleto…
· 使用定理 `KaehlerDifferential.eq_1`：∀ (R : Type u) (S : Type v) [inst : CommRing R
] [inst_1 : CommRing S] [inst_2 : Algebra R S],   Ω[S⁄R] = (KaehlerDifferential.
ideal R S).Cot…
· 使用定理 `Ideal.cotangent_subsingleton_iff`：cotangent_subsingleton_iff : Subsingle
ton I.Cotangent ↔ IsIdempotentElem I
· 使用定理 `Ideal.isIdempotentElem_iff_of_fg`：isIdempotentElem_iff_of_fg {R : Type*}
 [CommRing R] (I : Ideal R) (h : I.FG) : IsIdempotentElem I ↔ exists e : R, IsId
empotentElem e ∧ I = R…
· 使用定理 `KaehlerDifferential.ideal_fg`：KaehlerDifferential.ideal_fg [EssFiniteTyp
e R S] : (KaehlerDifferential.ideal R S).FG
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
（共 83 条，此处仅展示前 30 条）

--- 原说明 ---
Proposition I.2.3 + I.2.6 of [iversen]
A finite-type `R`-algebra `S` is (formally) unramified iff there exists a `t : S
 ⊗[R] S` satisfying
1. `t` annihilates every `1 ⊗ s - s ⊗ 1`.
2. the image of `t` is `1` under the map `S ⊗[R] S → S`.
-/
theorem iff_exists_tensorProduct [EssFiniteType R S] :
    FormallyUnramified R S ↔ ∃ t : S ⊗[R] S,
      (∀ s, ((1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) * t = 0) ∧ TensorProduct.lmul' R t = 1 := by
  rw [formallyUnramified_iff, KaehlerDifferential,
    Ideal.cotangent_subsingleton_iff, Ideal.isIdempotentElem_iff_of_fg _
      (KaehlerDifferential.ideal_fg R S)]
  have : ∀ t : S ⊗[R] S, TensorProduct.lmul' R t = 1 ↔ 1 - t ∈ KaehlerDifferential.ideal R S := by
    intro t
    simp only [KaehlerDifferential.ideal, RingHom.mem_ker, map_sub, map_one,
      sub_eq_zero, @eq_comm S 1]
  simp_rw [this, ← KaehlerDifferential.span_range_eq_ideal]
  constructor
  · rintro ⟨e, he₁, he₂ : _ = Ideal.span _⟩
    refine ⟨1 - e, ?_, ?_⟩
    · intro s
      obtain ⟨x, hx⟩ : e ∣ 1 ⊗ₜ[R] s - s ⊗ₜ[R] 1 := by
        rw [← Ideal.mem_span_singleton, ← he₂]
        exact Ideal.subset_span ⟨s, rfl⟩
      rw [hx, mul_comm, ← mul_assoc, sub_mul, one_mul, he₁.eq, sub_self, zero_mul]
    · rw [sub_sub_cancel, he₂, Ideal.mem_span_singleton]
  · rintro ⟨t, ht₁, ht₂⟩
    use 1 - t
    rw [← sub_sub_self 1 t] at ht₁; generalize 1 - t = e at *
    constructor
    · suffices e ∈ (Submodule.span (S ⊗[R] S) {1 - e}).annihilator by
        simpa [IsIdempotentElem, mul_sub, sub_eq_zero, eq_comm,
          Submodule.mem_annihilator_span_singleton] using this
      exact (show Ideal.span _ ≤ _ by simpa only [Ideal.span_le, Set.range_subset_iff,
        Submodule.mem_annihilator_span_singleton, SetLike.mem_coe]) ht₂
    · apply le_antisymm <;> simp only [Ideal.submodule_span_eq, Ideal.mem_span_singleton, ht₂,
        Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Set.range_subset_iff]
      intro s
      use 1 ⊗ₜ[R] s - s ⊗ₜ[R] 1
      linear_combination ht₁ s
/-
**Algebra.FormallyUnramified.finite_of_free_aux** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
ra.FormallyUnramified`。
形式化陈述：finite_of_free_aux (I) [DecidableEq I] (b : Basis I R S) (f : I ->₀ S) (x 
: S) (a : I -> I ->₀ R) (ha : a = fun i => b.repr (b i * x)) : (1 otimesₜ[R] x *
 Finsupp.sum f fun i y => y otimesₜ[R] b i) = Finset.sum (f.support.biUnion fun 
i => (a i).support) fun k => Finsupp.sum (b.repr (f.sum fun i y => a i k • y)) f
un j c => c • b j otimesₜ[R] b k
参数：I；b : Basis I R S；f : I ->₀ S；x : S；a : I -> I ->₀ R；ha : a = fun i => b.repr
 (b i * x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst 
: Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (g : α → M → N),   f.sum g = ∑
 a ∈ f…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.linearCombination_repr`：linearCombination_repr : Finsupp.li
nearCombination _ b (b.repr x) = x
· 使用定理 `TensorProduct.tmul_sum`：tmul_sum (m : M) {α : Type*} (s : Finset α) (n :
 α -> N) : (m otimesₜ[R] ∑ a in s, n a) = ∑ a in s, m otimesₜ[R] n a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `Finsupp.sum_sum_index`：∀ {α : Type u_1} {β : Type u_7} {M : Type u_8} {N
 : Type u_10} {P : Type u_11} [inst : Zero M]   [inst_1 : AddCommMonoid N] [inst
_2 : AddCom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Finsupp.sum_smul_index`：sum_smul_index [MulZeroClass R] [AddCommMonoid M
] {g : α ->₀ R} {b : R} {h : α -> R -> M} (h0 : forall i, h i 0 = 0) : (b • g).s
um h = g.sum…
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
（共 38 条，此处仅展示前 30 条）
-/
lemma finite_of_free_aux (I) [DecidableEq I] (b : Basis I R S)
    (f : I →₀ S) (x : S) (a : I → I →₀ R) (ha : a = fun i ↦ b.repr (b i * x)) :
    (1 ⊗ₜ[R] x * Finsupp.sum f fun i y ↦ y ⊗ₜ[R] b i) =
      Finset.sum (f.support.biUnion fun i ↦ (a i).support) fun k ↦
      Finsupp.sum (b.repr (f.sum fun i y ↦ a i k • y)) fun j c ↦ c • b j ⊗ₜ[R] b k := by
  rw [Finsupp.sum, Finset.mul_sum]
  subst ha
  let a i := b.repr (b i * x)
  conv_lhs =>
    simp only [TensorProduct.tmul_mul_tmul, one_mul, mul_comm x (b _),
      ← show ∀ i, Finsupp.linearCombination _ b (a i) = b i * x from
          fun _ ↦ b.linearCombination_repr _]
  conv_lhs => simp only [Finsupp.linearCombination, Finsupp.coe_lsum,
    LinearMap.coe_smulRight, LinearMap.id_coe, id_eq, Finsupp.sum, TensorProduct.tmul_sum,
    ← TensorProduct.smul_tmul]
  have h₁ : ∀ k,
    (Finsupp.sum (Finsupp.sum f fun i y ↦ a i k • b.repr y) fun j z ↦ z • b j ⊗ₜ[R] b k) =
      (f.sum fun i y ↦ (b.repr y).sum fun j z ↦ a i k • z • b j ⊗ₜ[R] b k) := by
    intro i
    rw [Finsupp.sum_sum_index]
    · congr
      ext j s
      rw [Finsupp.sum_smul_index]
      · simp only [mul_smul, Finsupp.sum, ← Finset.smul_sum]
      intro; simp only [zero_smul]
    · intro; simp only [zero_smul]
    · intros; simp only [add_smul]
  have h₂ : ∀ (x : S), ((b.repr x).support.sum fun a ↦ b.repr x a • b a) = x := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using b.linearCombination_repr
  simp only [a] at h₁
  simp_rw [map_finsuppSum, map_smul, h₁, Finsupp.sum, Finset.sum_comm (t := f.support),
    TensorProduct.smul_tmul', ← TensorProduct.sum_tmul, ← Finset.smul_sum, h₂]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_subset_zero_on_sdiff
  · exact Finset.subset_biUnion_of_mem (fun i ↦ (a i).support) hi
  · simp only [a, Finset.mem_sdiff, Finset.mem_biUnion, Finsupp.mem_support_iff, ne_eq, not_not,
      and_imp, forall_exists_index]
    simp +contextual
  · exact fun _ _ ↦ rfl

variable [FormallyUnramified R S] [EssFiniteType R S]

variable (R S) in
/--
A finite-type `R`-algebra `S` is (formally) unramified iff there exists a `t : S ⊗[R] S` satisfying
1. `t` annihilates every `1 ⊗ s - s ⊗ 1`.
2. the image of `t` is `1` under the map `S ⊗[R] S → S`.

See `Algebra.FormallyUnramified.iff_exists_tensorProduct`.
This is the choice of such a `t`.
-/
noncomputable
/-
**Algebra.FormallyUnramified.elem** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.FormallyUnr
amified`。
形式化陈述：elem : S otimes[R] S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def elem : S ⊗[R] S :=
  (iff_exists_tensorProduct.mp inferInstance).choose
/-
**Algebra.FormallyUnramified.one_tmul_sub_tmul_one_mul_elem** 是 Mathlib 中的一个引理，位
于命名空间 `Algebra.FormallyUnramified`。
形式化陈述：one_tmul_sub_tmul_one_mul_elem (s : S) : (1 otimesₜ s - s otimesₜ 1) * ele
m R S = 0
参数：s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.FormallyUnramified.iff_exists_tensorProduct`：iff_exists_tensorPr
oduct [EssFiniteType R S] : FormallyUnramified R S ↔ exists t : S otimes[R] S, (
forall s, ((1 : S) otimesₜ[R] s - s otime…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma one_tmul_sub_tmul_one_mul_elem
    (s : S) : (1 ⊗ₜ s - s ⊗ₜ 1) * elem R S = 0 :=
  (iff_exists_tensorProduct.mp inferInstance).choose_spec.1 s
/-
**Algebra.FormallyUnramified.one_tmul_mul_elem** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
a.FormallyUnramified`。
形式化陈述：one_tmul_mul_elem (s : S) : (1 otimesₜ s) * elem R S = (s otimesₜ 1) * ele
m R S
参数：s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用引理 `Algebra.FormallyUnramified.one_tmul_sub_tmul_one_mul_elem`：one_tmul_sub_
tmul_one_mul_elem (s : S) : (1 otimesₜ s - s otimesₜ 1) * elem R S = 0
-/
lemma one_tmul_mul_elem
    (s : S) : (1 ⊗ₜ s) * elem R S = (s ⊗ₜ 1) * elem R S := by
  rw [← sub_eq_zero, ← sub_mul, one_tmul_sub_tmul_one_mul_elem]
/-
**Algebra.FormallyUnramified.lmul_elem** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Formal
lyUnramified`。
形式化陈述：lmul_elem : TensorProduct.lmul' R (elem R S) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.FormallyUnramified.iff_exists_tensorProduct`：iff_exists_tensorPr
oduct [EssFiniteType R S] : FormallyUnramified R S ↔ exists t : S otimes[R] S, (
forall s, ((1 : S) otimesₜ[R] s - s otime…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma lmul_elem :
    TensorProduct.lmul' R (elem R S) = 1 :=
  (iff_exists_tensorProduct.mp inferInstance).choose_spec.2


variable (R S)

/-- An unramified free algebra is finitely generated. Iversen I.2.8 -/
/-
**Algebra.FormallyUnramified.finite_of_free** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.F
ormallyUnramified`。
形式化陈述：finite_of_free [Module.Free R S] : Module.Finite R S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.linearCombination_repr`：linearCombination_repr : Finsupp.li
nearCombination _ b (b.repr x) = x
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `LinearEquiv.trans.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Ty
pe u_4} {M₁ : Type u_8} {M₂ : Type u_9} {M₃ : Type u_10} [inst : Semiring R₁]   
[inst_1 : Semiring…
· 使用定理 `Finsupp.lcongr_symm`：lcongr_symm {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₛₗ
[σ] N) : (lcongr e₁ e₂).symm = lcongr e₁.symm e₂.symm
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_reindex`：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.
symm
· 使用定理 `Equiv.punitProd_symm_apply`：∀ (α : Type u_9) (a : α), (Equiv.punitProd α
).symm a = (PUnit.unit, a)
· 使用定理 `Finsupp.coe_basisSingleOne`：coe_basisSingleOne : (Finsupp.basisSingleOne
 : ι -> ι ->₀ R) = fun i => Finsupp.single i 1
· 使用定理 `Finsupp.lcongr_single`：lcongr_single {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M
 ≃ₛₗ[σ] N) (i : ι) (m : M) : lcongr e₁ e₂ (Finsupp.single i m) = Finsupp.single 
(e₁ i) (e₂ …
· 使用定理 `finsuppTensorFinsupp_symm_single`：finsuppTensorFinsupp_symm_single (i : 
ι × κ) (m : M) (n : N) : (finsuppTensorFinsupp R S M N ι κ).symm (Finsupp.single
 i (m otimesₜ n)) = Fi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `Module.Basis.coe_singleton`：coe_singleton {ι R : Type*} [Unique ι] [Semi
ring R] : ⇑(Basis.singleton ι R) = 1
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
（共 69 条，此处仅展示前 30 条）

--- 原说明 ---
An unramified free algebra is finitely generated. Iversen I.2.8
-/
lemma finite_of_free [Module.Free R S] : Module.Finite R S := by
  classical
  let I := Module.Free.ChooseBasisIndex R S
  -- Let `bᵢ` be an `R`-basis of `S`.
  let b : Basis I R S := Module.Free.chooseBasis R S
  -- Let `∑ₛ fᵢ ⊗ bᵢ : S ⊗[R] S` (summing over some finite `s`) be an element such that
  -- `∑ₛ fᵢbᵢ = 1` and `∀ x : S, xfᵢ ⊗ bᵢ = aᵢ ⊗ xfᵢ` which exists since `S` is unramified over `R`.
  have ⟨f, hf⟩ : ∃ (a : I →₀ S), elem R S = a.sum (fun i x ↦ x ⊗ₜ b i) := by
    let b' := ((Basis.singleton PUnit.{1} S).tensorProduct b).reindex (Equiv.punitProd I)
    use b'.repr (elem R S)
    conv_lhs => rw [← b'.linearCombination_repr (elem R S), Finsupp.linearCombination_apply]
    congr! with _ i x
    simp [b', Basis.tensorProduct, TensorProduct.smul_tmul']
  constructor
  -- I claim that `{ fᵢbⱼ | i, j ∈ s }` spans `S` over `R`.
  use Finset.image₂ (fun i j ↦ f i * b j) f.support f.support
  rw [← top_le_iff]
  -- For all `x : S`, let `bᵢx = ∑ aᵢⱼbⱼ`.
  rintro x -
  let a : I → I →₀ R := fun i ↦ b.repr (b i * x)
  -- Consider `F` such that `fⱼx = ∑ Fᵢⱼbⱼ`.
  let F : I →₀ I →₀ R := Finsupp.onFinset f.support (fun j ↦ b.repr (x * f j))
    (fun j ↦ not_imp_comm.mp fun hj ↦ by simp [Finsupp.notMem_support_iff.mp hj])
  have hG : ∀ j ∉ (Finset.biUnion f.support fun i ↦ (a i).support),
      b.repr (f.sum (fun i y ↦ a i j • y)) = 0 := by
    intro j hj
    simp only [Finset.mem_biUnion, Finsupp.mem_support_iff, ne_eq, not_exists, not_and,
      not_not] at hj
    simp only [Finsupp.sum]
    trans b.repr (f.support.sum (fun _ ↦ 0))
    · refine congr_arg b.repr (Finset.sum_congr rfl ?_)
      simp only [Finsupp.mem_support_iff]
      intro i hi
      rw [hj i hi, zero_smul]
    · simp only [Finset.sum_const_zero, map_zero]
  -- And `G` such that `∑ₛ aᵢⱼfᵢ = ∑ Gᵢⱼbⱼ`, where `aᵢⱼ` are the coefficients `bᵢx = ∑ aᵢⱼbⱼ`.
  let G : I →₀ I →₀ R := Finsupp.onFinset (Finset.biUnion f.support (fun i ↦ (a i).support))
    (fun j ↦ b.repr (f.sum (fun i y ↦ a i j • y)))
    (fun j ↦ not_imp_comm.mp (hG j))
  -- Then `∑ Fᵢⱼ(bⱼ ⊗ bᵢ) = ∑ fⱼx ⊗ bᵢ = ∑ fⱼ ⊗ xbᵢ = ∑ aᵢⱼ(fⱼ ⊗ bᵢ) = ∑ Gᵢⱼ(bⱼ ⊗ bᵢ)`.
  -- Since `bⱼ ⊗ bᵢ` forms an `R`-basis of `S ⊗ S`, we conclude that `F = G`.
  have : F = G := by
    apply Finsupp.curryEquiv.symm.injective
    apply (Finsupp.equivCongrLeft (Equiv.prodComm I I)).injective
    apply (b.tensorProduct b).repr.symm.injective
    suffices (F.sum fun a f ↦ f.sum fun b' c ↦ c • b b' ⊗ₜ[R] b a) =
        G.sum fun a f ↦ f.sum fun b' c ↦ c • b b' ⊗ₜ[R] b a by
      simpa [Finsupp.linearCombination_apply, Finsupp.sum_uncurry_index]
    have : ∀ i, ((b.repr (x * f i)).sum fun j k ↦ k • b j ⊗ₜ[R] b i) = (x * f i) ⊗ₜ[R] b i := by
      intro i
      simp_rw [Finsupp.sum, TensorProduct.smul_tmul', ← TensorProduct.sum_tmul]
      congr 1
      exact b.linearCombination_repr _
    rw [Finsupp.onFinset_sum, Finsupp.onFinset_sum]
    · trans (x ⊗ₜ 1) * elem R S
      · simp_rw [this, hf, Finsupp.sum, Finset.mul_sum, TensorProduct.tmul_mul_tmul, one_mul]
      · rw [← one_tmul_mul_elem, hf, finite_of_free_aux]
        rfl
    · intro; simp
    · intro; simp
  -- In particular, `fⱼx = ∑ Fᵢⱼbⱼ = ∑ Gᵢⱼbⱼ = ∑ₛ aᵢⱼfᵢ` for all `j`.
  have : ∀ j, x * f j = f.sum fun i y ↦ a i j • y := by
    intro j
    apply b.repr.injective
    exact DFunLike.congr_fun this j
  -- Since `∑ₛ fⱼbⱼ = 1`, `x = ∑ₛ aᵢⱼfᵢbⱼ` is indeed in the span of `{ fᵢbⱼ | i, j ∈ s }`.
  rw [← mul_one x, ← @lmul_elem R, hf, map_finsuppSum, Finsupp.sum, Finset.mul_sum]
  simp only [TensorProduct.lmul'_apply_tmul, Finset.coe_image₂, ← mul_assoc, this,
    Finsupp.sum, Finset.sum_mul, smul_mul_assoc]
  apply Submodule.sum_mem; intro i hi
  apply Submodule.sum_mem; intro j hj
  apply Submodule.smul_mem
  apply Submodule.subset_span
  use j, hj, i, hi

/--
Proposition I.2.3 of [iversen]
If `S` is an unramified `R`-algebra, and `M` is an `S`-module, then the map
`S ⊗[R] M →ₗ[S] M` taking `(b, m) ↦ b • m` admits an `S`-linear section. -/
noncomputable
/-
**Algebra.FormallyUnramified.sec** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.FormallyUnra
mified`。
形式化陈述：sec : M ->ₗ[S] S otimes[R] M where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def sec :
    M →ₗ[S] S ⊗[R] M where
  __ := ((TensorProduct.AlgebraTensorModule.mapBilinear R S S S S S M
    LinearMap.id).flip (elem R S)).comp (lsmul R R M).toLinearMap.flip
  map_smul' r m := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.flip_apply, TensorProduct.AlgebraTensorModule.mapBilinear_apply, RingHom.id_apply]
    trans (TensorProduct.AlgebraTensorModule.map (LinearMap.id (R := S) (M := S))
      ((LinearMap.flip (AlgHom.toLinearMap (lsmul R R M))) m)) ((1 ⊗ₜ r) * elem R S)
    · induction elem R S using TensorProduct.induction_on
      · simp
      · simp [smul_comm r]
      · simp only [map_add, mul_add, *]
    · have := one_tmul_sub_tmul_one_mul_elem (R := R) r
      rw [sub_mul, sub_eq_zero] at this
      rw [this]
      induction elem R S using TensorProduct.induction_on
      · simp
      · simp [TensorProduct.smul_tmul']
      · simp only [map_add, smul_add, mul_add, *]
/-
**Algebra.FormallyUnramified.comp_sec** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Formall
yUnramified`。
形式化陈述：comp_sec : (TensorProduct.AlgebraTensorModule.lift ((lsmul S S M).toLinear
Map.flip.restrictScalars R).flip).comp (sec R S M) = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
（共 34 条，此处仅展示前 30 条）
-/
lemma comp_sec :
    (TensorProduct.AlgebraTensorModule.lift
      ((lsmul S S M).toLinearMap.flip.restrictScalars R).flip).comp (sec R S M) =
      LinearMap.id := by
  ext x
  simp only [sec, LinearMap.coe_comp, LinearMap.coe_mk, LinearMap.coe_toAddHom,
    Function.comp_apply, LinearMap.flip_apply, TensorProduct.AlgebraTensorModule.mapBilinear_apply,
    TensorProduct.AlgebraTensorModule.lift_apply, LinearMap.id_coe, id_eq]
  trans (TensorProduct.lmul' R (elem R S)) • x
  · induction elem R S using TensorProduct.induction_on with
    | zero => simp
    | tmul r s => simp [mul_smul, smul_comm r s]
    | add y z hy hz => simp [hy, hz, add_smul]
  · rw [lmul_elem, one_smul]

/-- If `S` is an unramified `R`-algebra, then `R`-flat implies `S`-flat. Iversen I.2.7 -/
/-
**Algebra.FormallyUnramified.flat_of_restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 `
Algebra.FormallyUnramified`。
形式化陈述：flat_of_restrictScalars [Module.Flat R M] : Module.Flat S M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Flat.of_retract`：of_retract [f : Flat R M] (i : N ->ₗ[R] M) (r : 
M ->ₗ[R] N) (h : r.comp i = LinearMap.id) : Flat R N
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用引理 `Algebra.FormallyUnramified.comp_sec`：comp_sec : (TensorProduct.AlgebraTe
nsorModule.lift ((lsmul S S M).toLinearMap.flip.restrictScalars R).flip).comp (s
ec R S M) = LinearMap.id

--- 原说明 ---
If `S` is an unramified `R`-algebra, then `R`-flat implies `S`-flat. Iversen I.2
.7
-/
lemma flat_of_restrictScalars [Module.Flat R M] : Module.Flat S M :=
  Module.Flat.of_retract _ _ (comp_sec R S M)

/-- If `S` is an unramified `R`-algebra, then `R`-projective implies `S`-projective. -/
/-
**Algebra.FormallyUnramified.projective_of_restrictScalars** 是 Mathlib 中的一个引理，位于
命名空间 `Algebra.FormallyUnramified`。
形式化陈述：projective_of_restrictScalars [Module.Projective R M] : Module.Projective 
S M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Projective.of_split`：∀ {R : Type u_1} [inst : Semiring R] {P : Ty
pe u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   {M : Type u_3}
 [inst_3 : AddCo…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Projective.tensorProduct`：∀ {R : Type u} [inst : Semiring R] {R₀ 
: Type u_2} {M : Type u_1} {N : Type u_3} [inst_1 : CommSemiring R₀]   [inst_2 :
 Algebra R₀ R] [inst_…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用引理 `Algebra.FormallyUnramified.comp_sec`：comp_sec : (TensorProduct.AlgebraTe
nsorModule.lift ((lsmul S S M).toLinearMap.flip.restrictScalars R).flip).comp (s
ec R S M) = LinearMap.id

--- 原说明 ---
If `S` is an unramified `R`-algebra, then `R`-projective implies `S`-projective.
-/
lemma projective_of_restrictScalars [Module.Projective R M] : Module.Projective S M :=
  Module.Projective.of_split _ _ (comp_sec R S M)

end Algebra.FormallyUnramified

