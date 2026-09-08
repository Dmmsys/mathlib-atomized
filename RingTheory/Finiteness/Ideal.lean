/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Finitely generated ideals

Lemmas about finiteness of ideal operations.
-/

public section

namespace Ideal

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- The image of a finitely generated ideal is finitely generated.

This is the `Ideal` version of `Submodule.FG.map`. -/
/-
**Ideal.FG.map** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.FG`。
形式化陈述：∀ {R : Type u_3} {S : Type u_4} [inst : Semiring R] [inst_1 : Semiring S] 
{I : Ideal R},   I.FG → ∀ (f : R →+* S), (Ideal.map f I).FG
参数：f : R →+* S；Ideal.map f I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)

--- 原说明 ---
The image of a finitely generated ideal is finitely generated.

This is the `Ideal` version of `Submodule.FG.map`.
-/
theorem FG.map {R S : Type*} [Semiring R] [Semiring S] {I : Ideal R} (h : I.FG) (f : R →+* S) :
    (I.map f).FG := by
  classical
    obtain ⟨s, hs⟩ := h
    refine ⟨s.image f, ?_⟩
    rw [Finset.coe_image, ← map_span, hs]
/-
**Ideal.fg_ker_comp** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：fg_ker_comp {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] (f : R 
->+* S) (g : S ->+* A) (hf : (RingHom.ker f).FG) (hg : (RingHom.ker g).FG) (hsur
 : Function.Surjective f) : (RingHom.ker (g.comp f)).FG
参数：f : R ->+* S；g : S ->+* A；hf : (RingHom.ker f).FG；hg : (RingHom.ker g).FG；hsu
r : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `Submodule.fg_ker_comp`：fg_ker_comp (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (hf
1 : (LinearMap.ker f).FG) (hf2 : (LinearMap.ker g).FG) (hsur : Function.Surjecti
ve f) : (Li…
· 使用定理 `Submodule.FG.restrictScalars_of_surjective`：∀ {R : Type u_4} {A : Type u
_5} {M : Type u_6} [inst : Semiring A] [inst_1 : AddCommMonoid M]   [inst_2 : _r
oot_.Module A M] {S : Submodule …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem fg_ker_comp {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] (f : R →+* S)
    (g : S →+* A) (hf : (RingHom.ker f).FG) (hg : (RingHom.ker g).FG)
    (hsur : Function.Surjective f) :
    (RingHom.ker (g.comp f)).FG := by
  let : Algebra R S := RingHom.toAlgebra f
  let : Algebra R A := RingHom.toAlgebra (g.comp f)
  let : Algebra S A := RingHom.toAlgebra g
  let : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f₁ := Algebra.linearMap R S
  let g₁ := (IsScalarTower.toAlgHom R S A).toLinearMap
  exact Submodule.fg_ker_comp f₁ g₁ hf
    (Submodule.FG.restrictScalars_of_surjective hg hsur) hsur

/-- Let `f : R →+* S` be a surjective ring homomorphism, and let `I` be an ideal of `R`. If `f(I)`
and `I ∩ ker(f)` are finitely generated ideals, then `I` is also finitely generated. -/
/-
**Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Idea
l`。
形式化陈述：fg_of_fg_map_of_fg_inf_ker_of_surjective {R S : Type*} [CommRing R] [CommR
ing S] {f : R ->+* S} {I : Ideal R} (hmap : (I.map f).FG) (hk : (I ⊓ (RingHom.ke
r f)).FG) (hf : Function.Surjective f) : I.FG
参数：hmap : (I.map f).FG；hk : (I ⊓ (RingHom.ker f)).FG；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.fg_of_fg_map_of_fg_inf_ker`：fg_of_fg_map_of_fg_inf_ker (f : M 
->ₗ[R] P) {s : Submodule R M} (hs1 : (s.map f).FG) (hs2 : (s ⊓ LinearMap.ker f).
FG) : s.FG
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.restrictScalars.congr_simp`：∀ (S : Type u_1) {R : Type u_2} {M
 : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : Semiring S
]   [inst_3 : _root_.Modul…
· 使用定理 `Ideal.map_eq_submodule_map`：map_eq_submodule_map (f : R ->+* S) [h : Rin
gHomSurjective f] (I : Ideal R) : I.map f = Submodule.map f.toSemilinearMap I
· 使用定理 `Submodule.FG.restrictScalars_of_surjective`：∀ {R : Type u_4} {A : Type u
_5} {M : Type u_6} [inst : Semiring A] [inst_1 : AddCommMonoid M]   [inst_2 : _r
oot_.Module A M] {S : Submodule …

--- 原说明 ---
Let `f : R →+* S` be a surjective ring homomorphism, and let `I` be an ideal of 
`R`. If `f(I)`
and `I ∩ ker(f)` are finitely generated ideals, then `I` is also finitely genera
ted.
-/
theorem fg_of_fg_map_of_fg_inf_ker_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    {f : R →+* S} {I : Ideal R} (hmap : (I.map f).FG) (hk : (I ⊓ (RingHom.ker f)).FG)
    (hf : Function.Surjective f) : I.FG := by
  algebraize [f]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (Module.compHom.toLinearMap f) ?_ hk
  have : RingHomSurjective f := ⟨hf⟩
  simpa [Ideal.map_eq_submodule_map] using! Submodule.FG.restrictScalars_of_surjective hmap hf
/-
**Ideal.exists_radical_pow_le_of_fg** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：exists_radical_pow_le_of_fg {R : Type*} [CommSemiring R] (I : Ideal R) (h 
: I.radical.FG) : exists n : Nat, I.radical ^ n <= I
参数：I : Ideal R；h : I.radical.FG。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.fg_induction`：fg_induction {R M : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] {motive : forall N : Submodule R M, N.FG -> Prop} (single
ton : forall…
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span.eq_1`：∀ {α : Type u} [inst : Semiring α] (s : Set α), Ideal.s
pan s = Submodule.span α s
· 使用定理 `Ideal.span_singleton_pow`：span_singleton_pow (s : R) [(span {s}).IsTwoSi
ded] (n : Nat) : span {s} ^ n = (span {s ^ n} : Ideal R)
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Ideal.mem_sup_left`：mem_sup_left {S T : Ideal R} : forall {x : R}, x in 
S -> x in S ⊔ T
· 使用定理 `Ideal.mem_sup_right`：mem_sup_right {S T : Ideal R} : forall {x : R}, x i
n T -> x in S ⊔ T
· 使用定理 `Ideal.add_eq_sup`：add_eq_sup {I J : Ideal R} : I + J = I ⊔ J
· 使用定理 `add_pow`：add_pow [CommSemiring R] (x y : R) (n : Nat) : (x + y) ^ n = ∑ 
m in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `Ideal.sum_eq_sup`：sum_eq_sup {ι : Type*} (s : Finset ι) (f : ι -> Ideal 
R) : s.sum f = s.sup f
· 使用定理 `Finset.sup_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   s.sup f ≤ a ↔ ∀
 b ∈ s,…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ideal.mul_le_left`：mul_le_left [I.IsTwoSided] : I * J <= I
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用定理 `Ideal.mul_le_right`：mul_le_right : I * J <= J
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem exists_radical_pow_le_of_fg {R : Type*} [CommSemiring R] (I : Ideal R) (h : I.radical.FG) :
    ∃ n : ℕ, I.radical ^ n ≤ I := by
  suffices hJ : ∀ J : Ideal R, J.FG → J ≤ I.radical → ∃ n : ℕ, J ^ n ≤ I by
    simpa using hJ I.radical h
  intro J hJ hJK
  induction J, hJ using Submodule.fg_induction with
  | singleton x =>
    obtain ⟨n, hn⟩ := hJK (subset_span (Set.mem_singleton x))
    exact ⟨n, by rwa [← span, span_singleton_pow, span_le, Set.singleton_subset_iff]⟩
  | sup J K _ _ hJ hK =>
    obtain ⟨n, hn⟩ := hJ fun x hx => hJK <| mem_sup_left hx
    obtain ⟨m, hm⟩ := hK fun x hx => hJK <| mem_sup_right hx
    use n + m
    rw [← add_eq_sup, add_pow, sum_eq_sup, Finset.sup_le_iff]
    refine fun i _ => mul_le_left.trans ?_
    obtain h | h := le_or_gt n i
    · exact mul_le_left.trans ((pow_le_pow_right h).trans hn)
    · exact mul_le_right.trans ((pow_le_pow_right (by lia)).trans hm)
/-
**Ideal.exists_pow_le_of_le_radical_of_fg_radical** 是 Mathlib 中的一个定理，位于命名空间 `Ide
al`。
形式化陈述：exists_pow_le_of_le_radical_of_fg_radical {R : Type*} [CommSemiring R] {I 
J : Ideal R} (hIJ : I <= J.radical) (hJ : J.radical.FG) : exists k : Nat, I ^ k 
<= J
参数：hIJ : I <= J.radical；hJ : J.radical.FG。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.exists_radical_pow_le_of_fg`：exists_radical_pow_le_of_fg {R : Type
*} [CommSemiring R] (I : Ideal R) (h : I.radical.FG) : exists n : Nat, I.radical
 ^ n <= I
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ideal.pow_right_mono`：pow_right_mono (e : I <= J) (n : Nat) : I ^ n <= J
 ^ n
-/
theorem exists_pow_le_of_le_radical_of_fg_radical {R : Type*} [CommSemiring R] {I J : Ideal R}
    (hIJ : I ≤ J.radical) (hJ : J.radical.FG) :
    ∃ k : ℕ, I ^ k ≤ J := by
  obtain ⟨k, hk⟩ := J.exists_radical_pow_le_of_fg hJ
  exact ⟨k, (pow_right_mono hIJ k).trans hk⟩
/-
**Ideal.exists_pow_le_of_le_radical_of_fg** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：exists_pow_le_of_le_radical_of_fg {R : Type*} [CommSemiring R] {I J : Idea
l R} (h' : I <= J.radical) (h : I.FG) : exists n : Nat, I ^ n <= J
参数：h' : I <= J.radical；h : I.FG。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.fg_induction`：fg_induction {R M : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] {motive : forall N : Submodule R M, N.FG -> Prop} (single
ton : forall…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.submodule_span_eq`：submodule_span_eq {s : Set α} : Submodule.span 
α s = Ideal.span s
· 使用定理 `Ideal.span_singleton_pow`：span_singleton_pow (s : R) [(span {s}).IsTwoSi
ded] (n : Nat) : span {s} ^ n = (span {s ^ n} : Ideal R)
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用引理 `Ideal.sup_pow_add_le_pow_sup_pow`：sup_pow_add_le_pow_sup_pow {n m : Nat}
 : (I ⊔ J) ^ (n + m) <= I ^ n ⊔ J ^ m
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
-/
lemma exists_pow_le_of_le_radical_of_fg {R : Type*} [CommSemiring R] {I J : Ideal R}
    (h' : I ≤ J.radical) (h : I.FG) :
    ∃ n : ℕ, I ^ n ≤ J := by
  induction I, h using Submodule.fg_induction with
  | singleton x =>
    simp only [submodule_span_eq, span_le, Set.singleton_subset_iff, SetLike.mem_coe] at h'
    obtain ⟨n, hn⟩ := h'
    refine ⟨n, by simpa [span_singleton_pow, span_le]⟩
  | sup I₁ I₂ _ _ h₁ h₂ =>
    obtain ⟨n₁, hn₁⟩ := h₁ (le_sup_left.trans h')
    obtain ⟨n₂, hn₂⟩ := h₂ (le_sup_right.trans h')
    use n₁ + n₂
    exact sup_pow_add_le_pow_sup_pow.trans (sup_le hn₁ hn₂)
/-
**Ideal._root_.Submodule.FG.smul** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Submodule.FG.smul {I : Ideal R} [I.IsTwoSided] {N : Submodule R M}
    (hI : I.FG) (hN : N.FG) : (I • N).FG := by
  obtain ⟨s, rfl⟩ := hI
  obtain ⟨t, rfl⟩ := hN
  classical rw [Submodule.span_smul_span, ← s.coe_smul]
  exact ⟨_, rfl⟩
/-
**Ideal.FG.mul** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.FG`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {I J : Ideal R} [I.IsTwoSided], I.FG 
→ J.FG → (I * J).FG
参数：I * J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.FG.smul`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I : Ideal R} [I.IsTwoS
ided] {…
-/
theorem FG.mul {I J : Ideal R} [I.IsTwoSided] (hI : I.FG) (hJ : J.FG) : (I * J).FG :=
  Submodule.FG.smul hI hJ
/-
**Ideal.FG.pow** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.FG`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {I : Ideal R} [I.IsTwoSided] {n : ℕ},
 I.FG → (I ^ n).FG
参数：I ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.pow_zero`：∀ {R : Type u} [inst : Semiring R] {A : Type v} [ins
t_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower R A A] 
(M : Sub…
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Ideal.fg_top`：∀ (R : Type u_1) [inst : Semiring R], ⊤.FG
· 使用定理 `Ideal.IsTwoSided.pow_succ`：∀ {R : Type u} [inst : Semiring R] {I : Ideal
 R} [I.IsTwoSided] (n : ℕ), I ^ (n + 1) = I * I ^ n
· 使用定理 `Ideal.FG.mul`：∀ {R : Type u_1} [inst : Semiring R] {I J : Ideal R} [I.Is
TwoSided], I.FG → J.FG → (I * J).FG
-/
theorem FG.pow {I : Ideal R} [I.IsTwoSided] {n : ℕ} (hI : I.FG) : (I ^ n).FG :=
  n.rec (by rw [I.pow_zero, one_eq_top]; exact fg_top R) fun n ih ↦ by
    rw [IsTwoSided.pow_succ]
    exact hI.mul ih

end Ideal

