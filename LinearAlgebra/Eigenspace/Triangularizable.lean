/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Triangularizable linear endomorphisms

This file contains basic results relevant to the triangularizability of linear endomorphisms.

## Main definitions / results

* `Module.End.exists_eigenvalue`: in finite dimensions, over an algebraically closed field, every
  linear endomorphism has an eigenvalue.
* `Module.End.iSup_genEigenspace_eq_top`: in finite dimensions, over an algebraically
  closed field, the generalized eigenspaces of any linear endomorphism span the whole space.
* `Module.End.iSup_genEigenspace_restrict_eq_top`: in finite dimensions, if the
  generalized eigenspaces of a linear endomorphism span the whole space then the same is true of
  its restriction to any invariant submodule.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2024]
* https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors

## TODO

Define triangularizable endomorphisms (e.g., as existence of a maximal chain of invariant subspaces)
and prove that in finite dimensions over a field, this is equivalent to the property that the
generalized eigenspaces span the whole space.

## Tags

eigenspace, eigenvector, eigenvalue, eigen
-/

public section

open Set Function Module Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace Module.End

/-
**Module.End.exists_hasEigenvalue_of_genEigenspace_eq_top** 是 Mathlib 中的一个定理，位于命
名空间 `Module.End`。
形式化陈述：exists_hasEigenvalue_of_genEigenspace_eq_top [Nontrivial M] {f : End R M} 
(k : Nat∞) (hf : ⨆ μ, f.genEigenspace μ k = ⊤) : exists μ, f.HasEigenvalue μ
参数：k : Nat∞；hf : ⨆ μ, f.genEigenspace μ k = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.instNontrivial`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial M], 
Nontrivial (Su…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Module.End.HasUnifEigenvalue.lt`：∀ {R : Type v} {M : Type w} [inst : Com
mRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {f : Module.En
d R M} {μ : R} {k m :…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem exists_hasEigenvalue_of_genEigenspace_eq_top [Nontrivial M] {f : End R M} (k : ℕ∞)
    (hf : ⨆ μ, f.genEigenspace μ k = ⊤) :
    ∃ μ, f.HasEigenvalue μ := by
  suffices ∃ μ, f.HasUnifEigenvalue μ k by
    peel this with μ hμ
    exact HasUnifEigenvalue.lt zero_lt_one hμ
  simp [HasUnifEigenvalue, ← not_forall, ← iSup_eq_bot, hf]

-- This is Lemma 5.19 of [axler2024], although we are no longer following that proof.
/-- In finite dimensions, over an algebraically closed field, every linear endomorphism has an
eigenvalue. -/
/-
**Module.End.exists_eigenvalue** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：exists_eigenvalue [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (
f : End K V) : exists c : K, f.HasEigenvalue c
参数：f : End K V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `spectrum.nonempty_of_isAlgClosed_of_finiteDimensional`：nonempty_of_isAlg
Closed_of_finiteDimensional [IsAlgClosed 𝕜] [Nontrivial A] [I : FiniteDimensiona
l 𝕜 A] (a : A) : (σ a).Nonempty
· 使用定理 `instNontrivialLinearMapId`：∀ {K : Type u_3} {V : Type u_4} {V' : Type u_
5} [inst : DivisionRing K] [inst_1 : AddCommGroup V]   [inst_2 : AddCommGroup V'
] [inst_3 : _ro…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V

--- 原说明 ---
In finite dimensions, over an algebraically closed field, every linear endomorph
ism has an
eigenvalue.
-/
theorem exists_eigenvalue [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : End K V) :
    ∃ c : K, f.HasEigenvalue c := by
  simp_rw [hasEigenvalue_iff_mem_spectrum]
  exact spectrum.nonempty_of_isAlgClosed_of_finiteDimensional K f
/-
**Module.End.** 是 Mathlib 中的一个实例，位于命名空间 `Module.End`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : End K V) :
    Inhabited f.Eigenvalues :=
  ⟨⟨f.exists_eigenvalue.choose, f.exists_eigenvalue.choose_spec⟩⟩

-- Lemma 8.22(c) of [axler2024]
/-- In finite dimensions, over an algebraically closed field, the generalized eigenspaces of any
linear endomorphism span the whole space. -/
/-
**Module.End.iSup_maxGenEigenspace_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`
。
形式化陈述：iSup_maxGenEigenspace_eq_top [IsAlgClosed K] [FiniteDimensional K V] (f : 
End K V) : ⨆ (μ : K), f.maxGenEigenspace μ = ⊤
参数：f : End K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.finrank_eq_zero`：Submodule.finrank_eq_zero [StrongRankConditio
n R] {S : Submodule R M} [Module.Finite R S] : finrank R S = 0 ↔ S = ⊥
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `finrank_top`：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M
· 使用定理 `Module.finrank_pos_iff`：Module.finrank_pos_iff [IsDomain R] [IsTorsionFr
ee R M] : 0 < finrank R M ↔ Nontrivial M
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Module.End.exists_eigenvalue`：exists_eigenvalue [IsAlgClosed K] [FiniteD
imensional K V] [Nontrivial V] (f : End K V) : exists c : K, f.HasEigenvalue c
· 使用定理 `Module.End.map_genEigenrange_le`：map_genEigenrange_le {f : End K V} {μ :
 K} {n : Nat} : Submodule.map f (f.genEigenrange μ n) <= f.genEigenrange μ n
· 使用定理 `Submodule.mem_map_of_mem`：mem_map_of_mem {f : M ->ₛₗ[σ₁₂] M₂} {p : Submo
dule R M} {r} (h : r in p) : f r in map f p
· 使用定理 `Module.End.pos_finrank_genEigenspace_of_hasEigenvalue`：pos_finrank_genEi
genspace_of_hasEigenvalue [FiniteDimensional K V] {f : End K V} {k : Nat} {μ : K
} (hx : f.HasEigenvalue μ) (hk : 0 < k) : 0…
· 使用引理 `Module.End.genEigenspace_nat`：genEigenspace_nat {f : End R M} {μ : R} {k
 : Nat} : f.genEigenspace μ k = LinearMap.ker ((f - μ • 1) ^ k)
· 使用引理 `Module.End.genEigenrange_nat`：genEigenrange_nat {f : End R M} {μ : R} {k
 : Nat} : f.genEigenrange μ k = LinearMap.range ((f - μ • 1) ^ k)
· 使用定理 `LinearMap.finrank_range_add_finrank_ker`：finrank_range_add_finrank_ker [
FiniteDimensional K V] (f : V ->ₗ[K] V₂) : finrank K (LinearMap.range f) + finra
nk K (LinearMap.ker f) = finr…
· 使用定理 `Submodule.map_iSup`：map_iSup {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι -> 
Submodule R M) : map f (⨆ i, p i) = ⨆ i, map f (p i)
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Submodule.map_subtype_top`：map_subtype_top : map p.subtype (⊤ : Submodul
e R p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.End.maxGenEigenspace.eq_1`：∀ {R : Type v} {M : Type w} [inst : Co
mmRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (f : Module.E
nd R M) (μ : R), f.max…
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
In finite dimensions, over an algebraically closed field, the generalized eigens
paces of any
linear endomorphism span the whole space.
-/
theorem iSup_maxGenEigenspace_eq_top [IsAlgClosed K] [FiniteDimensional K V] (f : End K V) :
    ⨆ (μ : K), f.maxGenEigenspace μ = ⊤ := by
  -- We prove the claim by strong induction on the dimension of the vector space.
  suffices ∀ n, finrank K V = n → ⨆ (μ : K), f.maxGenEigenspace μ = ⊤ by exact this _ rfl
  intro n h_dim
  induction n using Nat.strong_induction_on generalizing V with | h n ih =>
  rcases n with - | n
  -- If the vector space is 0-dimensional, the result is trivial.
  · rw [← top_le_iff]
    simp only [Submodule.finrank_eq_zero.1 (Eq.trans (finrank_top _ _) h_dim), bot_le]
  -- Otherwise the vector space is nontrivial.
  · have : Nontrivial V := finrank_pos_iff.1 (by rw [h_dim]; apply Nat.zero_lt_succ)
    -- Hence, `f` has an eigenvalue `μ₀`.
    obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀, f.HasEigenvalue μ₀ := exists_eigenvalue f
    -- We define `ES` to be the generalized eigenspace
    let ES := f.genEigenspace μ₀ (finrank K V)
    -- and `ER` to be the generalized eigenrange.
    let ER := f.genEigenrange μ₀ (finrank K V)
    -- `f` maps `ER` into itself.
    have h_f_ER : ∀ x : V, x ∈ ER → f x ∈ ER := fun x hx =>
      map_genEigenrange_le (Submodule.mem_map_of_mem hx)
    -- Therefore, we can define the restriction `f'` of `f` to `ER`.
    let f' : End K ER := f.restrict h_f_ER
    -- The dimension of `ES` is positive
    have h_dim_ES_pos : 0 < finrank K ES := by
      dsimp +instances only [ES]
      rw [h_dim]
      apply pos_finrank_genEigenspace_of_hasEigenvalue hμ₀ (Nat.zero_lt_succ n)
    -- and the dimensions of `ES` and `ER` add up to `finrank K V`.
    have h_dim_add : finrank K ER + finrank K ES = finrank K V := by
      dsimp +instances only [ER, ES]
      rw [Module.End.genEigenspace_nat, Module.End.genEigenrange_nat]
      apply LinearMap.finrank_range_add_finrank_ker
    -- Therefore the dimension `ER` mus be smaller than `finrank K V`.
    have h_dim_ER : finrank K ER < n.succ := by lia
    -- This allows us to apply the induction hypothesis on `ER`:
    have ih_ER : ⨆ (μ : K), f'.maxGenEigenspace μ = ⊤ :=
      ih (finrank K ER) h_dim_ER f' rfl
    -- The induction hypothesis gives us a statement about subspaces of `ER`. We can transfer this
    -- to a statement about subspaces of `V` via `Submodule.subtype`:
    have ih_ER' : ⨆ (μ : K), (f'.maxGenEigenspace μ).map ER.subtype = ER := by
      simp only [(Submodule.map_iSup _ _).symm, ih_ER, Submodule.map_subtype_top ER]
    -- Moreover, every generalized eigenspace of `f'` is contained in the corresponding generalized
    -- eigenspace of `f`.
    have hff' :
      ∀ μ, (f'.maxGenEigenspace μ).map ER.subtype ≤ f.maxGenEigenspace μ := by
      intros
      rw [maxGenEigenspace, genEigenspace_restrict]
      apply Submodule.map_comap_le
    -- It follows that `ER` is contained in the span of all generalized eigenvectors.
    have hER : ER ≤ ⨆ (μ : K), f.maxGenEigenspace μ := by
      rw [← ih_ER']
      exact iSup_mono hff'
    -- `ES` is contained in this span by definition.
    have hES : ES ≤ ⨆ (μ : K), f.maxGenEigenspace μ :=
      ((f.genEigenspace μ₀).mono le_top).trans (le_iSup f.maxGenEigenspace μ₀)
    -- Moreover, we know that `ER` and `ES` are disjoint.
    have h_disjoint : Disjoint ER ES := generalized_eigenvec_disjoint_range_ker f μ₀
    -- Since the dimensions of `ER` and `ES` add up to the dimension of `V`, it follows that the
    -- span of all generalized eigenvectors is all of `V`.
    change ⨆ (μ : K), f.maxGenEigenspace μ = ⊤
    rw [← top_le_iff, ← Submodule.eq_top_of_disjoint ER ES h_dim_add.ge h_disjoint]
    apply sup_le hER hES

end Module.End

namespace Submodule

variable {p : Submodule K V} {f : Module.End K V}

set_option backward.isDefEq.respectTransparency.types false in
/-
**Submodule.inf_iSup_genEigenspace** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：inf_iSup_genEigenspace [FiniteDimensional K V] (h : forall x in p, f x in 
p) (k : Nat∞) : p ⊓ ⨆ μ, f.genEigenspace μ k = ⨆ μ, p ⊓ f.genEigenspace μ k
参数：h : forall x in p, f x in p；k : Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Submodule.mem_iSup_iff_exists_finsupp`：mem_iSup_iff_exists_finsupp (p : 
ι -> Submodule R N) (x : N) : x in iSup p ↔ exists (f : ι ->₀ N), (forall i, f i
 in p i) ∧ (f.sum fun _i xi…
· 使用定理 `Commute.pow_pow`：pow_pow (h : Commute a b) (m n : Nat) : Commute (a ^ m)
 (b ^ n)
· 使用定理 `Commute.sub_left`：sub_left : Commute a c -> Commute b c -> Commute (a - 
b) c
· 使用定理 `Commute.sub_right`：sub_right : Commute a b -> Commute a c -> Commute a (
b - c)
· 使用引理 `Algebra.commute_algebraMap_right`：commute_algebraMap_right (r : R) (x : 
A) : Commute x (algebraMap R A r)
· 使用引理 `Algebra.commute_algebraMap_left`：commute_algebraMap_left (r : R) (x : A)
 : Commute (algebraMap R A r) x
· 使用定理 `Finset.noncommProd_commute`：noncommProd_commute (s : Finset α) (f : α ->
 β) (comm) (y : β) (h : forall x in s, Commute y (f x)) : Commute y (s.noncommPr
od f comm)
· 使用定理 `Commute.pow_right`：pow_right (h : Commute a b) (n : Nat) : Commute a (b 
^ n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用引理 `Module.End.mem_genEigenspace_nat`：mem_genEigenspace_nat {f : End R M} {μ
 : R} {k : Nat} {x : M} : x in f.genEigenspace μ k ↔ x in LinearMap.ker ((f - μ 
• 1) ^ k)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `OrderHom.mono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst
_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.noncommProd_erase_mul`：noncommProd_erase_mul [DecidableEq α] (s :
 Finset α) {a : α} (h : a in s) (f : α -> β) (comm) (comm'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `Module.End.mul_apply`：mul_apply (f g : Module.End R M) (x : M) : (f * g)
 x = f (g x)
（共 82 条，此处仅展示前 30 条）
-/
theorem inf_iSup_genEigenspace [FiniteDimensional K V] (h : ∀ x ∈ p, f x ∈ p) (k : ℕ∞) :
    p ⊓ ⨆ μ, f.genEigenspace μ k = ⨆ μ, p ⊓ f.genEigenspace μ k := by
  refine le_antisymm (fun m hm ↦ ?_)
    (le_inf_iff.mpr ⟨iSup_le fun μ ↦ inf_le_left, iSup_mono fun μ ↦ inf_le_right⟩)
  classical
  obtain ⟨hm₀ : m ∈ p, hm₁ : m ∈ ⨆ μ, f.genEigenspace μ k⟩ := hm
  obtain ⟨m, hm₂, rfl⟩ := (mem_iSup_iff_exists_finsupp _ _).mp hm₁
  suffices ∀ μ, (m μ : V) ∈ p by
    exact (mem_iSup_iff_exists_finsupp _ _).mpr ⟨m, fun μ ↦ mem_inf.mp ⟨this μ, hm₂ μ⟩, rfl⟩
  intro μ
  by_cases hμ : μ ∈ m.support; swap
  · simp only [Finsupp.notMem_support_iff.mp hμ, p.zero_mem]
  have hm₂_aux := hm₂
  simp_rw [Module.End.mem_genEigenspace] at hm₂_aux
  choose l hlk hl using hm₂_aux
  let l₀ : ℕ := m.support.sup l
  have h_comm : ∀ (μ₁ μ₂ : K),
    Commute ((f - algebraMap K (End K V) μ₁) ^ l₀)
            ((f - algebraMap K (End K V) μ₂) ^ l₀) := fun μ₁ μ₂ ↦
    ((Commute.sub_right rfl <| Algebra.commute_algebraMap_right _ _).sub_left
      (Algebra.commute_algebraMap_left _ _)).pow_pow _ _
  let g : End K V := (m.support.erase μ).noncommProd _ fun μ₁ _ μ₂ _ _ ↦ h_comm μ₁ μ₂
  have hfg : Commute f g := Finset.noncommProd_commute _ _ _ _ fun μ' _ ↦
    (Commute.sub_right rfl <| Algebra.commute_algebraMap_right _ _).pow_right _
  have hg₀ : g (m.sum fun _μ mμ ↦ mμ) = g (m μ) := by
    suffices ∀ μ' ∈ m.support, g (m μ') = if μ' = μ then g (m μ) else 0 by
      rw [map_finsuppSum, Finsupp.sum_congr (g2 := fun μ' _ ↦ if μ' = μ then g (m μ) else 0) this,
        Finsupp.sum_ite_eq', if_pos hμ]
    rintro μ' hμ'
    split_ifs with hμμ'
    · rw [hμμ']
    have hl₀ : ((f - algebraMap K (End K V) μ') ^ l₀) (m μ') = 0 := by
      rw [← LinearMap.mem_ker, Algebra.algebraMap_eq_smul_one, ← End.mem_genEigenspace_nat]
      simp_rw [← End.mem_genEigenspace_nat] at hl
      suffices (l μ' : ℕ∞) ≤ l₀ from (f.genEigenspace μ').mono this (hl μ')
      simpa only [Nat.cast_le] using Finset.le_sup hμ'
    have : _ = g := (m.support.erase μ).noncommProd_erase_mul (Finset.mem_erase.mpr ⟨hμμ', hμ'⟩)
      (fun μ ↦ (f - algebraMap K (End K V) μ) ^ l₀) (fun μ₁ _ μ₂ _ _ ↦ h_comm μ₁ μ₂)
    rw [← this, Module.End.mul_apply, hl₀, _root_.map_zero]
  have hg₁ : MapsTo g p p := Finset.noncommProd_induction _ _ _ (fun g' : End K V ↦ MapsTo g' p p)
      (fun f₁ f₂ ↦ MapsTo.comp) (mapsTo_id _) fun μ' _ ↦ by
    suffices MapsTo (f - algebraMap K (End K V) μ') p p by
      simp only [Module.End.coe_pow, this.iterate l₀]
    intro x hx
    rw [LinearMap.sub_apply, algebraMap_end_apply]
    exact p.sub_mem (h _ hx) (smul_mem p μ' hx)
  have hg₂ : MapsTo g ↑(f.genEigenspace μ k) ↑(f.genEigenspace μ k) :=
    f.mapsTo_genEigenspace_of_comm hfg μ k
  have hg₃ : InjOn g ↑(f.genEigenspace μ k) := by
    apply LinearMap.injOn_of_disjoint_ker subset_rfl
    have := f.independent_genEigenspace k
    have aux (μ') (_hμ' : μ' ∈ m.support.erase μ) :
        (f.genEigenspace μ') ↑l₀ ≤ (f.genEigenspace μ') k := by
      apply (f.genEigenspace μ').mono
      obtain _ | k := k
      · exact le_top
      · exact Nat.cast_le.2 <| Finset.sup_le fun i _ ↦ Nat.cast_le.1 <| hlk i
    rw [LinearMap.ker_noncommProd_eq_of_supIndep_ker, ← Finset.sup_eq_iSup]
    · have := Finset.supIndep_iff_disjoint_erase.mp (this.supIndep' m.support) μ hμ
      apply this.mono_right
      apply Finset.sup_mono_fun
      intro μ' hμ'
      rw [Algebra.algebraMap_eq_smul_one, ← End.genEigenspace_nat]
      apply aux μ' hμ'
    · have := this.supIndep' (m.support.erase μ)
      apply this.antitone_fun
      intro μ' hμ'
      rw [Algebra.algebraMap_eq_smul_one, ← End.genEigenspace_nat]
      apply aux μ' hμ'
  have hg₄ : SurjOn g
      ↑(p ⊓ f.genEigenspace μ k) ↑(p ⊓ f.genEigenspace μ k) := by
    have : MapsTo g
        ↑(p ⊓ f.genEigenspace μ k) ↑(p ⊓ f.genEigenspace μ k) :=
      hg₁.inter_inter hg₂
    rw [← LinearMap.injOn_iff_surjOn this]
    exact hg₃.mono inter_subset_right
  specialize hm₂ μ
  obtain ⟨y, ⟨hy₀ : y ∈ p, hy₁ : y ∈ f.genEigenspace μ k⟩, hy₂ : g y = g (m μ)⟩ :=
    hg₄ ⟨(hg₀ ▸ hg₁ hm₀), hg₂ hm₂⟩
  rwa [← hg₃ hy₁ hm₂ hy₂]
/-
**Submodule.eq_iSup_inf_genEigenspace** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：eq_iSup_inf_genEigenspace [FiniteDimensional K V] (k : Nat∞) (h : forall x
 in p, f x in p) (h' : ⨆ μ, f.genEigenspace μ k = ⊤) : p = ⨆ μ, p ⊓ f.genEigensp
ace μ k
参数：k : Nat∞；h : forall x in p, f x in p；h' : ⨆ μ, f.genEigenspace μ k = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.inf_iSup_genEigenspace`：inf_iSup_genEigenspace [FiniteDimensio
nal K V] (h : forall x in p, f x in p) (k : Nat∞) : p ⊓ ⨆ μ, f.genEigenspace μ k
 = ⨆ μ, p ⊓ f.genEigen…
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a
-/
theorem eq_iSup_inf_genEigenspace [FiniteDimensional K V] (k : ℕ∞)
    (h : ∀ x ∈ p, f x ∈ p) (h' : ⨆ μ, f.genEigenspace μ k = ⊤) :
    p = ⨆ μ, p ⊓ f.genEigenspace μ k := by
  rw [← inf_iSup_genEigenspace h, h', inf_top_eq]

end Submodule

/-- In finite dimensions, if the generalized eigenspaces of a linear endomorphism span the whole
space then the same is true of its restriction to any invariant submodule. -/
/-
**Module.End.genEigenspace_restrict_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.End.genEigenspace_restrict_eq_top {p : Submodule K V} {f : Module.E
nd K V} [FiniteDimensional K V] {k : Nat∞} (h : forall x in p, f x in p) (h' : ⨆
 μ, f.genEigenspace μ k = ⊤) : ⨆ μ, Module.End.genEigenspace (LinearMap.restrict
 f h) μ k = ⊤
参数：h : forall x in p, f x in p；h' : ⨆ μ, f.genEigenspace μ k = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Submodule.eq_iSup_inf_genEigenspace`：eq_iSup_inf_genEigenspace [FiniteDi
mensional K V] (k : Nat∞) (h : forall x in p, f x in p) (h' : ⨆ μ, f.genEigenspa
ce μ k = ⊤) : p = ⨆ μ, p …
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.comap_map_eq_of_injective`：comap_map_eq_of_injective (p : Subm
odule R M) : (p.map f).comap f = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.comap_subtype_self`：comap_subtype_self : comap p.subtype p = ⊤
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.inf_genEigenspace`：∀ {R : Type v} {M : Type w} [inst : CommRin
g R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (f : Module.End R 
M) (p : Submodule…

--- 原说明 ---
In finite dimensions, if the generalized eigenspaces of a linear endomorphism sp
an the whole
space then the same is true of its restriction to any invariant submodule.
-/
theorem Module.End.genEigenspace_restrict_eq_top
    {p : Submodule K V} {f : Module.End K V} [FiniteDimensional K V] {k : ℕ∞}
    (h : ∀ x ∈ p, f x ∈ p) (h' : ⨆ μ, f.genEigenspace μ k = ⊤) :
    ⨆ μ, Module.End.genEigenspace (LinearMap.restrict f h) μ k = ⊤ := by
  have := congr_arg (Submodule.comap p.subtype) (Submodule.eq_iSup_inf_genEigenspace k h h')
  have h_inj : Function.Injective p.subtype := Subtype.coe_injective
  simp_rw [Submodule.inf_genEigenspace f p h, Submodule.comap_subtype_self,
    ← Submodule.map_iSup, Submodule.comap_map_eq_of_injective h_inj] at this
  exact this.symm
