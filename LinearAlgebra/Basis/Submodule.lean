/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Bases of submodules
-/

@[expose] public section

open Function Set Submodule Finsupp Module

assert_not_exists Ordinal

noncomputable section

universe u

variable {ι ι' R R₂ M M' : Type*}

namespace Module.Basis
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable (b : Basis ι R M)

/-- If the submodule `P` has a basis, `x ∈ P` iff it is a linear combination of basis vectors. -/
/-
**Module.Basis.mem_submodule_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：mem_submodule_iff {P : Submodule R M} (b : Basis ι R P) {x : M} : x in P ↔
 exists c : ι ->₀ R, x = Finsupp.sum c fun i x => x • (b i : M)
参数：b : Basis ι R P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Finsupp.range_linearCombination`：range_linearCombination : LinearMap.ran
ge (linearCombination R v) = span R (range v)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If the submodule `P` has a basis, `x ∈ P` iff it is a linear combination of basi
s vectors.
-/
theorem mem_submodule_iff {P : Submodule R M} (b : Basis ι R P) {x : M} :
    x ∈ P ↔ ∃ c : ι →₀ R, x = Finsupp.sum c fun i x => x • (b i : M) := by
  conv_lhs =>
    rw [← P.range_subtype, ← Submodule.map_top, ← b.span_eq, Submodule.map_span, ← Set.range_comp,
        ← Finsupp.range_linearCombination]
  simp [@eq_comm _ x, Function.comp, Finsupp.linearCombination_apply]

set_option backward.isDefEq.respectTransparency false in
/-- If the submodule `P` has a finite basis,
`x ∈ P` iff it is a linear combination of basis vectors. -/
/-
**Module.Basis.mem_submodule_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：mem_submodule_iff' [Fintype ι] {P : Submodule R M} (b : Basis ι R P) {x : 
M} : x in P ↔ exists c : ι -> R, x = ∑ i, c i • (b i : M)
参数：b : Basis ι R P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Module.Basis.mem_submodule_iff`：mem_submodule_iff {P : Submodule R M} (b
 : Basis ι R P) {x : M} : x in P ↔ exists c : ι ->₀ R, x = Finsupp.sum c fun i x
 => x • (b i : M)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.sum_fintype`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : Fintype α]   (f : α →₀ M) (g :
 α → M → …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If the submodule `P` has a finite basis,
`x ∈ P` iff it is a linear combination of basis vectors.
-/
theorem mem_submodule_iff' [Fintype ι] {P : Submodule R M} (b : Basis ι R P) {x : M} :
    x ∈ P ↔ ∃ c : ι → R, x = ∑ i, c i • (b i : M) :=
  b.mem_submodule_iff.trans <|
    Finsupp.equivFunOnFinite.exists_congr_left.trans <|
      exists_congr fun c => by simp [Finsupp.sum_fintype, Finsupp.equivFunOnFinite]

end Basis

open LinearMap

variable {v : ι → M}
variable [Ring R] [CommRing R₂] [AddCommGroup M]
variable [Module R M] [Module R₂ M]
variable {x y : M}
variable (b : Basis ι R M)

/-
**Module.Basis.eq_bot_of_rank_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [inst : Ring R] [inst_1 : A
ddCommGroup M] [inst_2 : _root_.Module R M]   [IsDomain R] (b : Module.Basis ι R
 M) (N : Submodule R M),   (∀ {m : ℕ} (v : Fin m → ↥N), LinearIndependent R (Sub
type.val ∘ v) → m = 0) → N = ⊥
参数：b : Module.Basis ι R M；N : Submodule R M；∀ {m : ℕ} (v : Fin m → ↥N), LinearIn
dependent R (Subtype.val ∘ v) → m = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.linearIndependent_iff`：Fintype.linearIndependent_iff [Fintype ι]
 : LinearIndependent R v ↔ forall g : ι -> R, ∑ i, g i • v i = 0 -> forall i, g 
i = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonFinOfNatNat`：Meta.FastSubsingleton (Fin 1)
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.Basis.smul_eq_zero`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5
} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] 
[IsDomain R] (b…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem Basis.eq_bot_of_rank_eq_zero [IsDomain R] (b : Basis ι R M) (N : Submodule R M)
    (rank_eq : ∀ {m : ℕ} (v : Fin m → N), LinearIndependent R ((↑) ∘ v : Fin m → M) → m = 0) :
    N = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  contrapose! rank_eq with x_ne
  refine ⟨1, fun _ => ⟨x, hx⟩, ?_, one_ne_zero⟩
  rw [Fintype.linearIndependent_iff]
  rintro g sum_eq i
  simp only [Fin.default_eq_zero, Finset.univ_unique,
    Finset.sum_singleton] at sum_eq
  convert! (b.smul_eq_zero.mp sum_eq).resolve_right x_ne

end Module

section Induction

variable [Ring R] [IsDomain R]
variable [AddCommGroup M] [Module R M] {b : ι → M}

/-- If `N` is a submodule with finite rank, do induction on adjoining a linear independent
element to a submodule. -/
/-
**Submodule.inductionOnRankAux** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：Submodule.inductionOnRankAux (b : Basis ι R M) (P : Submodule R M -> Sort*
) (ih : forall N : Submodule R M, (forall N' <= N, forall x in N, (forall (c : R
), forall y in N', c • x + y = (0 : M) -> c = 0) -> P N') -> P N) (n : Nat) (N :
 Submodule R M) (rank_le : forall {m : Nat} (v : Fin m -> N), LinearIndependent 
R ((↑) ∘ v : Fin m -> M) -> m <= n) : P N
参数：b : Basis ι R M；P : Submodule R M -> Sort*；ih : forall N : Submodule R M, (fo
rall N' <= N, forall x in N, (forall (c : R), forall y in N', c • x + y = (0 : M
) -> c = 0) -> P N') -> P N；n : Nat；N : Submodule R M；rank_le : forall {m : Nat}
 (v : Fin m -> N), LinearIndependent R ((↑) ∘ v : Fin m -> M) -> m <= n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `N` is a submodule with finite rank, do induction on adjoining a linear indep
endent
element to a submodule.
-/
def Submodule.inductionOnRankAux (b : Basis ι R M) (P : Submodule R M → Sort*)
    (ih : ∀ N : Submodule R M,
      (∀ N' ≤ N, ∀ x ∈ N, (∀ (c : R), ∀ y ∈ N', c • x + y = (0 : M) → c = 0) → P N') → P N)
    (n : ℕ) (N : Submodule R M)
    (rank_le : ∀ {m : ℕ} (v : Fin m → N), LinearIndependent R ((↑) ∘ v : Fin m → M) → m ≤ n) :
    P N := by
  haveI : DecidableEq M := Classical.decEq M
  have Pbot : P ⊥ := by
    apply ih
    intro N _ x x_mem x_ortho
    exfalso
    rw [mem_bot] at x_mem
    simpa [x_mem] using x_ortho 1 0 N.zero_mem
  induction n generalizing N with
  | zero =>
    suffices N = ⊥ by rwa [this]
    apply Basis.eq_bot_of_rank_eq_zero b _ fun m hv => Nat.le_zero.mp (rank_le _ hv)
  | succ n rank_ih =>
    apply ih
    intro N' N'_le x x_mem x_ortho
    apply rank_ih
    intro m v hli
    refine Nat.succ_le_succ_iff.mp (rank_le (Fin.cons ⟨x, x_mem⟩ fun i => ⟨v i, N'_le (v i).2⟩) ?_)
    convert! hli.finCons' x _ ?_
    · ext i
      refine Fin.cases ?_ ?_ i <;> simp
    · intro c y hy hc
      refine x_ortho c y (Submodule.span_le.mpr ?_ hy) hc
      rintro _ ⟨z, rfl⟩
      exact (v z).2

end Induction

namespace Module.Basis

/-- An element of a non-unital-non-associative algebra is in the center exactly when it commutes
with the basis elements. -/
/-
**Module.Basis.mem_center_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {A : Type u_7} [inst : Semiring R] [inst_1
 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A] [SMulCommClass R 
A A] [SMulCommClass R R A] [IsScalarTower R A A]   (b : Module.Basis ι R A) {z :
 A},   z ∈ Set.center A ↔     (∀ (i : ι), Commute (b i) z) ∧ ∀ (i j : ι), z * (b
 i * b j) = z * b i * b j ∧ b i * b j * z = b i * (b j * z)
参数：b : Module.Basis ι R A；∀ (i : ι), Commute (b i) z；i j : ι；b i * b j；b j * z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用定理 `IsMulCentral.comm`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulCentral
 z → ∀ (a : M), Commute z a
· 使用定理 `IsMulCentral.left_assoc`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMulC
entral z → ∀ (b c : M), z * (b * c) = z * b * c
· 使用定理 `IsMulCentral.right_assoc`：∀ {M : Type u_1} [inst : Mul M] {z : M}, IsMul
Central z → ∀ (a b : M), a * b * z = a * (b * z)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.center.eq_1`：∀ (M : Type u_1) [inst : Mul M], Set.center M = {z | Is
MulCentral z}
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.linearCombination_repr`：linearCombination_repr : Finsupp.li
nearCombination _ b (b.repr x) = x
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `Finsupp.sum.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst 
: Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (g : α → M → N),   f.sum g = ∑
 a ∈ f…
· 使用定理 `commute_iff_eq`：commute_iff_eq [Mul S] (a b : S) : Commute a b ↔ a * b =
 b * a
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…

--- 原说明 ---
An element of a non-unital-non-associative algebra is in the center exactly when
 it commutes
with the basis elements.
-/
lemma mem_center_iff {A}
    [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [SMulCommClass R A A] [SMulCommClass R R A] [IsScalarTower R A A]
    (b : Basis ι R A) {z : A} :
    z ∈ Set.center A ↔
      (∀ i, Commute (b i) z) ∧ ∀ i j,
        z * (b i * b j) = (z * b i) * b j
          ∧ (b i * b j) * z = b i * (b j * z) := by
  constructor
  · intro h
    constructor
    · intro i
      apply (h.1 (b i)).symm
    · intros
      exact ⟨h.2 _ _, h.3 _ _⟩
  · intro h
    rw [center, mem_ofPred_eq]
    constructor
    case comm =>
      intro y
      rw [← b.linearCombination_repr y, linearCombination_apply, sum, commute_iff_eq,
        Finset.sum_mul, Finset.mul_sum]
      simp_rw [mul_smul_comm, smul_mul_assoc, (h.1 _).eq]
    case left_assoc =>
      intro c d
      rw [← b.linearCombination_repr c, ← b.linearCombination_repr d, linearCombination_apply,
          linearCombination_apply, sum, sum, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum,
          Finset.mul_sum]
      simp_rw [smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, Finset.mul_sum,
        Finset.smul_sum, smul_mul_assoc, mul_smul_comm, (h.2 _ _).1,
        (@SMulCommClass.smul_comm R R A)]
      rw [Finset.sum_comm]
    case right_assoc =>
      intro c d
      rw [← b.linearCombination_repr c, ← b.linearCombination_repr d, linearCombination_apply,
          linearCombination_apply, sum, Finsupp.sum, Finset.sum_mul]
      simp_rw [smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, Finset.mul_sum,
               Finset.smul_sum, smul_mul_assoc, mul_smul_comm, Finset.sum_mul, smul_mul_assoc,
               (h.2 _ _).2]

section RestrictScalars

variable {S : Type*} [CommRing R] [IsDomain R] [Ring S] [Nontrivial S] [AddCommGroup M]
variable [Algebra R S] [Module S M] [Module R M]
variable [IsScalarTower R S M] [IsTorsionFree R S] (b : Basis ι S M)
variable (R)

open Submodule

/-- Let `b` be an `S`-basis of `M`. Let `R` be a CommRing such that `Algebra R S` has no zero smul
divisors, then the submodule of `M` spanned by `b` over `R` admits `b` as an `R`-basis. -/
/-
**Module.Basis.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：{ι : Type u_1} →   (R : Type u_3) →     {M : Type u_5} →       {S : Type u
_7} →         [inst : CommRing R] →           [IsDomain R] →             [inst_2
 : Ring S] →               [Nontrivial S] →                 [inst_4 : AddCommGro
up M] →                   [inst_5 : Algebra R S] →                     [inst_6 :
 _root_.Module S M] →                       [inst_7 : _root_.Module R M] →      
                   [IsScalarTower R S M] →                           [Module.IsT
orsionFree R S] →                             (b : Module.Basis ι S M) → Module.
Basis ι R ↥(Submodule.span R (Set.range ⇑b))
参数：R : Type u_3；b : Module.Basis ι S M；Submodule.span R (Set.range ⇑b)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `b` be an `S`-basis of `M`. Let `R` be a CommRing such that `Algebra R S` ha
s no zero smul
divisors, then the submodule of `M` spanned by `b` over `R` admits `b` as an `R`
-basis.
-/
noncomputable def restrictScalars : Basis ι R (span R (Set.range b)) :=
  Basis.span (b.linearIndependent.restrict_scalars (smul_left_injective R one_ne_zero))

@[simp]
/-
**Module.Basis.restrictScalars_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} (R : Type u_3) {M : Type u_5} {S : Type u_7} [inst : Comm
Ring R] [inst_1 : IsDomain R]   [inst_2 : Ring S] [inst_3 : Nontrivial S] [inst_
4 : AddCommGroup M] [inst_5 : Algebra R S]   [inst_6 : _root_.Module S M] [inst_
7 : _root_.Module R M] [inst_8 : IsScalarTower R S M]   [inst_9 : Module.IsTorsi
onFree R S] (b : Module.Basis ι S M) (i : ι), ↑((Module.Basis.restrictScalars R 
b) i) = b i
参数：R : Type u_3；b : Module.Basis ι S M；i : ι；(Module.Basis.restrictScalars R b) 
i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Module.Basis.span_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} 
[inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {v
 : ι → M} (hl…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restrictScalars_apply (i : ι) : (b.restrictScalars R i : M) = b i := by
  simp only [Basis.restrictScalars, Basis.span_apply]

@[simp]
/-
**Module.Basis.restrictScalars_repr_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basi
s`。
形式化陈述：∀ {ι : Type u_1} (R : Type u_3) {M : Type u_5} {S : Type u_7} [inst : Comm
Ring R] [inst_1 : IsDomain R]   [inst_2 : Ring S] [inst_3 : Nontrivial S] [inst_
4 : AddCommGroup M] [inst_5 : Algebra R S]   [inst_6 : _root_.Module S M] [inst_
7 : _root_.Module R M] [inst_8 : IsScalarTower R S M]   [inst_9 : Module.IsTorsi
onFree R S] (b : Module.Basis ι S M) (m : ↥(Submodule.span R (Set.range ⇑b))) (i
 : ι),   (algebraMap R S) (((Module.Basis.restrictScalars R b).repr m) i) = (b.r
epr ↑m) i
参数：R : Type u_3；b : Module.Basis ι S M；m : ↥(Submodule.span R (Set.range ⇑b))；i 
: ι；algebraMap R S；((Module.Basis.restrictScalars R b).repr m) i；b.repr ↑m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.CompatibleSMul.finsupp_cod`：∀ (R : Type u_9) (S : Type u_10) (
M : Type u_11) (N : Type u_12) (ι : Type u_13) [inst : Semiring S]   [inst_1 : A
ddCommMonoid M] [inst_2 : …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.mapRange.linearMap_apply`：∀ {α : Type u_1} {M : Type u_2} {N : T
ype u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R
₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
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
· 使用定理 `Module.Basis.restrictScalars_apply`：∀ {ι : Type u_1} (R : Type u_3) {M :
 Type u_5} {S : Type u_7} [inst : CommRing R] [inst_1 : IsDomain R]   [inst_2 : 
Ring S] [inst_3 : Nontri…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
theorem restrictScalars_repr_apply (m : span R (Set.range b)) (i : ι) :
    algebraMap R S ((b.restrictScalars R).repr m i) = b.repr m i := by
  suffices
    Finsupp.mapRange.linearMap (Algebra.linearMap R S) ∘ₗ (b.restrictScalars R).repr.toLinearMap =
      ((b.repr : M →ₗ[S] ι →₀ S).restrictScalars R).domRestrict _
    by exact DFunLike.congr_fun (LinearMap.congr_fun this m) i
  refine Basis.ext (b.restrictScalars R) fun _ => ?_
  simp only [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply, map_one,
    Basis.repr_self, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    Algebra.linearMap_apply, LinearMap.domRestrict_apply,
    Basis.restrictScalars_apply, LinearMap.coe_restrictScalars]

/-- Let `b` be an `S`-basis of `M`. Then `m : M` lies in the `R`-module spanned by `b` iff all the
coordinates of `m` on the basis `b` are in `R` (see `Basis.mem_span` for the case `R = S`). -/
/-
**Module.Basis.mem_span_iff_repr_mem** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：∀ {ι : Type u_1} (R : Type u_3) {M : Type u_5} {S : Type u_7} [inst : Comm
Ring R] [IsDomain R] [inst_2 : Ring S]   [Nontrivial S] [inst_4 : AddCommGroup M
] [inst_5 : Algebra R S] [inst_6 : _root_.Module S M]   [inst_7 : _root_.Module 
R M] [IsScalarTower R S M] [Module.IsTorsionFree R S] (b : Module.Basis ι S M) (
m : M),   m ∈ Submodule.span R (Set.range ⇑b) ↔ ∀ (i : ι), (b.repr m) i ∈ Set.ra
nge ⇑(algebraMap R S)
参数：R : Type u_3；b : Module.Basis ι S M；m : M；Set.range ⇑b；i : ι；b.repr m；algebra
Map R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.restrictScalars_repr_apply`：∀ {ι : Type u_1} (R : Type u_3)
 {M : Type u_5} {S : Type u_7} [inst : CommRing R] [inst_1 : IsDomain R]   [inst
_2 : Ring S] [inst_3 : Nontri…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.linearCombination_repr`：linearCombination_repr : Finsupp.li
nearCombination _ b (b.repr x) = x
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
Let `b` be an `S`-basis of `M`. Then `m : M` lies in the `R`-module spanned by `
b` iff all the
coordinates of `m` on the basis `b` are in `R` (see `Basis.mem_span` for the cas
e `R = S`).
-/
theorem mem_span_iff_repr_mem (m : M) :
    m ∈ span R (Set.range b) ↔ ∀ i, b.repr m i ∈ Set.range (algebraMap R S) := by
  refine
    ⟨fun hm i => ⟨(b.restrictScalars R).repr ⟨m, hm⟩ i, b.restrictScalars_repr_apply R ⟨m, hm⟩ i⟩,
      fun h => ?_⟩
  rw [← b.linearCombination_repr m, Finsupp.linearCombination_apply S _]
  refine sum_mem fun i _ => ?_
  obtain ⟨_, h⟩ := h i
  simp_rw [← h, algebraMap_smul]
  exact smul_mem _ _ (subset_span (Set.mem_range_self i))

end RestrictScalars

section AddSubgroup

variable {M R : Type*} [Ring R] [Nontrivial R] [IsAddTorsionFree R]
  [AddCommGroup M] [Module R M] (A : AddSubgroup M) {ι : Type*} (b : Basis ι R M)

/--
Let `A` be a subgroup of an additive commutative group `M` that is also an `R`-module.
Construct a basis of `A` as a `ℤ`-basis from an `R`-basis of `E` that generates `A`.
-/
/-
**Module.Basis.addSubgroupOfClosure** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：{M : Type u_7} →   {R : Type u_8} →     [inst : Ring R] →       [Nontrivia
l R] →         [IsAddTorsionFree R] →           [inst_3 : AddCommGroup M] →     
        [inst_4 : _root_.Module R M] →               (A : AddSubgroup M) →      
           {ι : Type u_9} →                   (b : Module.Basis ι R M) →        
             A = AddSubgroup.closure (Set.range ⇑b) → Module.Basis ι ℤ ↥(AddSubg
roup.toIntSubmodule A)
参数：A : AddSubgroup M；b : Module.Basis ι R M；Set.range ⇑b；AddSubgroup.toIntSubmod
ule A。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Int.instIsDomain`：IsDomain ℤ

--- 原说明 ---
Let `A` be a subgroup of an additive commutative group `M` that is also an `R`-m
odule.
Construct a basis of `A` as a `ℤ`-basis from an `R`-basis of `E` that generates 
`A`.
-/
noncomputable def addSubgroupOfClosure (h : A = .closure (Set.range b)) :
    Basis ι ℤ A.toIntSubmodule :=
  (b.restrictScalars ℤ).map <|
    LinearEquiv.ofEq _ _
      (by rw [h, ← Submodule.span_int_eq_addSubgroupClosure, toAddSubgroup_toIntSubmodule])

@[simp]
/-
**Module.Basis.addSubgroupOfClosure_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basi
s`。
形式化陈述：∀ {M : Type u_7} {R : Type u_8} [inst : Ring R] [inst_1 : Nontrivial R] [i
nst_2 : IsAddTorsionFree R]   [inst_3 : AddCommGroup M] [inst_4 : _root_.Module 
R M] (A : AddSubgroup M) {ι : Type u_9} (b : Module.Basis ι R M)   (h : A = AddS
ubgroup.closure (Set.range ⇑b)) (i : ι), ↑((Module.Basis.addSubgroupOfClosure A 
b h) i) = b i
参数：A : AddSubgroup M；b : Module.Basis ι R M；h : A = AddSubgroup.closure (Set.ran
ge ⇑b)；i : ι；(Module.Basis.addSubgroupOfClosure A b h) i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.restrictScalars_apply`：∀ {ι : Type u_1} (R : Type u_3) {M :
 Type u_5} {S : Type u_7} [inst : CommRing R] [inst_1 : IsDomain R]   [inst_2 : 
Ring S] [inst_3 : Nontri…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem addSubgroupOfClosure_apply (h : A = .closure (Set.range b)) (i : ι) :
    b.addSubgroupOfClosure A h i = b i := by
  simp [addSubgroupOfClosure]

@[simp]
/-
**Module.Basis.addSubgroupOfClosure_repr_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module
.Basis`。
形式化陈述：∀ {M : Type u_7} {R : Type u_8} [inst : Ring R] [inst_1 : Nontrivial R] [i
nst_2 : IsAddTorsionFree R]   [inst_3 : AddCommGroup M] [inst_4 : _root_.Module 
R M] (A : AddSubgroup M) {ι : Type u_9} (b : Module.Basis ι R M)   (h : A = AddS
ubgroup.closure (Set.range ⇑b)) (x : ↥A) (i : ι),   ↑(((Module.Basis.addSubgroup
OfClosure A b h).repr x) i) = (b.repr ↑x) i
参数：A : AddSubgroup M；b : Module.Basis ι R M；h : A = AddSubgroup.closure (Set.ran
ge ⇑b)；x : ↥A；i : ι；((Module.Basis.addSubgroupOfClosure A b h).repr x) i；b.repr 
↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.CompatibleSMul.finsupp_cod`：∀ (R : Type u_9) (S : Type u_10) (
M : Type u_11) (N : Type u_12) (ι : Type u_13) [inst : Semiring S]   [inst_1 : A
ddCommMonoid M] [inst_2 : …
· 使用定理 `LinearMap.CompatibleSMul.intModule`：∀ {M : Type u_8} {M₂ : Type u_10} [i
nst : AddCommGroup M] [inst_1 : AddCommGroup M₂] {S : Type u_14}   [inst_2 : Sem
iring S] [inst_3 : _root…
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.mapRange.linearMap_apply`：∀ {α : Type u_1} {M : Type u_2} {N : T
ype u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R
₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Module.Basis.addSubgroupOfClosure_apply`：∀ {M : Type u_7} {R : Type u_8}
 [inst : Ring R] [inst_1 : Nontrivial R] [inst_2 : IsAddTorsionFree R]   [inst_3
 : AddCommGroup M] [inst_4 : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
theorem addSubgroupOfClosure_repr_apply (h : A = .closure (Set.range b)) (x : A) (i : ι) :
    (b.addSubgroupOfClosure A h).repr x i = b.repr x i := by
  suffices Finsupp.mapRange.linearMap (Algebra.linearMap ℤ R) ∘ₗ
      (b.addSubgroupOfClosure A h).repr.toLinearMap =
        ((b.repr : M →ₗ[R] ι →₀ R).restrictScalars ℤ).domRestrict A.toIntSubmodule by
    exact DFunLike.congr_fun (LinearMap.congr_fun this x) i
  exact (b.addSubgroupOfClosure A h).ext fun _ ↦ by simp

end AddSubgroup

end Module.Basis

