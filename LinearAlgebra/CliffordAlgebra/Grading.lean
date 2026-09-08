/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Results about the grading structure of the clifford algebra

The main result is `CliffordAlgebra.gradedAlgebra`, which says that the clifford algebra is a
ℤ₂-graded algebra (or "superalgebra").
-/

@[expose] public section


namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {Q : QuadraticForm R M}

open scoped DirectSum

variable (Q)

/-- The even or odd submodule, defined as the supremum of the even or odd powers of
`(ι Q).range`. `evenOdd 0` is the even submodule, and `evenOdd 1` is the odd submodule. -/
/-
**CliffordAlgebra.evenOdd** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：evenOdd (i : ZMod 2) : Submodule R (CliffordAlgebra Q)
参数：i : ZMod 2。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The even or odd submodule, defined as the supremum of the even or odd powers of
`(ι Q).range`. `evenOdd 0` is the even submodule, and `evenOdd 1` is the odd sub
module.
-/
def evenOdd (i : ZMod 2) : Submodule R (CliffordAlgebra Q) :=
  ⨆ j : { n : ℕ // ↑n = i }, LinearMap.range (ι Q) ^ (j : ℕ)
/-
**CliffordAlgebra.one_le_evenOdd_zero** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra
`。
形式化陈述：one_le_evenOdd_zero : 1 <= evenOdd Q 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
theorem one_le_evenOdd_zero : 1 ≤ evenOdd Q 0 := by
  refine le_trans ?_ (le_iSup _ ⟨0, Nat.cast_zero⟩)
  exact (pow_zero _).ge
/-
**CliffordAlgebra.range_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_ι_le_evenOdd_one : LinearMap.range (ι Q) ≤ evenOdd Q 1 := by
  refine le_trans ?_ (le_iSup _ ⟨1, Nat.cast_one⟩)
  exact (pow_one _).ge
/-
**CliffordAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_mem_evenOdd_one (m : M) : ι Q m ∈ evenOdd Q 1 :=
  range_ι_le_evenOdd_one Q <| LinearMap.mem_range_self _ m
/-
**CliffordAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_mul_ι_mem_evenOdd_zero (m₁ m₂ : M) : ι Q m₁ * ι Q m₂ ∈ evenOdd Q 0 :=
  Submodule.mem_iSup_of_mem ⟨2, rfl⟩
    (by
      rw [Subtype.coe_mk, pow_two]
      exact
        Submodule.mul_mem_mul (LinearMap.mem_range_self (ι Q) m₁)
          (LinearMap.mem_range_self (ι Q) m₂))
/-
**CliffordAlgebra.evenOdd_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：evenOdd_mul_le (i j : ZMod 2) : evenOdd Q i * evenOdd Q j <= evenOdd Q (i 
+ j)
参数：i j : ZMod 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.iSup_eq_span`：iSup_eq_span {ι : Sort*} (p : ι -> Submodule R M
) : ⨆ i, p i = span R (⋃ i, ↑(p i))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.span_mul_span`：span_mul_span : span R S * span R T = span R (S
 * T)
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Set.iUnion_mul`：iUnion_mul (s : ι -> Set α) (t : Set α) : (⋃ i, s i) * t
 = ⋃ i, s i * t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.mul_iUnion`：mul_iUnion (s : Set α) (t : ι -> Set α) : (s * ⋃ i, t i)
 = ⋃ i, s * t i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Submodule.mul_mem_mul`：mul_mem_mul (hm : m in M) (hn : n in N) : m * n i
n M * N
-/
theorem evenOdd_mul_le (i j : ZMod 2) : evenOdd Q i * evenOdd Q j ≤ evenOdd Q (i + j) := by
  simp_rw [evenOdd, Submodule.iSup_eq_span, Submodule.span_mul_span]
  apply Submodule.span_mono
  simp_rw [Set.iUnion_mul, Set.mul_iUnion, Set.iUnion_subset_iff, Set.mul_subset_iff]
  rintro ⟨xi, rfl⟩ ⟨yi, rfl⟩ x hx y hy
  refine Set.mem_iUnion.mpr ⟨⟨xi + yi, Nat.cast_add _ _⟩, ?_⟩
  simp only [pow_add]
  exact Submodule.mul_mem_mul hx hy
/-
**CliffordAlgebra.evenOdd.gradedMonoid** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebr
a.evenOdd`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   (Q : QuadraticForm R M), SetLike.GradedMonoid
 (CliffordAlgebra.evenOdd Q)
参数：Q : QuadraticForm R M；CliffordAlgebra.evenOdd Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.one_le`：one_le {P : Submodule R A} : (1 : Submodule R A) <= P 
↔ (1 : A) in P
· 使用定理 `CliffordAlgebra.one_le_evenOdd_zero`：one_le_evenOdd_zero : 1 <= evenOdd 
Q 0
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.mul_le`：mul_le : M * N <= P ↔ forall m in M, forall n in N, m 
* n in P
· 使用定理 `CliffordAlgebra.evenOdd_mul_le`：evenOdd_mul_le (i j : ZMod 2) : evenOdd 
Q i * evenOdd Q j <= evenOdd Q (i + j)
-/
instance evenOdd.gradedMonoid : SetLike.GradedMonoid (evenOdd Q) where
  one_mem := Submodule.one_le.mp (one_le_evenOdd_zero Q)
  mul_mem _i _j _p _q hp hq := Submodule.mul_le.mp (evenOdd_mul_le Q _ _) _ hp _ hq

/-- A version of `CliffordAlgebra.ι` that maps directly into the graded structure. This is
primarily an auxiliary construction used to provide `CliffordAlgebra.gradedAlgebra`. -/
/-
**CliffordAlgebra.GradedAlgebra.** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `CliffordAlgebra.ι` that maps directly into the graded structure. T
his is
primarily an auxiliary construction used to provide `CliffordAlgebra.gradedAlgeb
ra`.
-/
protected def GradedAlgebra.ι : M →ₗ[R] ⨁ i : ZMod 2, evenOdd Q i :=
  DirectSum.lof R (ZMod 2) (fun i => ↥(evenOdd Q i)) 1 ∘ₗ (ι Q).codRestrict _ (ι_mem_evenOdd_one Q)
/-
**CliffordAlgebra.GradedAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem GradedAlgebra.ι_apply (m : M) :
    GradedAlgebra.ι Q m = DirectSum.of (fun i => ↥(evenOdd Q i)) 1 ⟨ι Q m, ι_mem_evenOdd_one Q m⟩ :=
  rfl

nonrec theorem GradedAlgebra.ι_sq_scalar (m : M) :
    GradedAlgebra.ι Q m * GradedAlgebra.ι Q m = algebraMap R _ (Q m) := by
  rw [GradedAlgebra.ι_apply Q, DirectSum.of_mul_of, DirectSum.algebraMap_apply]
  exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext rfl <| ι_sq_scalar _ _)
/-
**CliffordAlgebra.GradedAlgebra.lift_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem GradedAlgebra.lift_ι_eq (i' : ZMod 2) (x' : evenOdd Q i') :
    lift Q ⟨GradedAlgebra.ι Q, GradedAlgebra.ι_sq_scalar Q⟩ x' =
      DirectSum.of (fun i => evenOdd Q i) i' x' := by
  obtain ⟨x', hx'⟩ := x'
  dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
  induction hx' using Submodule.iSup_induction' with
  | mem i x hx =>
    obtain ⟨i, rfl⟩ := i
    dsimp only [Subtype.coe_mk] at hx
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
    | add x y i hx hy ihx ihy =>
      rw [map_add, ihx, ihy, ← map_add]
      rfl
    | mem_mul m hm i x hx ih =>
      obtain ⟨_, rfl⟩ := hm
      rw [map_mul, ih, lift_ι_apply, GradedAlgebra.ι_apply Q, DirectSum.of_mul_of]
      refine DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext ?_ ?_) <;>
        dsimp only [GradedMonoid.mk, Subtype.coe_mk]
      · rw [Nat.succ_eq_add_one, add_comm, Nat.cast_add, Nat.cast_one]
      rfl
  | zero =>
    rw [map_zero]
    apply Eq.symm
    apply DFinsupp.single_eq_zero.mpr; rfl
  | add x y hx hy ihx ihy =>
    rw [map_add, ihx, ihy, ← map_add]; rfl

/-- The clifford algebra is graded by the even and odd parts. -/
/-
**CliffordAlgebra.gradedAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `CliffordAlgebra`。
形式化陈述：gradedAlgebra : GradedAlgebra (evenOdd Q)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.evenOdd.gradedMonoid`：∀ {R : Type u_1} {M : Type u_2} [i
nst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (Q : 
QuadraticForm R M), SetLik…

--- 原说明 ---
The clifford algebra is graded by the even and odd parts.
-/
instance gradedAlgebra : GradedAlgebra (evenOdd Q) :=
  GradedAlgebra.ofAlgHom (evenOdd Q)
    -- while not necessary, the `by apply` makes this elaborate faster
    (lift Q ⟨by apply GradedAlgebra.ι Q, by apply GradedAlgebra.ι_sq_scalar Q⟩)
    -- the proof from here onward is mostly similar to the `TensorAlgebra` case, with some extra
    -- handling for the `iSup` in `evenOdd`.
    (by
      ext m
      dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        AlgHom.id_apply]
      rw [lift_ι_apply, GradedAlgebra.ι_apply Q, DirectSum.coeAlgHom_of, Subtype.coe_mk])
    (by apply GradedAlgebra.lift_ι_eq Q)
/-
**CliffordAlgebra.iSup_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iSup_ι_range_eq_top : ⨆ i : ℕ, LinearMap.range (ι Q) ^ i = ⊤ := by
  rw [← (DirectSum.Decomposition.isInternal (evenOdd Q)).submodule_iSup_eq_top, eq_comm]
  calc
    -- Porting note: needs extra annotations, no longer unifies against the goal in the face of
    -- ambiguity
    ⨆ (i : ZMod 2) (j : { n : ℕ // ↑n = i }), LinearMap.range (ι Q) ^ (j : ℕ) =
        ⨆ i : Σ i : ZMod 2, { n : ℕ // ↑n = i }, LinearMap.range (ι Q) ^ (i.2 : ℕ) := by
      rw [iSup_sigma]
    _ = ⨆ i : ℕ, LinearMap.range (ι Q) ^ i :=
      Function.Surjective.iSup_congr (fun i => i.2) (fun i => ⟨⟨_, i, rfl⟩, rfl⟩) fun _ => rfl
/-
**CliffordAlgebra.evenOdd_isCompl** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：evenOdd_isCompl : IsCompl (evenOdd Q 0) (evenOdd Q 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.IsInternal.isCompl`：∀ {R : Type u} [inst : Semiring R] {ι : Ty
pe v} [dec_ι : DecidableEq ι] {M : Type u_1} [inst_1 : AddCommMonoid M]   [inst_
2 : _root_.Module …
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `DirectSum.Decomposition.isInternal`：∀ {ι : Type u_1} {M : Type u_3} {σ :
 Type u_4} [inst : DecidableEq ι] [inst_1 : AddCommMonoid M] [inst_2 : SetLike σ
 M]   [inst_3 : AddSubmo…
-/
theorem evenOdd_isCompl : IsCompl (evenOdd Q 0) (evenOdd Q 1) :=
  (DirectSum.Decomposition.isInternal (evenOdd Q)).isCompl zero_ne_one <| by
    have : (Finset.univ : Finset (ZMod 2)) = {0, 1} := rfl
    simpa using congr_arg ((↑) : Finset (ZMod 2) → Set (ZMod 2)) this

/-- To show a property is true on the even or odd part, it suffices to show it is true on the
scalars or vectors (respectively), closed under addition, and under left-multiplication by a pair
of vectors. -/
@[elab_as_elim]
/-
**CliffordAlgebra.evenOdd_induction** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：evenOdd_induction (n : ZMod 2) {motive : forall x, x in evenOdd Q n -> Pro
p} (range_ι_pow : forall (v) (h : v in LinearMap.range (ι Q) ^ n.val), motive v 
(Submodule.mem_iSup_of_mem ⟨n.val, n.natCast_zmod_val⟩ h)) (add : forall x y hx 
hy, motive x hx -> motive y hy -> motive (x + y) (Submodule.add_mem _ hx hy)) (ι
_mul_ι_mul : forall m₁ m₂ x hx, motive x hx -> motive (ι Q m₁ * ι Q m₂ * x) (zer
o_add n ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero Q m₁ m₂) hx)) (x : Cl
iffordAlgebra Q) (hx : x i
参数：n : ZMod 2；range_ι_pow : forall (v) (h : v in LinearMap.range (ι Q) ^ n.val),
 motive v (Submodule.mem_iSup_of_mem ⟨n.val, n.natCast_zmod_val⟩ h)；add : forall
 x y hx hy, motive x hx -> motive y hy -> motive (x + y) (Submodule.add_mem _ hx
 hy)；ι_mul_ι_mul : forall m₁ m₂ x hx, motive x hx -> motive (ι Q m₁ * ι Q m₂ * x
) (zero_add n ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero Q m₁ m₂) hx)；x 
: CliffordAlgebra Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.mem_iSup_of_mem`：mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι ->
 Submodule R M} (i : ι) (h : b in p i) : b in ⨆ i, p i
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `SetLike.mul_mem_graded`：SetLike.mul_mem_graded {S : Type*} [SetLike S R]
 [Mul R] [Add ι] {A : ι -> S} [SetLike.GradedMul A] ⦃i j⦄ {gi gj} (hi : gi in A 
i) (hj : gj …
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `CliffordAlgebra.evenOdd.gradedMonoid`：∀ {R : Type u_1} {M : Type u_2} [i
nst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (Q : 
QuadraticForm R M), SetLik…
· 使用定理 `CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero`：ι_mul_ι_mem_evenOdd_zero (m₁ m
₂ : M) : ι Q m₁ * ι Q m₂ in evenOdd Q 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Submodule.iSup_induction'`：iSup_induction' {ι : Sort*} (p : ι -> Submodu
le R M) {motive : forall x, (x in ⨆ i, p i) -> Prop} (mem : forall (i) (x) (hx :
 x in p i), mot…
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Submodule.mul_induction_on'`：∀ {R : Type u} [inst : Semiring R] {A : Typ
e v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTowe
r R A A] {M N : S…
· 使用定理 `Submodule.pow_induction_on_left'`：∀ {R : Type u} [inst : CommSemiring R]
 {A : Type v} [inst_1 : Semiring A] [inst_2 : Algebra R A] (M : Submodule R A)  
 {C : (n : ℕ) → (x : A…
· 使用定理 `Submodule.mul_mem_mul`：mul_mem_mul (hm : m in M) (hn : n in N) : m * n i
n M * N
· 使用定理 `Submodule.algebraMap_mem`：algebraMap_mem (r : R) : algebraMap R A r in (
1 : Submodule R A)
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
To show a property is true on the even or odd part, it suffices to show it is tr
ue on the
scalars or vectors (respectively), closed under addition, and under left-multipl
ication by a pair
of vectors.
-/
theorem evenOdd_induction (n : ZMod 2) {motive : ∀ x, x ∈ evenOdd Q n → Prop}
    (range_ι_pow : ∀ (v) (h : v ∈ LinearMap.range (ι Q) ^ n.val),
        motive v (Submodule.mem_iSup_of_mem ⟨n.val, n.natCast_zmod_val⟩ h))
    (add : ∀ x y hx hy, motive x hx → motive y hy → motive (x + y) (Submodule.add_mem _ hx hy))
    (ι_mul_ι_mul :
      ∀ m₁ m₂ x hx,
        motive x hx →
          motive (ι Q m₁ * ι Q m₂ * x)
            (zero_add n ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero Q m₁ m₂) hx))
    (x : CliffordAlgebra Q) (hx : x ∈ evenOdd Q n) : motive x hx := by
  apply Submodule.iSup_induction' (motive := motive) _ _ (range_ι_pow 0 (Submodule.zero_mem _)) add
  refine Subtype.rec ?_
  simp_rw [ZMod.natCast_eq_iff, add_comm n.val]
  rintro n' ⟨k, rfl⟩ xv
  simp_rw [pow_add, pow_mul]
  intro hxv
  induction hxv using Submodule.mul_induction_on' with
  | mem_mul_mem a ha b hb =>
    induction ha using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      simp_rw [← Algebra.smul_def]
      exact range_ι_pow _ (Submodule.smul_mem _ _ hb)
    | add x y n hx hy ihx ihy =>
      simp_rw [add_mul]
      apply add _ _ _ _ ihx ihy
    | mem_mul x hx n'' y hy ihy =>
      revert hx
      simp_rw [pow_two]
      intro hx2
      induction hx2 using Submodule.mul_induction_on' with
      | mem_mul_mem m hm n hn =>
        simp_rw [LinearMap.mem_range] at hm hn
        obtain ⟨m₁, rfl⟩ := hm; obtain ⟨m₂, rfl⟩ := hn
        simp_rw [mul_assoc _ y b]
        exact ι_mul_ι_mul _ _ _ _ ihy
      | add x hx y hy ihx ihy =>
        simp_rw [add_mul]
        apply add _ _ _ _ ihx ihy
  | add x y hx hy ihx ihy =>
    apply add _ _ _ _ ihx ihy

/-- To show a property is true on the even parts, it suffices to show it is true on the
scalars, closed under addition, and under left-multiplication by a pair of vectors. -/
@[elab_as_elim]
/-
**CliffordAlgebra.even_induction** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：even_induction {motive : forall x, x in evenOdd Q 0 -> Prop} (algebraMap :
 forall r : R, motive (algebraMap _ _ r) (SetLike.algebraMap_mem_graded _ _)) (a
dd : forall x y hx hy, motive x hx -> motive y hy -> motive (x + y) (Submodule.a
dd_mem _ hx hy)) (ι_mul_ι_mul : forall m₁ m₂ x hx, motive x hx -> motive (ι Q m₁
 * ι Q m₂ * x) (zero_add (0 : ZMod 2) ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_even
Odd_zero Q m₁ m₂) hx)) (x : CliffordAlgebra Q) (hx : x in evenOdd Q 0) : motive 
x hx
参数：algebraMap : forall r : R, motive (algebraMap _ _ r) (SetLike.algebraMap_mem_
graded _ _)；add : forall x y hx hy, motive x hx -> motive y hy -> motive (x + y)
 (Submodule.add_mem _ hx hy)；ι_mul_ι_mul : forall m₁ m₂ x hx, motive x hx -> mot
ive (ι Q m₁ * ι Q m₂ * x) (zero_add (0 : ZMod 2) ▸ SetLike.mul_mem_graded (ι_mul
_ι_mem_evenOdd_zero Q m₁ m₂) hx)；x : CliffordAlgebra Q；hx : x in evenOdd Q 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.algebraMap_mem_graded`：SetLike.algebraMap_mem_graded [Zero ι] [C
ommSemiring S] [Semiring R] [Algebra S R] (A : ι -> Submodule S R) [SetLike.Grad
edOne A] (s : S) : …
· 使用定理 `SetLike.GradedMonoid.toGradedOne`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `CliffordAlgebra.evenOdd.gradedMonoid`：∀ {R : Type u_1} {M : Type u_2} [i
nst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (Q : 
QuadraticForm R M), SetLik…
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `SetLike.mul_mem_graded`：SetLike.mul_mem_graded {S : Type*} [SetLike S R]
 [Mul R] [Add ι] {A : ι -> S} [SetLike.GradedMul A] ⦃i j⦄ {gi gj} (hi : gi in A 
i) (hj : gj …
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero`：ι_mul_ι_mem_evenOdd_zero (m₁ m
₂ : M) : ι Q m₁ * ι Q m₂ in evenOdd Q 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CliffordAlgebra.evenOdd_induction`：evenOdd_induction (n : ZMod 2) {motiv
e : forall x, x in evenOdd Q n -> Prop} (range_ι_pow : forall (v) (h : v in Line
arMap.range (ι Q) ^ n.v…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.mem_iSup_of_mem`：mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι ->
 Submodule R M} (i : ι) (h : b in p i) : b in ⨆ i, p i
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_one`：mem_one {x : A} : x in (1 : Submodule R A) ↔ exists y
, algebraMap R A y = x

--- 原说明 ---
To show a property is true on the even parts, it suffices to show it is true on 
the
scalars, closed under addition, and under left-multiplication by a pair of vecto
rs.
-/
theorem even_induction {motive : ∀ x, x ∈ evenOdd Q 0 → Prop}
    (algebraMap : ∀ r : R, motive (algebraMap _ _ r) (SetLike.algebraMap_mem_graded _ _))
    (add : ∀ x y hx hy, motive x hx → motive y hy → motive (x + y) (Submodule.add_mem _ hx hy))
    (ι_mul_ι_mul :
      ∀ m₁ m₂ x hx,
        motive x hx →
          motive (ι Q m₁ * ι Q m₂ * x)
            (zero_add (0 : ZMod 2) ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero Q m₁ m₂) hx))
    (x : CliffordAlgebra Q) (hx : x ∈ evenOdd Q 0) : motive x hx := by
  refine evenOdd_induction _ _ (motive := motive) (fun rx h => ?_) add ι_mul_ι_mul x hx
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp h
  exact algebraMap r

/-- To show a property is true on the odd parts, it suffices to show it is true on the
vectors, closed under addition, and under left-multiplication by a pair of vectors. -/
@[elab_as_elim]
/-
**CliffordAlgebra.odd_induction** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：odd_induction {P : forall x, x in evenOdd Q 1 -> Prop} (ι : forall v, P (ι
 Q v) (ι_mem_evenOdd_one _ _)) (add : forall x y hx hy, P x hx -> P y hy -> P (x
 + y) (Submodule.add_mem _ hx hy)) (ι_mul_ι_mul : forall m₁ m₂ x hx, P x hx -> P
 (CliffordAlgebra.ι Q m₁ * CliffordAlgebra.ι Q m₂ * x) (zero_add (1 : ZMod 2) ▸ 
SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero Q m₁ m₂) hx)) (x : CliffordAlge
bra Q) (hx : x in evenOdd Q 1) : P x hx
参数：ι : forall v, P (ι Q v) (ι_mem_evenOdd_one _ _)；add : forall x y hx hy, P x h
x -> P y hy -> P (x + y) (Submodule.add_mem _ hx hy)；ι_mul_ι_mul : forall m₁ m₂ 
x hx, P x hx -> P (CliffordAlgebra.ι Q m₁ * CliffordAlgebra.ι Q m₂ * x) (zero_ad
d (1 : ZMod 2) ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero Q m₁ m₂) hx)；x
 : CliffordAlgebra Q；hx : x in evenOdd Q 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.ι_mem_evenOdd_one`：ι_mem_evenOdd_one (m : M) : ι Q m in 
evenOdd Q 1
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `SetLike.mul_mem_graded`：SetLike.mul_mem_graded {S : Type*} [SetLike S R]
 [Mul R] [Add ι] {A : ι -> S} [SetLike.GradedMul A] ⦃i j⦄ {gi gj} (hi : gi in A 
i) (hj : gj …
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `CliffordAlgebra.evenOdd.gradedMonoid`：∀ {R : Type u_1} {M : Type u_2} [i
nst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (Q : 
QuadraticForm R M), SetLik…
· 使用定理 `CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero`：ι_mul_ι_mem_evenOdd_zero (m₁ m
₂ : M) : ι Q m₁ * ι Q m₂ in evenOdd Q 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CliffordAlgebra.evenOdd_induction`：evenOdd_induction (n : ZMod 2) {motiv
e : forall x, x in evenOdd Q n -> Prop} (range_ι_pow : forall (v) (h : v in Line
arMap.range (ι Q) ^ n.v…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.mem_iSup_of_mem`：mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι ->
 Submodule R M} (i : ι) (h : b in p i) : b in ⨆ i, p i
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.val_one`：val_one (n : Nat) [Fact (1 < n)] : (1 : ZMod n).val = 1
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a

--- 原说明 ---
To show a property is true on the odd parts, it suffices to show it is true on t
he
vectors, closed under addition, and under left-multiplication by a pair of vecto
rs.
-/
theorem odd_induction {P : ∀ x, x ∈ evenOdd Q 1 → Prop}
    (ι : ∀ v, P (ι Q v) (ι_mem_evenOdd_one _ _))
    (add : ∀ x y hx hy, P x hx → P y hy → P (x + y) (Submodule.add_mem _ hx hy))
    (ι_mul_ι_mul :
      ∀ m₁ m₂ x hx,
        P x hx →
          P (CliffordAlgebra.ι Q m₁ * CliffordAlgebra.ι Q m₂ * x)
            (zero_add (1 : ZMod 2) ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero Q m₁ m₂) hx))
    (x : CliffordAlgebra Q) (hx : x ∈ evenOdd Q 1) : P x hx := by
  refine evenOdd_induction _ _ (motive := P) (fun ιv => ?_) add ι_mul_ι_mul x hx
  simp_rw [ZMod.val_one, pow_one]
  rintro ⟨v, rfl⟩
  exact ι v

end CliffordAlgebra

