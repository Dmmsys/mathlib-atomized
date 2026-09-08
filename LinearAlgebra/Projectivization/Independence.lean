/-
Copyright (c) 2022 Michael Blyth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Blyth
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Independence in Projective Space

In this file we define independence and dependence of families of elements in projective space.

## Implementation Details

We use an inductive definition to define the independence of points in projective
space, where the only constructor assumes an independent family of vectors from the
ambient vector space. Similarly for the definition of dependence.

## Results

- A family of elements is dependent if and only if it is not independent.
- Two elements are dependent if and only if they are equal.

## Future Work

- Prove the axioms of a projective geometry are satisfied by the dependence relation.
- Define projective linear subspaces.
-/

public section

open scoped LinearAlgebra.Projectivization

variable {ι K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {f : ι → ℙ K V}

namespace Projectivization

/-- A linearly independent family of nonzero vectors gives an independent family of points
in projective space. -/
/-
**Projectivization.Independent** 是 Mathlib 中的一个归纳类型，位于命名空间 `Projectivization`。
形式化陈述：{ι : Type u_1} →   {K : Type u_2} →     {V : Type u_3} →       [inst : Div
isionRing K] →         [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module K V] 
→ (ι → Projectivization K V) → Prop
参数：ι → Projectivization K V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linearly independent family of nonzero vectors gives an independent family of 
points
in projective space.
-/
inductive Independent : (ι → ℙ K V) → Prop
  | mk (f : ι → V) (hf : ∀ i : ι, f i ≠ 0) (hl : LinearIndependent K f) :
    Independent fun i => mk K (f i) (hf i)

/-- A family of points in a projective space is independent if and only if the representative
vectors determined by the family are linearly independent. -/
/-
**Projectivization.independent_iff** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization`。
形式化陈述：independent_iff : Independent f ↔ LinearIndependent K (Projectivization.re
p ∘ f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearIndependent.units_smul`：LinearIndependent.units_smul {v : ι -> M} 
(hv : LinearIndependent R v) (w : ι -> Rˣ) : LinearIndependent R (w • v)
· 使用定理 `Projectivization.exists_smul_eq_mk_rep`：exists_smul_eq_mk_rep (v : V) (h
v : v != 0) : exists a : Kˣ, a • v = (mk K v hv).rep
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Projectivization.rep_nonzero`：rep_nonzero (v : ℙ K V) : v.rep != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Projectivization.mk_rep`：mk_rep (v : ℙ K V) : mk K v.rep v.rep_nonzero =
 v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A family of points in a projective space is independent if and only if the repre
sentative
vectors determined by the family are linearly independent.
-/
theorem independent_iff : Independent f ↔ LinearIndependent K (Projectivization.rep ∘ f) := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨ff, hff, hh⟩
    choose a ha using fun i : ι => exists_smul_eq_mk_rep K (ff i) (hff i)
    convert! hh.units_smul a
    ext i
    exact (ha i).symm
  · convert! Independent.mk _ _ h
    · simp only [mk_rep, Function.comp_apply]
    · intro i
      apply rep_nonzero

/-- A family of points in projective space is independent if and only if the family of
submodules which the points determine is independent in the lattice-theoretic sense. -/
/-
**Projectivization.independent_iff_iSupIndep** 是 Mathlib 中的一个定理，位于命名空间 `Projecti
vization`。
形式化陈述：independent_iff_iSupIndep : Independent f ↔ iSupIndep fun i => (f i).submo
dule
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iSupIndep_iff_linearIndependent_of_ne_zero`：iSupIndep_iff_linearIndepend
ent_of_ne_zero [IsDomain R] [IsTorsionFree R N] {ι : Type*} {v : ι -> N} (h_ne_z
ero : forall i, v i != 0) : iSup…
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Projectivization.independent_iff`：independent_iff : Independent f ↔ Line
arIndependent K (Projectivization.rep ∘ f)
· 使用定理 `iSupIndep.linearIndependent`：iSupIndep.linearIndependent [IsDomain R] [I
sTorsionFree R N] {ι : Type*} (p : ι -> Submodule R N) (hp : iSupIndep p) {v : ι
 -> N} (hv : fora…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Projectivization.submodule_eq`：submodule_eq (v : ℙ K V) : v.submodule = 
K ∙ v.rep
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `Projectivization.rep_nonzero`：rep_nonzero (v : ℙ K V) : v.rep != 0

--- 原说明 ---
A family of points in projective space is independent if and only if the family 
of
submodules which the points determine is independent in the lattice-theoretic se
nse.
-/
theorem independent_iff_iSupIndep : Independent f ↔ iSupIndep fun i => (f i).submodule := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨f, hf, hi⟩
    simp only [submodule_mk]
    exact (iSupIndep_iff_linearIndependent_of_ne_zero (R := K) hf).mpr hi
  · rw [independent_iff]
    refine h.linearIndependent (Projectivization.submodule ∘ f) (fun i => ?_) fun i => ?_
    · simpa only [Function.comp_apply, submodule_eq] using Submodule.mem_span_singleton_self _
    · exact rep_nonzero (f i)

/-- A linearly dependent family of nonzero vectors gives a dependent family of points
in projective space. -/
/-
**Projectivization.Dependent** 是 Mathlib 中的一个归纳类型，位于命名空间 `Projectivization`。
形式化陈述：{ι : Type u_1} →   {K : Type u_2} →     {V : Type u_3} →       [inst : Div
isionRing K] →         [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module K V] 
→ (ι → Projectivization K V) → Prop
参数：ι → Projectivization K V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linearly dependent family of nonzero vectors gives a dependent family of point
s
in projective space.
-/
inductive Dependent : (ι → ℙ K V) → Prop
  | mk (f : ι → V) (hf : ∀ i : ι, f i ≠ 0) (h : ¬LinearIndependent K f) :
    Dependent fun i => mk K (f i) (hf i)

/-- A family of points in a projective space is dependent if and only if their
representatives are linearly dependent. -/
/-
**Projectivization.dependent_iff** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization`。
形式化陈述：dependent_iff : Dependent f ↔ ¬LinearIndependent K (Projectivization.rep ∘
 f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearIndependent.units_smul`：LinearIndependent.units_smul {v : ι -> M} 
(hv : LinearIndependent R v) (w : ι -> Rˣ) : LinearIndependent R (w • v)
· 使用定理 `Projectivization.exists_smul_eq_mk_rep`：exists_smul_eq_mk_rep (v : V) (h
v : v != 0) : exists a : Kˣ, a • v = (mk K v hv).rep
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Projectivization.rep_nonzero`：rep_nonzero (v : ℙ K V) : v.rep != 0
· 使用定理 `Projectivization.mk_rep`：mk_rep (v : ℙ K V) : mk K v.rep v.rep_nonzero =
 v

--- 原说明 ---
A family of points in a projective space is dependent if and only if their
representatives are linearly dependent.
-/
theorem dependent_iff : Dependent f ↔ ¬LinearIndependent K (Projectivization.rep ∘ f) := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨ff, hff, hh1⟩
    contrapose hh1
    choose a ha using fun i : ι => exists_smul_eq_mk_rep K (ff i) (hff i)
    convert! hh1.units_smul a⁻¹
    ext i
    simp only [← ha, inv_smul_smul, Pi.smul_apply', Pi.inv_apply, Function.comp_apply]
  · convert! Dependent.mk _ _ h
    · simp only [mk_rep, Function.comp_apply]
    · exact fun i => rep_nonzero (f i)

/-- Dependence is the negation of independence. -/
/-
**Projectivization.dependent_iff_not_independent** 是 Mathlib 中的一个定理，位于命名空间 `Proj
ectivization`。
形式化陈述：dependent_iff_not_independent : Dependent f ↔ ¬Independent f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Projectivization.dependent_iff`：dependent_iff : Dependent f ↔ ¬LinearInd
ependent K (Projectivization.rep ∘ f)
· 使用定理 `Projectivization.independent_iff`：independent_iff : Independent f ↔ Line
arIndependent K (Projectivization.rep ∘ f)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Dependence is the negation of independence.
-/
theorem dependent_iff_not_independent : Dependent f ↔ ¬Independent f := by
  rw [dependent_iff, independent_iff]

/-- Independence is the negation of dependence. -/
/-
**Projectivization.independent_iff_not_dependent** 是 Mathlib 中的一个定理，位于命名空间 `Proj
ectivization`。
形式化陈述：independent_iff_not_dependent : Independent f ↔ ¬Dependent f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Projectivization.dependent_iff_not_independent`：dependent_iff_not_indepe
ndent : Dependent f ↔ ¬Independent f
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Independence is the negation of dependence.
-/
theorem independent_iff_not_dependent : Independent f ↔ ¬Dependent f := by
  rw [dependent_iff_not_independent, Classical.not_not]

/-- Two points in a projective space are dependent if and only if they are equal. -/
@[simp]
/-
**Projectivization.dependent_pair_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Projectiviza
tion`。
形式化陈述：dependent_pair_iff_eq (u v : ℙ K V) : Dependent ![u, v] ↔ u = v
参数：u v : ℙ K V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Projectivization.dependent_iff_not_independent`：dependent_iff_not_indepe
ndent : Dependent f ↔ ¬Independent f
· 使用定理 `Projectivization.independent_iff`：independent_iff : Independent f ↔ Line
arIndependent K (Projectivization.rep ∘ f)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `linearIndependent_fin2`：linearIndependent_fin2 {f : Fin 2 -> V} : Linear
Independent K f ↔ f 1 != 0 ∧ forall a : K, a • f 1 != f 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Projectivization.rep_nonzero`：rep_nonzero (v : ℙ K V) : v.rep != 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Projectivization.mk_eq_mk_iff'`：mk_eq_mk_iff' (v w : V) (hv : v != 0) (h
w : w != 0) : mk K v hv = mk K w hw ↔ exists a : K, a • w = v
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Projectivization.mk_rep`：mk_rep (v : ℙ K V) : mk K v.rep v.rep_nonzero =
 v

--- 原说明 ---
Two points in a projective space are dependent if and only if they are equal.
-/
theorem dependent_pair_iff_eq (u v : ℙ K V) : Dependent ![u, v] ↔ u = v := by
  rw [dependent_iff_not_independent, independent_iff, linearIndependent_fin2]
  dsimp only [Function.comp_def, Matrix.cons_val]
  simp only [not_and, not_forall, not_not, ← mk_eq_mk_iff' K _ _ (rep_nonzero u) (rep_nonzero v),
    mk_rep, Classical.imp_iff_right_iff]
  exact Or.inl (rep_nonzero v)

/-- Two points in a projective space are independent if and only if the points are not equal. -/
@[simp]
/-
**Projectivization.independent_pair_iff_ne** 是 Mathlib 中的一个定理，位于命名空间 `Projectivi
zation`。
形式化陈述：independent_pair_iff_ne (u v : ℙ K V) : Independent ![u, v] ↔ u != v
参数：u v : ℙ K V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Projectivization.independent_iff_not_dependent`：independent_iff_not_depe
ndent : Independent f ↔ ¬Dependent f
· 使用定理 `Projectivization.dependent_pair_iff_eq`：dependent_pair_iff_eq (u v : ℙ K
 V) : Dependent ![u, v] ↔ u = v
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Two points in a projective space are independent if and only if the points are n
ot equal.
-/
theorem independent_pair_iff_ne (u v : ℙ K V) : Independent ![u, v] ↔ u ≠ v := by
  rw [independent_iff_not_dependent, dependent_pair_iff_eq u v]

/-- Two points are independent if and only if their underlying vectors are linearly independent. -/
/-
**Projectivization.independent_mk_iff_LinearIndependent** 是 Mathlib 中的一个引理，位于命名空
间 `Projectivization`。
形式化陈述：independent_mk_iff_LinearIndependent {u v : V} (hu : u != 0) (hv : v != 0)
 : Independent ![mk K u hu, mk K v hv] ↔ LinearIndependent K ![u, v]
参数：hu : u != 0；hv : v != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Projectivization.independent_pair_iff_ne`：independent_pair_iff_ne (u v :
 ℙ K V) : Independent ![u, v] ↔ u != v
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Projectivization.mk_eq_mk_iff'`：mk_eq_mk_iff' (v w : V) (hv : v != 0) (h
w : w != 0) : mk K v hv = mk K w hw ↔ exists a : K, a • w = v
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `linearIndependent_fin2`：linearIndependent_fin2 {f : Fin 2 -> V} : Linear
Independent K f ↔ f 1 != 0 ∧ forall a : K, a • f 1 != f 0

--- 原说明 ---
Two points are independent if and only if their underlying vectors are linearly 
independent.
-/
lemma independent_mk_iff_LinearIndependent {u v : V} (hu : u ≠ 0) (hv : v ≠ 0) :
    Independent ![mk K u hu, mk K v hv] ↔ LinearIndependent K ![u, v] := by
  rw [independent_pair_iff_ne, ne_eq, mk_eq_mk_iff' K u v hu hv, linearIndependent_fin2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact ⟨fun h ↦ ⟨hv, fun a ha ↦ h ⟨a, ha⟩⟩, fun ⟨_, h⟩ ⟨a, ha⟩ ↦ h a ha⟩

end Projectivization

