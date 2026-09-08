/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Internal grading of an `AddMonoidAlgebra`

In this file, we show that an `AddMonoidAlgebra` has an internal direct sum structure.

## Main results

* `AddMonoidAlgebra.gradeBy R f i`: the `i`th grade of an `R[M]` given by the
  degree function `f`.
* `AddMonoidAlgebra.grade R i`: the `i`th grade of an `R[M]` when the degree
  function is the identity.
* `AddMonoidAlgebra.gradeBy.gradedAlgebra`: `AddMonoidAlgebra` is an algebra graded by
  `AddMonoidAlgebra.gradeBy`.
* `AddMonoidAlgebra.grade.gradedAlgebra`: `AddMonoidAlgebra` is an algebra graded by
  `AddMonoidAlgebra.grade`.
* `AddMonoidAlgebra.gradeBy.isInternal`: propositionally, the statement that
  `AddMonoidAlgebra.gradeBy` defines an internal graded structure.
* `AddMonoidAlgebra.grade.isInternal`: propositionally, the statement that
  `AddMonoidAlgebra.grade` defines an internal graded structure when the degree function
  is the identity.
-/

@[expose] public section


noncomputable section

namespace AddMonoidAlgebra

variable {M : Type*} {ι : Type*} {R : Type*}

section

variable (R) [CommSemiring R]

/-- The submodule corresponding to each grade given by the degree function `f`. -/
/-
**AddMonoidAlgebra.gradeBy** 是 Mathlib 中的一个缩写定义，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：gradeBy (f : M -> ι) (i : ι) : Submodule R R[M] where carrier
参数：f : M -> ι；i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule corresponding to each grade given by the degree function `f`.
-/
abbrev gradeBy (f : M → ι) (i : ι) : Submodule R R[M] where
  carrier := { a | ∀ m, m ∈ a.coeff.support → f m = i }
  zero_mem' m h := by cases h
  add_mem' {a b} ha hb m h := by
    classical exact (Finset.mem_union.mp (Finsupp.support_add h)).elim (ha m) (hb m)
  smul_mem' _ _ h := Set.Subset.trans Finsupp.support_smul h

/-- The submodule corresponding to each grade. -/
/-
**AddMonoidAlgebra.grade** 是 Mathlib 中的一个缩写定义，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：grade (m : M) : Submodule R R[M]
参数：m : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule corresponding to each grade.
-/
abbrev grade (m : M) : Submodule R R[M] :=
  gradeBy R id m
/-
**AddMonoidAlgebra.gradeBy_id** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：gradeBy_id : gradeBy R (id : M -> M) = grade R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem gradeBy_id : gradeBy R (id : M → M) = grade R := rfl
/-
**AddMonoidAlgebra.mem_gradeBy_iff** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：mem_gradeBy_iff (f : M -> ι) (i : ι) (a : R[M]) : a in gradeBy R f i ↔ (a.
coeff.support : Set M) subseteq f ⁻¹' {i}
参数：f : M -> ι；i : ι；a : R[M]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_gradeBy_iff (f : M → ι) (i : ι) (a : R[M]) :
    a ∈ gradeBy R f i ↔ (a.coeff.support : Set M) ⊆ f ⁻¹' {i} := by rfl
/-
**AddMonoidAlgebra.mem_grade_iff** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：mem_grade_iff (m : M) (a : R[M]) : a in grade R m ↔ a.coeff.support subset
eq {m}
参数：m : M；a : R[M]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_grade_iff (m : M) (a : R[M]) : a ∈ grade R m ↔ a.coeff.support ⊆ {m} := by
  rw [← Finset.coe_subset, Finset.coe_singleton]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**AddMonoidAlgebra.mem_grade_iff'** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：mem_grade_iff' (m : M) (a : R[M]) : a in grade R m ↔ a in LinearMap.range 
(lsingle (R
参数：m : M；a : R[M]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.mem_grade_iff`：mem_grade_iff (m : M) (a : R[M]) : a in 
grade R m ↔ a.coeff.support subseteq {m}
· 使用定理 `Finsupp.support_subset_singleton'`：support_subset_singleton' {f : α ->₀ 
M} {a : α} : f.support subseteq {a} ↔ exists b, f = single a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_grade_iff' (m : M) (a : R[M]) :
    a ∈ grade R m ↔ a ∈ LinearMap.range (lsingle (R := R) m) := by
  rw [mem_grade_iff, Finsupp.support_subset_singleton']; simp [← coeff_inj, eq_comm]
/-
**AddMonoidAlgebra.grade_eq_lsingle_range** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAl
gebra`。
形式化陈述：grade_eq_lsingle_range (m : M) : grade R m = LinearMap.range (lsingle m)
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `AddMonoidAlgebra.mem_grade_iff'`：mem_grade_iff' (m : M) (a : R[M]) : a i
n grade R m ↔ a in LinearMap.range (lsingle (R
-/
theorem grade_eq_lsingle_range (m : M) : grade R m = LinearMap.range (lsingle m) :=
  Submodule.ext (mem_grade_iff' R m)
/-
**AddMonoidAlgebra.single_mem_gradeBy** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebr
a`。
形式化陈述：single_mem_gradeBy {R} [CommSemiring R] (f : M -> ι) (m : M) (r : R) : sin
gle m r in gradeBy R f (f m)
参数：f : M -> ι；m : M；r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Finsupp.support_single_subset`：support_single_subset : (single a b).supp
ort subseteq {a}
-/
theorem single_mem_gradeBy {R} [CommSemiring R] (f : M → ι) (m : M) (r : R) :
    single m r ∈ gradeBy R f (f m) := by
  intro x hx
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hx)]
/-
**AddMonoidAlgebra.single_mem_grade** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`
。
形式化陈述：single_mem_grade {R} [CommSemiring R] (i : M) (r : R) : single i r in grad
e R i
参数：i : M；r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.single_mem_gradeBy`：single_mem_gradeBy {R} [CommSemirin
g R] (f : M -> ι) (m : M) (r : R) : single m r in gradeBy R f (f m)
-/
theorem single_mem_grade {R} [CommSemiring R] (i : M) (r : R) :
    single i r ∈ grade R i :=
  single_mem_gradeBy _ _ _

end

open DirectSum

/-
**AddMonoidAlgebra.gradeBy.gradedMonoid** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlge
bra.gradeBy`。
形式化陈述：∀ {M : Type u_1} {ι : Type u_2} {R : Type u_3} [inst : AddMonoid M] [inst_
1 : AddMonoid ι] [inst_2 : CommSemiring R]   (f : M →+ ι), SetLike.GradedMonoid 
(AddMonoidAlgebra.gradeBy R ⇑f)
参数：f : M →+ ι；AddMonoidAlgebra.gradeBy R ⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Finsupp.support_single_subset`：support_single_subset : (single a b).supp
ort subseteq {a}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.one_def`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiri
ng R] [inst_1 : Zero M], 1 = AddMonoidAlgebra.single 0 1
· 使用定理 `Finset.mem_add`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Add α]
 {s t : Finset α} {x : α},   x ∈ s + t ↔ ∃ y ∈ s, ∃ z ∈ t, y + z = x
· 使用定理 `AddMonoidAlgebra.support_coeff_mul_subset`：∀ {k : Type u₁} {G : Type u₂}
 [inst : Semiring k] [inst_1 : Add G] [inst_2 : DecidableEq G]   (x y : AddMonoi
dAlgebra k G), (x * y).coeff.su…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
-/
instance gradeBy.gradedMonoid [AddMonoid M] [AddMonoid ι] [CommSemiring R] (f : M →+ ι) :
    SetLike.GradedMonoid (gradeBy R f : ι → Submodule R R[M]) where
  one_mem m h := by
    rw [one_def] at h
    obtain rfl : m = 0 := Finset.mem_singleton.1 <| Finsupp.support_single_subset h
    apply map_zero
  mul_mem i j a b ha hb c hc := by
    classical
    obtain ⟨ma, hma, mb, hmb, rfl⟩ : ∃ y ∈ a.coeff.support, ∃ z ∈ b.coeff.support, y + z = c :=
      Finset.mem_add.1 <| support_coeff_mul_subset a b hc
    rw [map_add, ha ma hma, hb mb hmb]
/-
**AddMonoidAlgebra.grade.gradedMonoid** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebr
a.grade`。
形式化陈述：∀ {M : Type u_1} {R : Type u_3} [inst : AddMonoid M] [inst_1 : CommSemirin
g R],   SetLike.GradedMonoid (AddMonoidAlgebra.grade R)
参数：AddMonoidAlgebra.grade R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.gradeBy.gradedMonoid`：∀ {M : Type u_1} {ι : Type u_2} {
R : Type u_3} [inst : AddMonoid M] [inst_1 : AddMonoid ι] [inst_2 : CommSemiring
 R]   (f : M →+ ι), SetLike…
-/
instance grade.gradedMonoid [AddMonoid M] [CommSemiring R] :
    SetLike.GradedMonoid (grade R : M → Submodule R R[M]) := by
  apply gradeBy.gradedMonoid (AddMonoidHom.id _)

variable [AddMonoid M] [DecidableEq ι] [AddMonoid ι] [CommSemiring R] (f : M →+ ι)

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition; the canonical grade decomposition, used to provide
`DirectSum.decompose`. -/
/-
**AddMonoidAlgebra.decomposeAux** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：decomposeAux : R[M] ->ₐ[R] ⨁ i : ι, gradeBy R f i
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.gradeBy.gradedMonoid`：∀ {M : Type u_1} {ι : Type u_2} {
R : Type u_3} [inst : AddMonoid M] [inst_1 : AddMonoid ι] [inst_2 : CommSemiring
 R]   (f : M →+ ι), SetLike…

--- 原说明 ---
Auxiliary definition; the canonical grade decomposition, used to provide
`DirectSum.decompose`.
-/
def decomposeAux : R[M] →ₐ[R] ⨁ i : ι, gradeBy R f i :=
  lift R _ M {
    toFun m := .of (fun i ↦ gradeBy R f i) (f m.toAdd) ⟨single m.toAdd 1, single_mem_gradeBy _ _ _⟩
    map_one' := of_eq_of_gradedMonoid_eq (by congr 2 <;> simp)
    map_mul' i j := by
      simpa [toAdd_mul, of_mul_of, GradedMonoid.GMul.mul, single_mul_single, mul_one] using
        DirectSum.of_eq_of_gradedMonoid_eq <| Sigma.subtype_ext (f.map_add _ _) rfl
  }
/-
**AddMonoidAlgebra.decomposeAux_single** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgeb
ra`。
形式化陈述：decomposeAux_single (m : M) (r : R) : decomposeAux f (single m r) = .of (f
un i => gradeBy R f i) (f m) ⟨single m r, single_mem_gradeBy _ _ _⟩
参数：m : M；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddMonoidAlgebra.gradeBy.gradedMonoid`：∀ {M : Type u_1} {ι : Type u_2} {
R : Type u_3} [inst : AddMonoid M] [inst_1 : AddMonoid ι] [inst_2 : CommSemiring
 R]   (f : M →+ ι), SetLike…
· 使用定理 `AddMonoidAlgebra.single_mem_gradeBy`：single_mem_gradeBy {R} [CommSemirin
g R] (f : M -> ι) (m : M) (r : R) : single m r in gradeBy R f (f m)
· 使用定理 `AddMonoidAlgebra.lift_single`：lift_single (F : Multiplicative M ->* A) (
a b) : lift R A M F (single a b) = b • F (Multiplicative.ofAdd a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.of_smul`：of_smul (i : ι) (c : R) (x) : of M i (c • x) = c • of
 M i x
· 使用定理 `DirectSum.of_eq_of_gradedMonoid_eq`：of_eq_of_gradedMonoid_eq {A : ι -> T
ype*} [forall i : ι, AddCommMonoid (A i)] {i j : ι} {a : A i} {b : A j} (h : Gra
dedMonoid.mk i a = Grade…
· 使用定理 `Sigma.subtype_ext`：∀ {α : Type u_1} {β : Type u_7} {p : α → β → Prop} {x
₀ x₁ : (a : α) × Subtype (p a)},   x₀.fst = x₁.fst → ↑x₀.snd = ↑x₁.snd → x₀ = x₁
· 使用定理 `AddMonoidAlgebra.smul_single'`：∀ {R : Type u_1} {M : Type u_4} [inst : S
emiring R] (r' : R) (m : M) (r : R),   r' • AddMonoidAlgebra.single m r = AddMon
oidAlgebra.single m…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem decomposeAux_single (m : M) (r : R) :
    decomposeAux f (single m r) =
      .of (fun i ↦ gradeBy R f i) (f m) ⟨single m r, single_mem_gradeBy _ _ _⟩ := by
  refine (lift_single _ _ _).trans ?_
  refine (DirectSum.of_smul R _ _ _).symm.trans ?_
  apply DirectSum.of_eq_of_gradedMonoid_eq
  refine Sigma.subtype_ext rfl ?_
  refine (smul_single' _ _ _).trans ?_
  rw [mul_one]
  rfl
/-
**AddMonoidAlgebra.decomposeAux_coe** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`
。
形式化陈述：decomposeAux_coe {i : ι} (x : gradeBy R f i) : decomposeAux f ↑x = DirectS
um.of (fun i => gradeBy R f i) i x
参数：x : gradeBy R f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.gradeBy.gradedMonoid`：∀ {M : Type u_1} {ι : Type u_2} {
R : Type u_3} [inst : AddMonoid M] [inst_1 : AddMonoid ι] [inst_2 : CommSemiring
 R]   (f : M →+ ι), SetLike…
· 使用定理 `AddMonoidAlgebra.induction`：∀ {R : Type u_1} {M : Type u_4} [inst : Semi
ring R] {motive : AddMonoidAlgebra R M → Prop} (x : AddMonoidAlgebra R M),   mot
ive 0 →     (∀ (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `Set.union_subset_iff`：union_subset_iff {s t u : Set α} : s union t subse
teq u ↔ s subseteq u ∧ t subseteq u
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用引理 `Finsupp.support_add_eq`：support_add_eq [DecidableEq ι] (h : Disjoint g₁.
support g₂.support) : (g₁ + g₂).support = g₁.support union g₂.support
· 使用定理 `AddMonoidAlgebra.coeff_single`：∀ {R : Type u_1} {M : Type u_4} [inst : S
emiring R] (m : M) (r : R), (AddMonoidAlgebra.single m r).coeff = fun₀ | m => r
· 使用定理 `AddMonoidAlgebra.coeff_add`：∀ {R : Type u_1} {M : Type u_4} [inst : Semi
ring R] (x y : AddMonoidAlgebra R M), (x + y).coeff = x.coeff + y.coeff
· 使用定理 `AddMonoidAlgebra.mem_gradeBy_iff`：mem_gradeBy_iff (f : M -> ι) (i : ι) (
a : R[M]) : a in gradeBy R f i ↔ (a.coeff.support : Set M) subseteq f ⁻¹' {i}
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `AddMonoidAlgebra.single_mem_gradeBy`：single_mem_gradeBy {R} [CommSemirin
g R] (f : M -> ι) (m : M) (r : R) : single m r in gradeBy R f (f m)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AddMonoidAlgebra.decomposeAux_single`：decomposeAux_single (m : M) (r : R
) : decomposeAux f (single m r) = .of (fun i => gradeBy R f i) (f m) ⟨single m r
, single_mem_gradeBy _ _ _…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `DirectSum.of_eq_of_gradedMonoid_eq`：of_eq_of_gradedMonoid_eq {A : ι -> T
ype*} [forall i : ι, AddCommMonoid (A i)] {i j : ι} {a : A i} {b : A j} (h : Gra
dedMonoid.mk i a = Grade…
-/
theorem decomposeAux_coe {i : ι} (x : gradeBy R f i) :
    decomposeAux f ↑x = DirectSum.of (fun i => gradeBy R f i) i x := by
  classical
  obtain ⟨x, hx⟩ := x
  revert hx
  refine induction x ?_ ?_
  · intro hx
    symm
    exact map_zero _
  · intro m b y hmy hb ih hmby
    have : Disjoint (Finsupp.single m b).support y.coeff.support := by
      simpa only [Finsupp.support_single _ hb, Finset.disjoint_singleton_left]
    rw [mem_gradeBy_iff, coeff_add, coeff_single, Finsupp.support_add_eq this, Finset.coe_union,
      Set.union_subset_iff] at hmby
    obtain ⟨h1, h2⟩ := hmby
    have : f m = i := by
      rwa [Finsupp.support_single _ hb, Finset.coe_singleton, Set.singleton_subset_iff]
        at h1
    subst this
    simp only [map_add, decomposeAux_single f m]
    let ih' := ih h2
    dsimp at ih'
    rw [ih', ← map_add]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    congr 2

set_option backward.isDefEq.respectTransparency.types false in
/-
**AddMonoidAlgebra.gradeBy.gradedAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidAlg
ebra.gradeBy`。
形式化陈述：{M : Type u_1} →   {ι : Type u_2} →     {R : Type u_3} →       [inst : Add
Monoid M] →         [inst_1 : DecidableEq ι] →           [inst_2 : AddMonoid ι] 
→             [inst_3 : CommSemiring R] → (f : M →+ ι) → GradedAlgebra (AddMonoi
dAlgebra.gradeBy R ⇑f)
参数：f : M →+ ι；AddMonoidAlgebra.gradeBy R ⇑f。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.gradeBy.gradedMonoid`：∀ {M : Type u_1} {ι : Type u_2} {
R : Type u_3} [inst : AddMonoid M] [inst_1 : AddMonoid ι] [inst_2 : CommSemiring
 R]   (f : M →+ ι), SetLike…
-/
instance gradeBy.gradedAlgebra : GradedAlgebra (gradeBy R f) :=
  .ofAlgHom _ (decomposeAux f) (by ext; simp [decomposeAux_single]) <| by simp [decomposeAux_coe]

@[simp]
/-
**AddMonoidAlgebra.decomposeAux_eq_decompose** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoi
dAlgebra`。
形式化陈述：decomposeAux_eq_decompose : ⇑(decomposeAux f : R[M] ->ₐ[R] ⨁ i : ι, gradeB
y R f i) = DirectSum.decompose (gradeBy R f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.gradeBy.gradedMonoid`：∀ {M : Type u_1} {ι : Type u_2} {
R : Type u_3} [inst : AddMonoid M] [inst_1 : AddMonoid ι] [inst_2 : CommSemiring
 R]   (f : M →+ ι), SetLike…
-/
theorem decomposeAux_eq_decompose :
    ⇑(decomposeAux f : R[M] →ₐ[R] ⨁ i : ι, gradeBy R f i) =
      DirectSum.decompose (gradeBy R f) :=
  rfl
/-
**AddMonoidAlgebra.GradesBy.decompose_single** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoi
dAlgebra.GradesBy`。
形式化陈述：∀ {M : Type u_1} {ι : Type u_2} {R : Type u_3} [inst : AddMonoid M] [inst_
1 : DecidableEq ι] [inst_2 : AddMonoid ι]   [inst_3 : CommSemiring R] (f : M →+ 
ι) (m : M) (r : R),   (DirectSum.decompose (AddMonoidAlgebra.gradeBy R ⇑f)) (Add
MonoidAlgebra.single m r) =     (DirectSum.of (fun i => ↥(AddMonoidAlgebra.grade
By R (⇑f) i)) (f m)) ⟨AddMonoidAlgebra.single m r, ⋯⟩
参数：f : M →+ ι；m : M；r : R；DirectSum.decompose (AddMonoidAlgebra.gradeBy R ⇑f)；Ad
dMonoidAlgebra.single m r；DirectSum.of (fun i => ↥(AddMonoidAlgebra.gradeBy R (⇑
f) i)) (f m)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.decomposeAux_single`：decomposeAux_single (m : M) (r : R
) : decomposeAux f (single m r) = .of (fun i => gradeBy R f i) (f m) ⟨single m r
, single_mem_gradeBy _ _ _…
-/
theorem GradesBy.decompose_single (m : M) (r : R) :
    DirectSum.decompose (gradeBy R f) (single m r : R[M]) =
      .of (fun i ↦ gradeBy R f i) (f m) ⟨single m r, single_mem_gradeBy _ _ _⟩ :=
  decomposeAux_single _ _ _
/-
**AddMonoidAlgebra.grade.gradedAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidAlgeb
ra.grade`。
形式化陈述：{ι : Type u_2} →   {R : Type u_3} →     [inst : DecidableEq ι] →       [in
st_1 : AddMonoid ι] → [inst_2 : CommSemiring R] → GradedAlgebra (AddMonoidAlgebr
a.grade R)
参数：AddMonoidAlgebra.grade R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance grade.gradedAlgebra : GradedAlgebra (grade R : ι → Submodule _ _) :=
  inferInstanceAs <| GradedAlgebra (gradeBy R (AddMonoidHom.id ι))
/-
**AddMonoidAlgebra.grade.decompose_single** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAl
gebra.grade`。
形式化陈述：∀ {ι : Type u_2} {R : Type u_3} [inst : DecidableEq ι] [inst_1 : AddMonoid
 ι] [inst_2 : CommSemiring R] (i : ι) (r : R),   (DirectSum.decompose (AddMonoid
Algebra.grade R)) (AddMonoidAlgebra.single i r) =     (DirectSum.of (fun i => ↥(
AddMonoidAlgebra.grade R i)) i) ⟨AddMonoidAlgebra.single i r, ⋯⟩
参数：i : ι；r : R；DirectSum.decompose (AddMonoidAlgebra.grade R)；AddMonoidAlgebra.s
ingle i r；DirectSum.of (fun i => ↥(AddMonoidAlgebra.grade R i)) i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.decomposeAux_single`：decomposeAux_single (m : M) (r : R
) : decomposeAux f (single m r) = .of (fun i => gradeBy R f i) (f m) ⟨single m r
, single_mem_gradeBy _ _ _…
-/
theorem grade.decompose_single (i : ι) (r : R) :
    DirectSum.decompose (grade R : ι → Submodule _ _) (single i r) =
      .of (fun i ↦ grade R i) i ⟨single i r, single_mem_grade _ _⟩ :=
  decomposeAux_single _ _ _

/-- `AddMonoidAlgebra.gradeBy` describe an internally graded algebra. -/
/-
**AddMonoidAlgebra.gradeBy.isInternal** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebr
a.gradeBy`。
形式化陈述：∀ {M : Type u_1} {ι : Type u_2} {R : Type u_3} [inst : AddMonoid M] [inst_
1 : DecidableEq ι] [inst_2 : AddMonoid ι]   [inst_3 : CommSemiring R] (f : M →+ 
ι), DirectSum.IsInternal (AddMonoidAlgebra.gradeBy R ⇑f)
参数：f : M →+ ι；AddMonoidAlgebra.gradeBy R ⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.Decomposition.isInternal`：∀ {ι : Type u_1} {M : Type u_3} {σ :
 Type u_4} [inst : DecidableEq ι] [inst_1 : AddCommMonoid M] [inst_2 : SetLike σ
 M]   [inst_3 : AddSubmo…

--- 原说明 ---
`AddMonoidAlgebra.gradeBy` describe an internally graded algebra.
-/
theorem gradeBy.isInternal : DirectSum.IsInternal (gradeBy R f) :=
  DirectSum.Decomposition.isInternal _

/-- `AddMonoidAlgebra.grade` describe an internally graded algebra. -/
/-
**AddMonoidAlgebra.grade.isInternal** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra.
grade`。
形式化陈述：∀ {ι : Type u_2} {R : Type u_3} [inst : DecidableEq ι] [AddMonoid ι] [inst
_2 : CommSemiring R],   DirectSum.IsInternal (AddMonoidAlgebra.grade R)
参数：AddMonoidAlgebra.grade R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.Decomposition.isInternal`：∀ {ι : Type u_1} {M : Type u_3} {σ :
 Type u_4} [inst : DecidableEq ι] [inst_1 : AddCommMonoid M] [inst_2 : SetLike σ
 M]   [inst_3 : AddSubmo…

--- 原说明 ---
`AddMonoidAlgebra.grade` describe an internally graded algebra.
-/
theorem grade.isInternal : DirectSum.IsInternal (grade R : ι → Submodule R _) :=
  DirectSum.Decomposition.isInternal _

end AddMonoidAlgebra

