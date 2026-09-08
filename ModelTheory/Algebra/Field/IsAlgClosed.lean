/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.ModelTheory.Algebra.Field.CharP
public import Mathlib.ModelTheory.Satisfiability

/-!

# The First-Order Theory of Algebraically Closed Fields

This file defines the theory of algebraically closed fields of characteristic `p`, as well
as proving completeness of the theory and the Lefschetz Principle.

## Main definitions

* `FirstOrder.Language.Theory.ACF p` : the theory of algebraically closed fields of characteristic
  `p` as a theory over the language of rings.
* `FirstOrder.Field.ACF_isComplete` : the theory of algebraically closed fields of characteristic
  `p` is complete whenever `p` is prime or zero.
* `FirstOrder.Field.ACF_zero_realize_iff_infinite_ACF_prime_realize` : the Lefschetz principle.

## Implementation details

To apply a theorem about the model theory of algebraically closed fields to a specific
algebraically closed field `K` which does not have a `Language.ring.Structure` instance,
you must introduce the local instance `compatibleRingOfRing K`. Theorems whose statement requires
both a `Language.ring.Structure` instance and a `Field` instance will all be stated with the
assumption `Field K`, `CharP K p`, `IsAlgClosed K` and `CompatibleRing K` and there are instances
defined saying that these assumptions imply `Theory.field.Model K` and `(Theory.ACF p).Model K`

## References

The first-order theory of algebraically closed fields, along with the Lefschetz Principle and
the Ax-Grothendieck Theorem were first formalized in Lean 3 by Joseph Hua
[here](https://github.com/Jlh18/ModelTheoryInLean8) with the master's thesis
[here](https://github.com/Jlh18/ModelTheory8Report)

-/

@[expose] public section

variable {K : Type*}

namespace FirstOrder

namespace Field

open FirstOrder.Ring FreeCommRing Polynomial Language

/-- A generic monic polynomial of degree `n` as an element of the
free commutative ring in `n + 1` variables, with a variable for each
of the `n` non-leading coefficients of the polynomial and one variable (`Fin.last n`)
for `X`. -/
/-
**FirstOrder.Field.genericMonicPoly** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Field`
。
形式化陈述：genericMonicPoly (n : Nat) : FreeCommRing (Fin (n + 1))
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A generic monic polynomial of degree `n` as an element of the
free commutative ring in `n + 1` variables, with a variable for each
of the `n` non-leading coefficients of the polynomial and one variable (`Fin.las
t n`)
for `X`.
-/
noncomputable def genericMonicPoly (n : ℕ) : FreeCommRing (Fin (n + 1)) :=
  of (Fin.last _) ^ n + ∑ i : Fin n, of i.castSucc * of (Fin.last _) ^ (i : ℕ)

set_option backward.isDefEq.respectTransparency.types false in
/-
**FirstOrder.Field.lift_genericMonicPoly** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.F
ield`。
形式化陈述：lift_genericMonicPoly [CommRing K] [Nontrivial K] {n : Nat} (v : Fin (n + 
1) -> K) : FreeCommRing.lift v (genericMonicPoly n) = (((monicEquivDegreeLT n).t
rans (degreeLTEquiv K n).toEquiv).symm (v ∘ Fin.castSucc)).1.eval (v (Fin.last _
))
参数：v : Fin (n + 1) -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FreeCommRing.lift_of`：lift_of (x : α) : lift f (of x) = f x
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_finsetSum`：eval_finsetSum (s : Finset ι) (g : ι -> R[X])
 (x : R) : (∑ i in s, g i).eval x = ∑ i in s, (g i).eval x
· 使用定理 `Polynomial.eval_monomial`：eval_monomial {n a} : (monomial n a).eval x = 
a * x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_genericMonicPoly [CommRing K] [Nontrivial K] {n : ℕ} (v : Fin (n + 1) → K) :
    FreeCommRing.lift v (genericMonicPoly n) =
    (((monicEquivDegreeLT n).trans (degreeLTEquiv K n).toEquiv).symm (v ∘ Fin.castSucc)).1.eval
      (v (Fin.last _)) := by
  simp [genericMonicPoly, monicEquivDegreeLT, degreeLTEquiv, eval_finsetSum]

/-- A sentence saying every monic polynomial of degree `n` has a root. -/
/-
**FirstOrder.Field.genericMonicPolyHasRoot** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder
.Field`。
形式化陈述：genericMonicPolyHasRoot (n : Nat) : Language.ring.Sentence
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sentence saying every monic polynomial of degree `n` has a root.
-/
noncomputable def genericMonicPolyHasRoot (n : ℕ) : Language.ring.Sentence :=
  (∃' ((termOfFreeCommRing (genericMonicPoly n)).relabel Sum.inr =' 0)).alls
/-
**FirstOrder.Field.realize_genericMonicPolyHasRoot** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Field`。
形式化陈述：realize_genericMonicPolyHasRoot [Field K] [CompatibleRing K] (n : Nat) : K
 ⊨ genericMonicPolyHasRoot n ↔ forall p : { p : K[X] // p.Monic ∧ p.natDegree = 
n }, exists x, p.1.eval x = 0
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FirstOrder.Language.Term.realize_relabel`：realize_relabel {t : L.Term α}
 {g : α -> β} {v : β -> M} : (t.relabel g).realize v = t.realize (v ∘ g)
· 使用定理 `FirstOrder.Ring.realize_termOfFreeCommRing`：realize_termOfFreeCommRing (
p : FreeCommRing α) (v : α -> R) : (termOfFreeCommRing p).realize v = FreeCommRi
ng.lift v p
· 使用定理 `FirstOrder.Field.lift_genericMonicPoly`：lift_genericMonicPoly [CommRing 
K] [Nontrivial K] {n : Nat} (v : Fin (n + 1) -> K) : FreeCommRing.lift v (generi
cMonicPoly n) = (((monicEqui…
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `Fin.snoc_comp_castSucc`：snoc_comp_castSucc {α : Sort*} {a : α} {f : Fin 
n -> α} : (snoc f a : Fin (n + 1) -> α) ∘ castSucc = f
· 使用定理 `FirstOrder.Ring.realize_zero`：realize_zero (v : α -> R) : Term.realize v
 (0 : ring.Term α) = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem realize_genericMonicPolyHasRoot [Field K] [CompatibleRing K] (n : ℕ) :
    K ⊨ genericMonicPolyHasRoot n ↔
      ∀ p : { p : K[X] // p.Monic ∧ p.natDegree = n }, ∃ x, p.1.eval x = 0 := by
  rw [Equiv.forall_congr_left ((monicEquivDegreeLT n).trans (degreeLTEquiv K n).toEquiv)]
  simp [Sentence.Realize, genericMonicPolyHasRoot, lift_genericMonicPoly]

/-- The theory of algebraically closed fields of characteristic `p` as a theory over
the language of rings -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**FirstOrder.Field._root_.FirstOrder.Language.Theory.ACF** 是 Mathlib 中的一个定义，位于命名
空间 `FirstOrder.Field`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def _root_.FirstOrder.Language.Theory.ACF (p : ℕ) : Theory .ring :=
  Theory.fieldOfChar p ∪ genericMonicPolyHasRoot '' {n | 0 < n}
/-
**FirstOrder.Field.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Field`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Language.ring.Structure K] (p : ℕ) [h : (Theory.ACF p).Model K] :
    (Theory.fieldOfChar p).Model K :=
  Theory.Model.mono h Set.subset_union_left
/-
**FirstOrder.Field.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Field`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Field K] [CompatibleRing K] {p : ℕ} [CharP K p] [IsAlgClosed K] :
    (Theory.ACF p).Model K := by
  refine Theory.model_union_iff.2 ⟨inferInstance, ?_⟩
  simp only [Theory.model_iff, Set.mem_image,
    forall_exists_index, and_imp]
  rintro _ n hn0 rfl
  simp only [realize_genericMonicPolyHasRoot]
  rintro ⟨p, _, rfl⟩
  exact IsAlgClosed.exists_root p (ne_of_gt
    (natDegree_pos_iff_degree_pos.1 hn0))
/-
**FirstOrder.Field.modelField_of_modelACF** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Field`。
形式化陈述：modelField_of_modelACF (p : Nat) (K : Type*) [Language.ring.Structure K] [
h : (Theory.ACF p).Model K] : Theory.field.Model K
参数：p : Nat；K : Type*；Theory.ACF p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Theory.Model.mono`：∀ {L : FirstOrder.Language} {M : 
Type w} [inst : L.Structure M] {T T' : L.Theory}, M ⊨ T' → T ⊆ T' → M ⊨ T
· 使用定理 `Set.subset_union_of_subset_left`：subset_union_of_subset_left {s t : Set 
α} (h : s subseteq t) (u : Set α) : s subseteq t union u
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
-/
theorem modelField_of_modelACF (p : ℕ) (K : Type*) [Language.ring.Structure K]
    [h : (Theory.ACF p).Model K] : Theory.field.Model K :=
  Theory.Model.mono h (Set.subset_union_of_subset_left Set.subset_union_left _)

/-- A model for the Theory of algebraically closed fields is a Field. After introducing
this as a local instance on a particular Type, you should usually also introduce
`modelField_of_modelACF p M`, `compatibleRingOfModelField` and `isAlgClosed_of_model_ACF` -/
@[reducible]
/-
**FirstOrder.Field.fieldOfModelACF** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Field`。
形式化陈述：fieldOfModelACF (p : Nat) (K : Type*) [Language.ring.Structure K] [h : (Th
eory.ACF p).Model K] : Field K
参数：p : Nat；K : Type*；Theory.ACF p。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Field.modelField_of_modelACF`：modelField_of_modelACF (p : Nat
) (K : Type*) [Language.ring.Structure K] [h : (Theory.ACF p).Model K] : Theory.
field.Model K

--- 原说明 ---
A model for the Theory of algebraically closed fields is a Field. After introduc
ing
this as a local instance on a particular Type, you should usually also introduce
`modelField_of_modelACF p M`, `compatibleRingOfModelField` and `isAlgClosed_of_m
odel_ACF`
-/
noncomputable def fieldOfModelACF (p : ℕ) (K : Type*)
    [Language.ring.Structure K]
    [h : (Theory.ACF p).Model K] : Field K := by
  have := modelField_of_modelACF p K
  exact fieldOfModelField K
/-
**FirstOrder.Field.isAlgClosed_of_model_ACF** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrde
r.Field`。
形式化陈述：isAlgClosed_of_model_ACF (p : Nat) (K : Type*) [Field K] [CompatibleRing K
] [h : (Theory.ACF p).Model K] : IsAlgClosed K
参数：p : Nat；K : Type*；Theory.ACF p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgClosed.of_exists_root`：of_exists_root (H : forall p : k[X], p.Monic
 -> Irreducible p -> exists x, p.eval x = 0) : IsAlgClosed k
· 使用定理 `FirstOrder.Language.Theory.Model.mono`：∀ {L : FirstOrder.Language} {M : 
Type w} [inst : L.Structure M] {T T' : L.Theory}, M ⊨ T' → T ⊆ T' → M ⊨ T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.natDegree_pos_iff_degree_pos`：natDegree_pos_iff_degree_pos : 
0 < natDegree p ↔ 0 < degree p
· 使用定理 `Polynomial.degree_pos_of_irreducible`：degree_pos_of_irreducible (hp : Ir
reducible p) : 0 < p.degree
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Field.realize_genericMonicPolyHasRoot`：realize_genericMonicPo
lyHasRoot [Field K] [CompatibleRing K] (n : Nat) : K ⊨ genericMonicPolyHasRoot n
 ↔ forall p : { p : K[X] // p.Monic ∧ …
-/
theorem isAlgClosed_of_model_ACF (p : ℕ) (K : Type*)
    [Field K] [CompatibleRing K] [h : (Theory.ACF p).Model K] :
    IsAlgClosed K := by
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hpm hpi
  have h : K ⊨ genericMonicPolyHasRoot '' {n | 0 < n} :=
    Theory.Model.mono h (by simp [Theory.ACF])
  simp only [Theory.model_iff, Set.mem_image,
    forall_exists_index, and_imp] at h
  have := h _ p.natDegree (natDegree_pos_iff_degree_pos.2
    (degree_pos_of_irreducible hpi)) rfl
  rw [realize_genericMonicPolyHasRoot] at this
  exact this ⟨_, hpm, rfl⟩
/-
**FirstOrder.Field.ACF_isSatisfiable** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Field
`。
形式化陈述：ACF_isSatisfiable {p : Nat} (hp : p.Prime ∨ p = 0) : (Theory.ACF p).IsSati
sfiable
参数：hp : p.Prime ∨ p = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Field.instModelACFOfCharPOfIsAlgClosed`：∀ {K : Type u_1} [ins
t : Field K] [inst_1 : FirstOrder.Ring.CompatibleRing K] {p : ℕ} [CharP K p] [Is
AlgClosed K],   K ⊨ FirstOrder.Language…
· 使用定理 `AlgebraicClosure.instCharP`：∀ (k : Type u) [inst : Field k] {p : ℕ} [Cha
rP k p], CharP (AlgebraicClosure k) p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ACF_isSatisfiable {p : ℕ} (hp : p.Prime ∨ p = 0) :
    (Theory.ACF p).IsSatisfiable := by
  cases hp with
  | inl hp =>
    have : Fact p.Prime := ⟨hp⟩
    let _ := compatibleRingOfRing (AlgebraicClosure (ZMod p))
    exact ⟨⟨AlgebraicClosure (ZMod p)⟩⟩
  | inr hp =>
    subst hp
    let _ := compatibleRingOfRing (AlgebraicClosure ℚ)
    exact ⟨⟨AlgebraicClosure ℚ⟩⟩

open Cardinal

/-- The Theory `Theory.ACF p` is `κ`-categorical whenever `κ` is an uncountable cardinal. -/
/-
**FirstOrder.Field.ACF_categorical** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Field`。
形式化陈述：ACF_categorical {p : Nat} (κ : Cardinal) (hκ : ℵ₀ < κ) : Categorical κ (Th
eory.ACF p)
参数：κ : Cardinal；hκ : ℵ₀ < κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Field.modelField_of_modelACF`：modelField_of_modelACF (p : Nat
) (K : Type*) [Language.ring.Structure K] [h : (Theory.ACF p).Model K] : Theory.
field.Model K
· 使用定理 `FirstOrder.Field.isAlgClosed_of_model_ACF`：isAlgClosed_of_model_ACF (p :
 Nat) (K : Type*) [Field K] [CompatibleRing K] [h : (Theory.ACF p).Model K] : Is
AlgClosed K
· 使用定理 `FirstOrder.Field.charP_of_model_fieldOfChar`：charP_of_model_fieldOfChar 
[Field K] [CompatibleRing K] [h : (Theory.fieldOfChar p).Model K] : CharP K p
· 使用定理 `FirstOrder.Field.instModelFieldOfCharOfACF`：∀ {K : Type u_1} [inst : Fir
stOrder.Language.ring.Structure K] (p : ℕ) [h : K ⊨ FirstOrder.Language.Theory.A
CF p],   K ⊨ FirstOrder.Language…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `IsAlgClosed.ringEquiv_of_equiv_of_char_eq`：ringEquiv_of_equiv_of_char_eq
 (p : Nat) [CharP K p] [CharP L p] (hK : ℵ₀ < #K) (hKL : Nonempty (K ≃ L)) : Non
empty (K ≃+* L)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.eq`：∀ {α β : Type u}, Cardinal.mk α = Cardinal.mk β ↔ Nonempty 
(α ≃ β)

--- 原说明 ---
The Theory `Theory.ACF p` is `κ`-categorical whenever `κ` is an uncountable card
inal.
-/
theorem ACF_categorical {p : ℕ} (κ : Cardinal) (hκ : ℵ₀ < κ) :
    Categorical κ (Theory.ACF p) := by
  rintro ⟨M⟩ ⟨N⟩ hM hN
  let _ := fieldOfModelACF p M
  have := modelField_of_modelACF p M
  let _ := compatibleRingOfModelField M
  have := isAlgClosed_of_model_ACF p M
  have := charP_of_model_fieldOfChar p M
  let _ := fieldOfModelACF p N
  have := modelField_of_modelACF p N
  let _ := compatibleRingOfModelField N
  have := isAlgClosed_of_model_ACF p N
  have := charP_of_model_fieldOfChar p N
  constructor
  refine languageEquivEquivRingEquiv.symm ?_
  apply Classical.choice
  refine IsAlgClosed.ringEquiv_of_equiv_of_char_eq p ?_ ?_
  · rw [hM]; exact hκ
  · rw [← Cardinal.eq, hM, hN]
/-
**FirstOrder.Field.ACF_isComplete** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Field`。
形式化陈述：ACF_isComplete {p : Nat} (hp : p.Prime ∨ p = 0) : (Theory.ACF p).IsComplet
e
参数：hp : p.Prime ∨ p = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.Categorical.isComplete`：∀ {L : FirstOrder.Language} (κ : Cardin
al.{w}) (T : L.Theory),   κ.Categorical T →     Cardinal.aleph0 ≤ κ →       Card
inal.lift.{w, max u v…
· 使用定理 `FirstOrder.Field.ACF_categorical`：ACF_categorical {p : Nat} (κ : Cardina
l) (hκ : ℵ₀ < κ) : Categorical κ (Theory.ACF p)
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Cardinal.instNoMaxOrder`：NoMaxOrder Cardinal.{u}
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FirstOrder.Ring.card_ring`：card_ring : card Language.ring = 5
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.lt_aleph0_of_finite`：lt_aleph0_of_finite (α : Type u) [Finite α
] : #α < ℵ₀
· 使用定理 `instFiniteULift`：∀ {α : Type v} [Finite α], Finite (ULift.{u, v} α)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `FirstOrder.Field.ACF_isSatisfiable`：ACF_isSatisfiable {p : Nat} (hp : p.
Prime ∨ p = 0) : (Theory.ACF p).IsSatisfiable
· 使用定理 `FirstOrder.Field.modelField_of_modelACF`：modelField_of_modelACF (p : Nat
) (K : Type*) [Language.ring.Structure K] [h : (Theory.ACF p).Model K] : Theory.
field.Model K
· 使用定理 `FirstOrder.Field.isAlgClosed_of_model_ACF`：isAlgClosed_of_model_ACF (p :
 Nat) (K : Type*) [Field K] [CompatibleRing K] [h : (Theory.ACF p).Model K] : Is
AlgClosed K
· 使用定理 `IsAlgClosed.instInfinite`：∀ {K : Type u_1} [inst : Field K] [IsAlgClosed
 K], Infinite K
-/
theorem ACF_isComplete {p : ℕ} (hp : p.Prime ∨ p = 0) :
    (Theory.ACF p).IsComplete := by
  apply Categorical.isComplete.{0, 0, 0} (Order.succ ℵ₀) _
    (ACF_categorical _ (Order.lt_succ _))
    (Order.le_succ ℵ₀)
  · simp only [card_ring, lift_id']
    exact le_trans (le_of_lt (lt_aleph0_of_finite _)) (Order.le_succ _)
  · exact ACF_isSatisfiable hp
  · rintro ⟨M⟩
    let _ := fieldOfModelACF p M
    have := modelField_of_modelACF p M
    let _ := compatibleRingOfModelField M
    have := isAlgClosed_of_model_ACF p M
    infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-
**FirstOrder.Field.finite_ACF_prime_not_realize_of_ACF_zero_realize** 是 Mathlib 
中的一个定理，位于命名空间 `FirstOrder.Field`。
形式化陈述：finite_ACF_prime_not_realize_of_ACF_zero_realize (φ : Language.ring.Senten
ce) (h : Theory.ACF 0 ⊨ᵇ φ) : Set.Finite { p : Nat.Primes | ¬ Theory.ACF p ⊨ᵇ φ 
}
参数：φ : Language.ring.Sentence；h : Theory.ACF 0 ⊨ᵇ φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Theory.models_iff_finset_models`：models_iff_finset_m
odels {φ : L.Sentence} : T ⊨ᵇ φ ↔ exists T0 : Finset L.Sentence, (T0 : L.Theory)
 subseteq T ∧ (T0 : L.Theory) ⊨ᵇ φ
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用定理 `Set.union_right_comm`：union_right_comm (s₁ s₂ s₃ : Set α) : s₁ union s₂ 
union s₃ = s₁ union s₃ union s₂
· 使用定理 `FirstOrder.Language.Theory.fieldOfChar.eq_1`：∀ (p : ℕ),   FirstOrder.Lan
guage.Theory.fieldOfChar p =     FirstOrder.Language.Theory.field ∪       if p =
 0 then (fun q => FirstOrder.Lang…
· 使用定理 `FirstOrder.Language.Theory.ACF.eq_1`：∀ (p : ℕ),   FirstOrder.Language.Th
eory.ACF p =     FirstOrder.Language.Theory.fieldOfChar p ∪ FirstOrder.Field.gen
ericMonicPolyHasRoot '' {…
· 使用定理 `FirstOrder.Language.Theory.models_sentence_of_mem`：models_sentence_of_me
m {φ : L.Sentence} (h : φ in T) : T ⊨ᵇ φ
· 使用定理 `Set.mem_union_left`：mem_union_left {x : α} {a : Set α} (b : Set α) : x i
n a -> x in a union b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FirstOrder.Field.modelField_of_modelACF`：modelField_of_modelACF (p : Nat
) (K : Type*) [Language.ring.Structure K] [h : (Theory.ACF p).Model K] : Theory.
field.Model K
· 使用定理 `FirstOrder.Field.charP_of_model_fieldOfChar`：charP_of_model_fieldOfChar 
[Field K] [CompatibleRing K] [h : (Theory.fieldOfChar p).Model K] : CharP K p
· 使用定理 `FirstOrder.Field.instModelFieldOfCharOfACF`：∀ {K : Type u_1} [inst : Fir
stOrder.Language.ring.Structure K] (p : ℕ) [h : K ⊨ FirstOrder.Language.Theory.A
CF p],   K ⊨ FirstOrder.Language…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FirstOrder.Language.Term.realize_relabel`：realize_relabel {t : L.Term α}
 {g : α -> β} {v : β -> M} : (t.relabel g).realize v = t.realize (v ∘ g)
· 使用定理 `FirstOrder.Ring.realize_termOfFreeCommRing`：realize_termOfFreeCommRing (
p : FreeCommRing α) (v : α -> R) : (termOfFreeCommRing p).realize v = FreeCommRi
ng.lift v p
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `FirstOrder.Ring.realize_zero`：realize_zero (v : α -> R) : Term.realize v
 (0 : ring.Term α) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CharP.charP_iff_prime_eq_zero`：charP_iff_prime_eq_zero [Nontrivial R] {p
 : Nat} (hp : p.Prime) : CharP R p ↔ (p : R) = 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `CharP.eq`：eq {p q : Nat} (hp : CharP R p) (hq : CharP R q) : p = q
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
（共 36 条，此处仅展示前 30 条）
-/
theorem finite_ACF_prime_not_realize_of_ACF_zero_realize
    (φ : Language.ring.Sentence) (h : Theory.ACF 0 ⊨ᵇ φ) :
    Set.Finite { p : Nat.Primes | ¬ Theory.ACF p ⊨ᵇ φ } := by
  rw [Theory.models_iff_finset_models] at h
  rcases h with ⟨T0, hT0, h⟩
  have f : ∀ ψ ∈ Theory.ACF 0,
      { s : Finset Nat.Primes // ∀ q : Nat.Primes, q ∉ s → Theory.ACF q ⊨ᵇ ψ } := by
    intro ψ hψ
    rw [Theory.ACF, Theory.fieldOfChar, Set.union_right_comm, Set.mem_union, if_pos rfl,
      Set.mem_image] at hψ
    apply Classical.choice
    rcases hψ with h | ⟨p, hp, rfl⟩
    · refine ⟨⟨∅, ?_⟩⟩
      intro q _
      exact Theory.models_sentence_of_mem
        (by rw [Theory.ACF, Theory.fieldOfChar, Set.union_right_comm];
            exact Set.mem_union_left _ h)
    · refine ⟨⟨{⟨p, hp⟩}, ?_⟩⟩
      rintro ⟨q, _⟩ hq ⟨K⟩ _ _
      have hqp : q ≠ p := by simpa [← Nat.Primes.coe_nat_inj] using hq
      let _ := fieldOfModelACF q K
      have := modelField_of_modelACF q K
      let _ := compatibleRingOfModelField K
      have := charP_of_model_fieldOfChar q K
      simp only [eqZero, Term.equal, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
        Term.realize_relabel, Sum.elim_comp_inl, realize_termOfFreeCommRing, map_natCast,
        realize_zero, ← CharP.charP_iff_prime_eq_zero hp]
      intro _
      exact hqp <| CharP.eq K this inferInstance
  let s : Finset Nat.Primes := T0.attach.biUnion (fun φ => f φ.1 (hT0 φ.2))
  have hs : ∀ (p : Nat.Primes) ψ, ψ ∈ T0 → p ∉ s → Theory.ACF p ⊨ᵇ ψ := by
    intro p ψ hψ hpψ
    simp only [s, Finset.mem_biUnion, Finset.mem_attach, true_and,
      Subtype.exists, not_exists] at hpψ
    exact (f ψ (hT0 hψ)).2 p (hpψ _ hψ)
  refine Set.Finite.subset (Finset.finite_toSet s) (Set.compl_subset_comm.2 ?_)
  intro p hp
  exact Theory.models_of_models_theory (fun ψ hψ => hs p ψ hψ hp) h

/-- The **Lefschetz principle**. A first-order sentence is modeled by the theory
of algebraically closed fields of characteristic zero if and only if it is modeled by
the theory of algebraically closed fields of characteristic `p` for infinitely many `p`. -/
/-
**FirstOrder.Field.ACF_zero_realize_iff_infinite_ACF_prime_realize** 是 Mathlib 中
的一个定理，位于命名空间 `FirstOrder.Field`。
形式化陈述：ACF_zero_realize_iff_infinite_ACF_prime_realize {φ : Language.ring.Sentenc
e} : Theory.ACF 0 ⊨ᵇ φ ↔ Set.Infinite { p : Nat.Primes | Theory.ACF p ⊨ᵇ φ }
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.infinite_of_finite_compl`：infinite_of_finite_compl [Infinite α] {s :
 Set α} (hs : sᶜ.Finite) : s.Infinite
· 使用定理 `Nat.Primes.infinite`：Infinite Nat.Primes
· 使用定理 `FirstOrder.Field.finite_ACF_prime_not_realize_of_ACF_zero_realize`：finit
e_ACF_prime_not_realize_of_ACF_zero_realize (φ : Language.ring.Sentence) (h : Th
eory.ACF 0 ⊨ᵇ φ) : Set.Finite { p : Nat.Primes | ¬ Theo…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `FirstOrder.Language.Theory.IsComplete.models_not_iff`：models_not_iff (h 
: T.IsComplete) (φ : L.Sentence) : T ⊨ᵇ φ.not ↔ ¬T ⊨ᵇ φ
· 使用定理 `FirstOrder.Field.ACF_isComplete`：ACF_isComplete {p : Nat} (hp : p.Prime 
∨ p = 0) : (Theory.ACF p).IsComplete
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
The **Lefschetz principle**. A first-order sentence is modeled by the theory
of algebraically closed fields of characteristic zero if and only if it is model
ed by
the theory of algebraically closed fields of characteristic `p` for infinitely m
any `p`.
-/
theorem ACF_zero_realize_iff_infinite_ACF_prime_realize {φ : Language.ring.Sentence} :
    Theory.ACF 0 ⊨ᵇ φ ↔ Set.Infinite { p : Nat.Primes | Theory.ACF p ⊨ᵇ φ } := by
  refine ⟨fun h => Set.infinite_of_finite_compl
      (finite_ACF_prime_not_realize_of_ACF_zero_realize φ h),
    not_imp_not.1 ?_⟩
  simpa [(ACF_isComplete (Or.inr rfl)).models_not_iff,
      fun p : Nat.Primes => (ACF_isComplete (Or.inl p.2)).models_not_iff] using
    finite_ACF_prime_not_realize_of_ACF_zero_realize φ.not

/-- Another statement of the **Lefschetz principle**. A first-order sentence is modeled by the
theory of algebraically closed fields of characteristic zero if and only if it is modeled by the
theory of algebraically closed fields of characteristic `p` for all but finitely many primes `p`.
-/
/-
**FirstOrder.Field.ACF_zero_realize_iff_finite_ACF_prime_not_realize** 是 Mathlib
 中的一个定理，位于命名空间 `FirstOrder.Field`。
形式化陈述：ACF_zero_realize_iff_finite_ACF_prime_not_realize {φ : Language.ring.Sente
nce} : Theory.ACF 0 ⊨ᵇ φ ↔ Set.Finite { p : Nat.Primes | Theory.ACF p ⊨ᵇ φ }ᶜ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Field.finite_ACF_prime_not_realize_of_ACF_zero_realize`：finit
e_ACF_prime_not_realize_of_ACF_zero_realize (φ : Language.ring.Sentence) (h : Th
eory.ACF 0 ⊨ᵇ φ) : Set.Finite { p : Nat.Primes | ¬ Theo…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FirstOrder.Field.ACF_zero_realize_iff_infinite_ACF_prime_realize`：ACF_ze
ro_realize_iff_infinite_ACF_prime_realize {φ : Language.ring.Sentence} : Theory.
ACF 0 ⊨ᵇ φ ↔ Set.Infinite { p : Nat.Primes | Theory.AC…
· 使用定理 `Set.infinite_of_finite_compl`：infinite_of_finite_compl [Infinite α] {s :
 Set α} (hs : sᶜ.Finite) : s.Infinite
· 使用定理 `Nat.Primes.infinite`：Infinite Nat.Primes

--- 原说明 ---
Another statement of the **Lefschetz principle**. A first-order sentence is mode
led by the
theory of algebraically closed fields of characteristic zero if and only if it i
s modeled by the
theory of algebraically closed fields of characteristic `p` for all but finitely
 many primes `p`.
-/
theorem ACF_zero_realize_iff_finite_ACF_prime_not_realize {φ : Language.ring.Sentence} :
    Theory.ACF 0 ⊨ᵇ φ ↔ Set.Finite { p : Nat.Primes | Theory.ACF p ⊨ᵇ φ }ᶜ :=
  ⟨fun h => finite_ACF_prime_not_realize_of_ACF_zero_realize φ h,
    fun h => ACF_zero_realize_iff_infinite_ACF_prime_realize.2
      (Set.infinite_of_finite_compl h)⟩


end Field

end FirstOrder

