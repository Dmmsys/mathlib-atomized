/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Free
public import Mathlib.Topology.Category.Profinite.Nobeling.Span
public import Mathlib.Topology.Category.Profinite.Nobeling.Successor
public import Mathlib.Topology.Category.Profinite.Nobeling.ZeroLimit

/-!
# Nöbeling's theorem

This file proves Nöbeling's theorem. For the overall proof outline see
`Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean`.

## Main result

* `LocallyConstant.freeOfProfinite`: Nöbeling's theorem.
  For `S : Profinite`, the `ℤ`-module `LocallyConstant S ℤ` is free.

## References

- [scholze2019condensed], Theorem 5.4.
-/

@[expose] public section

open Module Topology

universe u

namespace Profinite

namespace NobelingProof

variable {I : Type u} (C : Set (I → Bool)) [LinearOrder I] [WellFoundedLT I]

section Induction
/-!
## The induction

Here we put together the results of the sections `Zero`, `Limit` and `Successor` to prove the
predicate `P I o` holds for all ordinals `o`, and conclude with the main result:

* `GoodProducts.linearIndependent` which says that `GoodProducts C` is linearly independent when `C`
  is closed.

We also define

* `GoodProducts.Basis` which uses `GoodProducts.linearIndependent` and `GoodProducts.span` to
  define a basis for `LocallyConstant C ℤ`
-/

/-
**Profinite.NobelingProof.GoodProducts.P0** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.N
obelingProof.GoodProducts`。
形式化陈述：∀ {I : Type u} [inst : LinearOrder I] [inst_1 : WellFoundedLT I], Profinit
e.NobelingProof.P I 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bool.eq_false_iff`：∀ {b : Bool}, b = false ↔ b ≠ true
· 使用定理 `not_lt_zero`：∀ {α : Type u_1} {a : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], ¬a < 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.subset_singleton_iff_eq`：subset_singleton_iff_eq {s : Set α} {x : α}
 : s subseteq {x} ↔ s = ∅ ∨ s = {x}
· 使用定理 `Profinite.NobelingProof.GoodProducts.linearIndependentEmpty`：∀ {I : Type
 u_1} [inst : LinearOrder I], LinearIndependent ℤ (Profinite.NobelingProof.GoodP
roducts.eval ∅)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Profinite.NobelingProof.GoodProducts.linearIndependentSingleton`：∀ {I : 
Type u_1} [inst : LinearOrder I],   LinearIndependent ℤ (Profinite.NobelingProof
.GoodProducts.eval {fun x => false})

--- 原说明 ---
## The induction

Here we put together the results of the sections `Zero`, `Limit` and `Successor`
 to prove the
predicate `P I o` holds for all ordinals `o`, and conclude with the main result:

* `GoodProducts.linearIndependent` which says that `GoodProducts C` is linearly 
independent when `C`
  is closed.

We also define

* `GoodProducts.Basis` which uses `GoodProducts.linearIndependent` and `GoodProd
ucts.span` to
  define a basis for `LocallyConstant C ℤ`
-/
theorem GoodProducts.P0 : P I 0 := fun _ C _ hsC ↦ by
  have : C ⊆ {(fun _ ↦ false)} := fun c hc ↦ by
    ext x; exact Bool.eq_false_iff.mpr (fun ht ↦ not_lt_zero (hsC c hc x ht))
  rw [Set.subset_singleton_iff_eq] at this
  cases this
  · subst C
    exact linearIndependentEmpty
  · subst C
    exact linearIndependentSingleton
/-
**Profinite.NobelingProof.GoodProducts.Plimit** 是 Mathlib 中的一个定理，位于命名空间 `Profini
te.NobelingProof.GoodProducts`。
形式化陈述：∀ {I : Type u} [inst : LinearOrder I] [inst_1 : WellFoundedLT I] (o : Ordi
nal.{u}),   Order.IsSuccLimit o → (∀ o' < o, Profinite.NobelingProof.P I o') → P
rofinite.NobelingProof.P I o
参数：o : Ordinal.{u}；∀ o' < o, Profinite.NobelingProof.P I o'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Profinite.NobelingProof.GoodProducts.linearIndependent_iff_union_smaller
`：∀ {I : Type u} (C : Set (I → Bool)) [inst : LinearOrder I] [inst_1 : WellFound
edLT I] {o : Ordinal.{u}},   Order.IsSuccLimit o →     Profini…
· 使用定理 `linearIndependent_subtype_iff`：linearIndependent_subtype_iff {s : Set M}
 : LinearIndependent R (Subtype.val : s -> M) ↔ LinearIndepOn R id s
· 使用定理 `linearIndepOn_iUnion_of_directed`：linearIndepOn_iUnion_of_directed {η : 
Type*} {s : η -> Set ι} (hs : Directed (· subseteq ·) s) (h : forall i, LinearIn
depOn R v (s i)) : Lin…
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Profinite.NobelingProof.GoodProducts.smaller_mono`：smaller_mono {o₁ o₂ :
 Ordinal} (h : o₁ <= o₂) : smaller C o₁ subseteq smaller C o₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Profinite.NobelingProof.GoodProducts.linearIndependent_iff_smaller`：line
arIndependent_iff_smaller (o : Ordinal) : LinearIndependent Int (GoodProducts.ev
al (π C (ord I · < o))) ↔ LinearIndependent Int (fun (p …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Profinite.NobelingProof.isClosed_proj`：isClosed_proj (o : Ordinal) (hC :
 IsClosed C) : IsClosed (π C (ord I · < o))
· 使用定理 `Profinite.NobelingProof.contained_proj`：contained_proj (o : Ordinal) : c
ontained (π C (ord I · < o)) o
-/
theorem GoodProducts.Plimit (o : Ordinal) (ho : Order.IsSuccLimit o) :
    (∀ (o' : Ordinal), o' < o → P I o') → P I o := by
  intro h hho C hC hsC
  rw [linearIndependent_iff_union_smaller C ho hsC, linearIndependent_subtype_iff]
  exact linearIndepOn_iUnion_of_directed
    (Monotone.directed_le fun _ _ h ↦ GoodProducts.smaller_mono C h) fun ⟨o', ho'⟩ ↦
    (linearIndependent_iff_smaller _ _).mp (h o' ho' (ho'.le.trans hho)
    (π C (ord I · < o')) (isClosed_proj _ _ hC) (contained_proj _ _))
/-
**Profinite.NobelingProof.GoodProducts.linearIndependentAux** 是 Mathlib 中的一个定理，位
于命名空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：∀ {I : Type u} [inst : LinearOrder I] [inst_1 : WellFoundedLT I] (μ : Ordi
nal.{u}), Profinite.NobelingProof.P I μ
参数：μ : Ordinal.{u}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Profinite.NobelingProof.GoodProducts.P0`：∀ {I : Type u} [inst : LinearOr
der I] [inst_1 : WellFoundedLT I], Profinite.NobelingProof.P I 0
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Profinite.NobelingProof.GoodProducts.linearIndependent_iff_sum`：linearIn
dependent_iff_sum : LinearIndependent Int (eval C) ↔ LinearIndependent Int (SumE
val C ho)
· 使用定理 `ModuleCat.linearIndependent_leftExact`：linearIndependent_leftExact : Lin
earIndependent R u
· 使用定理 `Profinite.NobelingProof.succ_exact`：succ_exact : (ShortComplex.mk (Modul
eCat.ofHom (πs C o)) (ModuleCat.ofHom (Linear_CC' C hsC ho)) (by ext : 2; apply 
CC_comp_zero)).Exact
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Profinite.NobelingProof.isClosed_proj`：isClosed_proj (o : Ordinal) (hC :
 IsClosed C) : IsClosed (π C (ord I · < o))
· 使用定理 `Profinite.NobelingProof.contained_proj`：contained_proj (o : Ordinal) : c
ontained (π C (ord I · < o)) o
· 使用定理 `Profinite.NobelingProof.GoodProducts.linearIndependent_comp_of_eval`：lin
earIndependent_comp_of_eval (h₁ : ⊤ <= Submodule.span Int (Set.range (eval (π C 
(ord I · < o))))) : LinearIndependent Int (eval (C' C ho)…
· 使用定理 `Profinite.NobelingProof.GoodProducts.span`：∀ {I : Type u} (C : Set (I → 
Bool)) [inst : LinearOrder I] [WellFoundedLT I],   IsClosed C → ⊤ ≤ Submodule.sp
an ℤ (Set.range (Profinite.Nobe…
· 使用定理 `Profinite.NobelingProof.isClosed_C'`：isClosed_C' : IsClosed (C' C ho)
· 使用定理 `Profinite.NobelingProof.contained_C'`：contained_C' : contained (C' C ho)
 o
· 使用定理 `Profinite.NobelingProof.succ_mono`：succ_mono : CategoryTheory.Mono (Modu
leCat.ofHom (πs C o))
· 使用定理 `Profinite.NobelingProof.GoodProducts.square_commutes`：square_commutes : 
SumEval C ho ∘ Sum.inl = ModuleCat.ofHom (πs C o) ∘ eval (π C (ord I · < o))
· 使用定理 `Profinite.NobelingProof.GoodProducts.Plimit`：∀ {I : Type u} [inst : Line
arOrder I] [inst_1 : WellFoundedLT I] (o : Ordinal.{u}),   Order.IsSuccLimit o →
 (∀ o' < o, Profinite.NobelingPro…
-/
theorem GoodProducts.linearIndependentAux (μ : Ordinal) : P I μ := by
  refine Ordinal.limitRecOn μ P0 (fun o h ho C hC hsC ↦ ?_)
      (fun o ho h ↦ (GoodProducts.Plimit o ho (fun o' ho' ↦ (h o' ho'))))
  have ho' : o < Ordinal.type (· < · : I → I → Prop) :=
    lt_of_lt_of_le (Order.lt_succ _) ho
  rw [linearIndependent_iff_sum C hsC ho']
  refine ModuleCat.linearIndependent_leftExact (succ_exact C hC hsC ho') ?_ ?_ (succ_mono C o)
    (square_commutes C ho')
  · exact h (le_of_lt ho') (π C (ord I · < o)) (isClosed_proj C o hC) (contained_proj C o)
  · exact linearIndependent_comp_of_eval C hC hsC ho' (span (π C (ord I · < o))
      (isClosed_proj C o hC)) (h (le_of_lt ho') (C' C ho') (isClosed_C' C hC ho')
      (contained_C' C ho'))
/-
**Profinite.NobelingProof.GoodProducts.linearIndependent** 是 Mathlib 中的一个定理，位于命名
空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：∀ {I : Type u} (C : Set (I → Bool)) [inst : LinearOrder I] [WellFoundedLT 
I],   IsClosed C → LinearIndependent ℤ (Profinite.NobelingProof.GoodProducts.eva
l C)
参数：C : Set (I → Bool)；Profinite.NobelingProof.GoodProducts.eval C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Profinite.NobelingProof.GoodProducts.linearIndependentAux`：∀ {I : Type u
} [inst : LinearOrder I] [inst_1 : WellFoundedLT I] (μ : Ordinal.{u}), Profinite
.NobelingProof.P I μ
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Ordinal.typein_lt_type`：typein_lt_type (r : α -> α -> Prop) [IsWellOrder
 α r] (a : α) : typein r a < type r
-/
theorem GoodProducts.linearIndependent (hC : IsClosed C) :
    LinearIndependent ℤ (GoodProducts.eval C) :=
  GoodProducts.linearIndependentAux (Ordinal.type (· < · : I → I → Prop)) (le_refl _)
    C hC (fun _ _ _ _ ↦ Ordinal.typein_lt_type _ _)

/-- `GoodProducts C` as a `ℤ`-basis for `LocallyConstant C ℤ`. -/
noncomputable
/-
**Profinite.NobelingProof.GoodProducts.Basis** 是 Mathlib 中的一个定义，位于命名空间 `Profinit
e.NobelingProof.GoodProducts`。
形式化陈述：{I : Type u} →   (C : Set (I → Bool)) →     [inst : LinearOrder I] →      
 [WellFoundedLT I] → IsClosed C → Module.Basis ↑(Profinite.NobelingProof.GoodPro
ducts C) ℤ (LocallyConstant ↑C ℤ)
参数：C : Set (I → Bool)；Profinite.NobelingProof.GoodProducts C；LocallyConstant ↑C 
ℤ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Profinite.NobelingProof.GoodProducts.linearIndependent`：∀ {I : Type u} (
C : Set (I → Bool)) [inst : LinearOrder I] [WellFoundedLT I],   IsClosed C → Lin
earIndependent ℤ (Profinite.NobelingProof.Go…
· 使用定理 `Profinite.NobelingProof.GoodProducts.span`：∀ {I : Type u} (C : Set (I → 
Bool)) [inst : LinearOrder I] [WellFoundedLT I],   IsClosed C → ⊤ ≤ Submodule.sp
an ℤ (Set.range (Profinite.Nobe…
-/
def GoodProducts.Basis (hC : IsClosed C) :
    Basis (GoodProducts C) ℤ (LocallyConstant C ℤ) :=
  Basis.mk (GoodProducts.linearIndependent C hC) (GoodProducts.span C hC)

end Induction

variable {S : Profinite} {ι : S → I → Bool} (hι : IsClosedEmbedding ι)
include hι

/--
Given a profinite set `S` and a closed embedding `S → (I → Bool)`, the `ℤ`-module
`LocallyConstant C ℤ` is free.
-/
/-
**Profinite.NobelingProof.Nobeling_aux** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nobe
lingProof`。
形式化陈述：Nobeling_aux : Module.Free Int (LocallyConstant S Int)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_equiv'`：of_equiv' {P : Type v} [AddCommMonoid P] [Module 
R P] (_ : Module.Free R P) (e : P ≃ₗ[R] N) : Module.Free R N
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
· 使用定理 `Topology.IsClosedEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → Topo…

--- 原说明 ---
Given a profinite set `S` and a closed embedding `S → (I → Bool)`, the `ℤ`-modul
e
`LocallyConstant C ℤ` is free.
-/
theorem Nobeling_aux : Module.Free ℤ (LocallyConstant S ℤ) := Module.Free.of_equiv'
  (Module.Free.of_basis <| GoodProducts.Basis _ hι.isClosed_range) (LocallyConstant.congrLeftₗ ℤ
    hι.isEmbedding.toHomeomorph).symm

end NobelingProof

variable (S : Profinite.{u})

open scoped Classical in
/-- The embedding `S → (I → Bool)` where `I` is the set of clopens of `S`. -/
noncomputable
/-
**Profinite.Nobeling.** 是 Mathlib 中的一个定义，位于命名空间 `Profinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Nobeling.ι : S → ({C : Set S // IsClopen C} → Bool) := fun s C => decide (s ∈ C.1)

/-- The map `Nobeling.ι` is a closed embedding. -/
/-
**Profinite.Nobeling.isClosedEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nobe
ling`。
形式化陈述：∀ (S : Profinite), Topology.IsClosedEmbedding (Profinite.Nobeling.ι S)
参数：S : Profinite；Profinite.Nobeling.ι S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.isClosedEmbedding`：Continuous.isClosedEmbedding [CompactSpace
 X] [T2Space Y] {f : X -> Y} (h : Continuous f) (hf : Function.Injective f) : Is
ClosedEmbedding f
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `TopologicalSpace.DiscreteTopology.metrizableSpace`：∀ {X : Type u_2} [ins
t : TopologicalSpace X] [DiscreteTopology X], TopologicalSpace.MetrizableSpace X
· 使用定理 `instDiscreteTopologyBool`：DiscreteTopology Bool
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocallyConstant.iff_continuous`：iff_continuous {_ : TopologicalSpace Y
} [DiscreteTopology Y] (f : X -> Y) : IsLocallyConstant f ↔ Continuous f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsLocallyConstant.tfae`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] (f : X → Y),   [IsLocallyConstant f, ∀ (x : X), ∀ᶠ (x' : X) in nhds 
x, f x' = f …
· 使用定理 `IsClopen.isOpen`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X},
 IsClopen s → IsOpen s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isClopen_compl_iff`：isClopen_compl_iff : IsClopen sᶜ ↔ IsClopen s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `exists_isClopen_of_totally_separated`：exists_isClopen_of_totally_separat
ed {α : Type*} [TopologicalSpace α] [TotallySeparatedSpace α] : Pairwise (exists
 U : Set α, IsClopen U ∧ ·…
· 使用定理 `instTotallySeparatedSpaceOfTotallyDisconnectedSpace`：∀ {H : Type u_3} [i
nst : TopologicalSpace H] [LocallyCompactSpace H] [T2Space H] [TotallyDisconnect
edSpace H],   TotallySeparatedSpace H
· 使用定理 `WeaklyLocallyCompactSpace.locallyCompactSpace`：∀ {X : Type u_1} [inst : 
TopologicalSpace X] [R1Space X] [WeaklyLocallyCompactSpace X], LocallyCompactSpa
ce X
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
The map `Nobeling.ι` is a closed embedding.
-/
theorem Nobeling.isClosedEmbedding : IsClosedEmbedding (Nobeling.ι S) := by
  classical
  apply Continuous.isClosedEmbedding
  · dsimp +unfoldPartialApp [ι]
    refine continuous_pi ?_
    intro C
    rw [← IsLocallyConstant.iff_continuous]
    refine ((IsLocallyConstant.tfae _).out 0 3).mpr ?_
    rintro ⟨⟩
    · refine IsClopen.isOpen (isClopen_compl_iff.mp ?_)
      convert! C.2
      ext x
      simp
    · refine IsClopen.isOpen ?_
      convert! C.2
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq]
  · intro a b h
    by_contra hn
    obtain ⟨C, hC, hh⟩ := exists_isClopen_of_totally_separated hn
    apply hh.2 ∘ of_decide_eq_true
    dsimp +unfoldPartialApp [ι] at h
    rw [← congr_fun h ⟨C, hC⟩]
    exact decide_eq_true hh.1

end Profinite

open Profinite NobelingProof

/-- **Nöbeling's theorem**. The `ℤ`-module `LocallyConstant S ℤ` is free for every
`S : Profinite`. -/
/-
**LocallyConstant.freeOfProfinite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LocallyConstant.freeOfProfinite (S : Profinite.{u}) : Module.Free Int (Loc
allyConstant S Int)
参数：S : Profinite.{u}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_wellFoundedLT`：exists_wellFoundedLT : exists (_ : LinearOrder α),
 WellFoundedLT α
· 使用定理 `Profinite.NobelingProof.Nobeling_aux`：Nobeling_aux : Module.Free Int (Lo
callyConstant S Int)
· 使用定理 `Profinite.Nobeling.isClosedEmbedding`：∀ (S : Profinite), Topology.IsClos
edEmbedding (Profinite.Nobeling.ι S)

--- 原说明 ---
**Nöbeling's theorem**. The `ℤ`-module `LocallyConstant S ℤ` is free for every
`S : Profinite`.
-/
instance LocallyConstant.freeOfProfinite (S : Profinite.{u}) :
    Module.Free ℤ (LocallyConstant S ℤ) := by
  obtain ⟨_, _⟩ := exists_wellFoundedLT {C : Set S // IsClopen C}
  exact @Nobeling_aux {C : Set S // IsClopen C} _ _ S (Nobeling.ι S) (Nobeling.isClosedEmbedding S)
