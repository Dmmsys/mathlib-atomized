/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!

# General-Valued Constraint Satisfaction Problems

General-Valued CSP is a very broad class of problems in discrete optimization.
General-Valued CSP subsumes Min-Cost-Hom (including 3-SAT for example) and Finite-Valued CSP.

## Main definitions
* `ValuedCSP`: A VCSP template; fixes a domain, a codomain, and allowed cost functions.
* `ValuedCSP.Term`: One summand in a VCSP instance; calls a concrete function from given template.
* `ValuedCSP.Term.evalSolution`: An evaluation of the VCSP term for given solution.
* `ValuedCSP.Instance`: An instance of a VCSP problem over given template.
* `ValuedCSP.Instance.evalSolution`: An evaluation of the VCSP instance for given solution.
* `ValuedCSP.Instance.IsOptimumSolution`: Is given solution a minimum of the VCSP instance?
* `Function.HasMaxCutProperty`: Can given binary function express the Max-Cut problem?
* `FractionalOperation`: Multiset of operations on given domain of the same arity.
* `FractionalOperation.IsSymmetricFractionalPolymorphismFor`: Is given fractional operation a
  symmetric fractional polymorphism for given VCSP template?

## References
* [D. A. Cohen, M. C. Cooper, P. Creed, P. G. Jeavons, S. Živný,
  *An Algebraic Theory of Complexity for Discrete Optimisation*][cohen2012]

-/

@[expose] public section

/-- A template for a valued CSP problem over a domain `D` with costs in `C`.
Regarding `C` we want to support `Bool`, `Nat`, `ENat`, `Int`, `Rat`, `NNRat`,
`Real`, `NNReal`, `EReal`, `ENNReal`, and tuples made of any of those types. -/
@[nolint unusedArguments]
/--
Definition of `ValuedCSP` / `ValuedCSP` 的定义

English:
abbreviation ValuedCSP
  signature: (D C : Type*) [AddCommMonoid C] [PartialOrder C] [IsOrderedAddMonoid C]
  body: Set (Σ (n : Nat), (Fin n -> D) -> C) -- Cost functions `D^n → C` for any `n`

中文:
缩写 ValuedCSP
  签名: (D C : 类型) [AddCommMonoid C] [PartialOrder C] [IsOrderedAddMonoid C]
  定义体: Set (Σ (n : Nat), (Fin n -> D) -> C) -- Cost functions `D^n → C` for any `n`

Depends on / 依赖: functions
-/
abbrev ValuedCSP (D C : Type*) [AddCommMonoid C] [PartialOrder C] [IsOrderedAddMonoid C] :=
  Set (Σ (n : Nat), (Fin n -> D) -> C) -- Cost functions `D^n → C` for any `n`

variable {D C : Type*} [AddCommMonoid C] [PartialOrder C] [IsOrderedAddMonoid C]

/--
Definition of `ValuedCSP.Term` / `ValuedCSP.Term` 的定义

English:
structure ValuedCSP.Term
  parameters: (Γ : ValuedCSP D C) (ι : Type*)
  axioms and operations (4):
    - n : Nat
    - f : (Fin n -> D) -> C
    - inΓ : ⟨n, f⟩ in Γ
    - app : Fin n -> ι

中文:
结构 ValuedCSP.Term
  参数: (Γ : ValuedCSP D C) (ι : 类型)
  公理与运算 (4 个):
    - n : 自然数
    - f : (Fin n -> D) -> C
    - inΓ : ⟨n, f⟩ in Γ
    - app : Fin n -> ι
-/
structure ValuedCSP.Term (Γ : ValuedCSP D C) (ι : Type*) where
  /-- Arity of the function -/
  n : Nat
  /-- Which cost function is instantiated -/
  f : (Fin n -> D) -> C
  /-- The cost function comes from the template -/
  inΓ : ⟨n, f⟩ in Γ
  /-- Which variables are plugged as arguments to the cost function -/
  app : Fin n -> ι

/--
Definition of `ValuedCSP.Term.evalSolution` / `ValuedCSP.Term.evalSolution` 的定义

English:
definition ValuedCSP.Term.evalSolution
  signature: {Γ : ValuedCSP D C} {ι : Type*}
  body: t.f (x ∘ t.app)

中文:
定义 ValuedCSP.Term.evalSolution
  签名: {Γ : ValuedCSP D C} {ι : 类型}
  定义体: t.f (x ∘ t.app)

Depends on / 依赖: Countable, Countable.of_equiv, Equiv.ulift.symm, of_equiv, t.app
-/
def ValuedCSP.Term.evalSolution {Γ : ValuedCSP D C} {ι : Type*}
    (t : Γ.Term ι) (x : ι -> D) : C :=
  t.f (x ∘ t.app)

/--
Definition of `ValuedCSP.Instance` / `ValuedCSP.Instance` 的定义

English:
abbreviation ValuedCSP.Instance
  signature: (Γ : ValuedCSP D C) (ι : Type*)
  body: Multiset (Γ.Term ι)

中文:
缩写 ValuedCSP.Instance
  签名: (Γ : ValuedCSP D C) (ι : 类型)
  定义体: Multiset (Γ.Term ι)

Depends on / 依赖: Multiset
-/
abbrev ValuedCSP.Instance (Γ : ValuedCSP D C) (ι : Type*) : Type _ :=
  Multiset (Γ.Term ι)

/--
Definition of `ValuedCSP.Instance.evalSolution` / `ValuedCSP.Instance.evalSolution` 的定义

English:
definition ValuedCSP.Instance.evalSolution
  signature: {Γ : ValuedCSP D C} {ι : Type*}
  body: (I.map (·.evalSolution x)).sum

中文:
定义 ValuedCSP.Instance.evalSolution
  签名: {Γ : ValuedCSP D C} {ι : 类型}
  定义体: (I.map (·.evalSolution x)).sum

Depends on / 依赖: Countable, I.map, Subsingleton, Subsingleton.to_countable, evalSolution, to_countable
-/
def ValuedCSP.Instance.evalSolution {Γ : ValuedCSP D C} {ι : Type*}
    (I : Γ.Instance ι) (x : ι -> D) : C :=
  (I.map (·.evalSolution x)).sum

/--
Definition of `ValuedCSP.Instance.IsOptimumSolution` / `ValuedCSP.Instance.IsOptimumSolution` 的定义

English:
definition ValuedCSP.Instance.IsOptimumSolution
  signature: {Γ : ValuedCSP D C} {ι : Type*}
  body: forall y : ι -> D, I.evalSolution x <= I.evalSolution y

中文:
定义 ValuedCSP.Instance.IsOptimumSolution
  签名: {Γ : ValuedCSP D C} {ι : 类型}
  定义体: forall y : ι -> D, I.evalSolution x <= I.evalSolution y

Depends on / 依赖: Countable, I.evalSolution, Subtype, Subtype.countable, countable, evalSolution
-/
def ValuedCSP.Instance.IsOptimumSolution {Γ : ValuedCSP D C} {ι : Type*}
    (I : Γ.Instance ι) (x : ι -> D) : Prop :=
  forall y : ι -> D, I.evalSolution x <= I.evalSolution y

/--
Definition of `Function.HasMaxCutPropertyAt` / `Function.HasMaxCutPropertyAt` 的定义

English:
definition Function.HasMaxCutPropertyAt
  signature: (f : (Fin 2 -> D) -> C) (a b : D)
  body: f ![a, b] = f ![b, a] ∧
    forall x y : D, f ![a, b] <= f ![x, y] ∧ (f ![a, b] = f ![x, y] -> a = x ∧ b = y ∨ a = y ∧ b = x)

中文:
定义 Function.HasMaxCutPropertyAt
  签名: (f : (Fin 2 -> D) -> C) (a b : D)
  定义体: f ![a, b] = f ![b, a] ∧
    forall x y : D, f ![a, b] <= f ![x, y] ∧ (f ![a, b] = f ![x, y] -> a = x ∧ b = y ∨ a = y ∧ b = x)

Depends on / 依赖: Fin.eq_of_val_eq, Function, Function.Injective.countable, Injective, countable, eq_of_val_eq
-/
def Function.HasMaxCutPropertyAt (f : (Fin 2 -> D) -> C) (a b : D) : Prop :=
  f ![a, b] = f ![b, a] ∧
    forall x y : D, f ![a, b] <= f ![x, y] ∧ (f ![a, b] = f ![x, y] -> a = x ∧ b = y ∨ a = y ∧ b = x)

/--
Definition of `Function.HasMaxCutProperty` / `Function.HasMaxCutProperty` 的定义

English:
definition Function.HasMaxCutProperty
  signature: (f : (Fin 2 -> D) -> C)
  body: exists a b : D, a != b ∧ f.HasMaxCutPropertyAt a b

中文:
定义 Function.HasMaxCutProperty
  签名: (f : (Fin 2 -> D) -> C)
  定义体: exists a b : D, a != b ∧ f.HasMaxCutPropertyAt a b

Depends on / 依赖: Countable, Finite, Finite.to_countable, HasMaxCutPropertyAt, f.HasMaxCutPropertyAt, to_countable
-/
def Function.HasMaxCutProperty (f : (Fin 2 -> D) -> C) : Prop :=
  exists a b : D, a != b ∧ f.HasMaxCutPropertyAt a b

/--
Definition of `FractionalOperation` / `FractionalOperation` 的定义

English:
abbreviation FractionalOperation
  signature: (D : Type*) (m : Nat)
  body: Multiset ((Fin m -> D) -> D)

中文:
缩写 FractionalOperation
  签名: (D : 类型) (m : 自然数)
  定义体: Multiset ((Fin m -> D) -> D)

Depends on / 依赖: Multiset
-/
abbrev FractionalOperation (D : Type*) (m : Nat) : Type _ :=
  Multiset ((Fin m -> D) -> D)

variable {m : Nat}

/-- Arity of the "output" of the fractional operation. -/
@[simp]
/--
Definition of `FractionalOperation.size` / `FractionalOperation.size` 的定义

English:
definition FractionalOperation.size
  signature: (ω : FractionalOperation D m)
  body: ω.card

中文:
定义 FractionalOperation.size
  签名: (ω : FractionalOperation D m)
  定义体: ω.card

Depends on / 依赖: Countable, Prop.countable, countable
-/
def FractionalOperation.size (ω : FractionalOperation D m) : Nat := ω.card

/--
Definition of `FractionalOperation.IsValid` / `FractionalOperation.IsValid` 的定义

English:
definition FractionalOperation.IsValid
  signature: (ω : FractionalOperation D m)
  body: ω != ∅

中文:
定义 FractionalOperation.IsValid
  签名: (ω : FractionalOperation D m)
  定义体: ω != ∅
-/
def FractionalOperation.IsValid (ω : FractionalOperation D m) : Prop :=
  ω != ∅

/--
lemma `FractionalOperation.IsValid.contains` / 引理 `FractionalOperation.IsValid.contains`

English:
lemma FractionalOperation.IsValid.contains
  given: {ω : FractionalOperation D m} (valid : ω.IsValid)
  proof: Multiset.exists_mem_of_ne_zero valid

中文:
引理 FractionalOperation.IsValid.contains
  条件: {ω : FractionalOperation D m} (valid : ω.IsValid)
  证明: Multiset.exists_mem_of_ne_zero valid

Depends on / 依赖: Multiset, Multiset.exists_mem_of_ne_zero, exists_mem_of_ne_zero
-/
lemma FractionalOperation.IsValid.contains {ω : FractionalOperation D m} (valid : ω.IsValid) :
    exists g : (Fin m -> D) -> D, g in ω :=
  Multiset.exists_mem_of_ne_zero valid

/--
Definition of `FractionalOperation.tt` / `FractionalOperation.tt` 的定义

English:
definition FractionalOperation.tt
  signature: {ι : Type*} (ω : FractionalOperation D m) (x : Fin m -> ι -> D)
  body: ω.map (fun (g : (Fin m -> D) -> D) (i : ι) => g ((Function.swap x) i))

中文:
定义 FractionalOperation.tt
  签名: {ι : 类型} (ω : FractionalOperation D m) (x : Fin m -> ι -> D)
  定义体: ω.map (fun (g : (Fin m -> D) -> D) (i : ι) => g ((Function.swap x) i))

Depends on / 依赖: Countable, Function, Function.swap, Quotient, Quotient.countable, countable
-/
def FractionalOperation.tt {ι : Type*} (ω : FractionalOperation D m) (x : Fin m -> ι -> D) :
    Multiset (ι -> D) :=
  ω.map (fun (g : (Fin m -> D) -> D) (i : ι) => g ((Function.swap x) i))

/--
Definition of `Function.AdmitsFractional` / `Function.AdmitsFractional` 的定义

English:
definition Function.AdmitsFractional
  signature: {n : Nat} (f : (Fin n -> D) -> C) (ω : FractionalOperation D m)
  body: forall x : (Fin m -> (Fin n -> D)),
    m • ((ω.tt x).map f).sum <= ω.size • Finset.univ.sum (fun i => f (x i))

中文:
定义 Function.AdmitsFractional
  签名: {n : 自然数} (f : (Fin n -> D) -> C) (ω : FractionalOperation D m)
  定义体: forall x : (Fin m -> (Fin n -> D)),
    m • ((ω.tt x).map f).sum <= ω.size • Finset.univ.sum (fun i => f (x i))

Depends on / 依赖: Countable, Finset, Finset.univ.sum, Quotient, Setoid
-/
def Function.AdmitsFractional {n : Nat} (f : (Fin n -> D) -> C) (ω : FractionalOperation D m) : Prop :=
  forall x : (Fin m -> (Fin n -> D)),
    m • ((ω.tt x).map f).sum <= ω.size • Finset.univ.sum (fun i => f (x i))

/--
Definition of `FractionalOperation.IsFractionalPolymorphismFor` / `FractionalOperation.IsFractionalPolymorphismFor` 的定义

English:
definition FractionalOperation.IsFractionalPolymorphismFor
  body: forall f in Γ, f.snd.AdmitsFractional ω

中文:
定义 FractionalOperation.IsFractionalPolymorphismFor
  定义体: forall f in Γ, f.snd.AdmitsFractional ω

Depends on / 依赖: AdmitsFractional, f.snd.AdmitsFractional
-/
def FractionalOperation.IsFractionalPolymorphismFor
    (ω : FractionalOperation D m) (Γ : ValuedCSP D C) : Prop :=
  forall f in Γ, f.snd.AdmitsFractional ω

/--
Definition of `FractionalOperation.IsSymmetric` / `FractionalOperation.IsSymmetric` 的定义

English:
definition FractionalOperation.IsSymmetric
  signature: (ω : FractionalOperation D m)
  body: forall x y : (Fin m -> D), List.Perm (List.ofFn x) (List.ofFn y) -> forall g in ω, g x = g y

中文:
定义 FractionalOperation.IsSymmetric
  签名: (ω : FractionalOperation D m)
  定义体: forall x y : (Fin m -> D), List.Perm (List.ofFn x) (List.ofFn y) -> forall g in ω, g x = g y

Depends on / 依赖: List.Perm, List.ofFn
-/
def FractionalOperation.IsSymmetric (ω : FractionalOperation D m) : Prop :=
  forall x y : (Fin m -> D), List.Perm (List.ofFn x) (List.ofFn y) -> forall g in ω, g x = g y

/--
Definition of `FractionalOperation.IsSymmetricFractionalPolymorphismFor` / `FractionalOperation.IsSymmetricFractionalPolymorphismFor` 的定义

English:
definition FractionalOperation.IsSymmetricFractionalPolymorphismFor
  body: ω.IsFractionalPolymorphismFor Γ ∧ ω.IsSymmetric

中文:
定义 FractionalOperation.IsSymmetricFractionalPolymorphismFor
  定义体: ω.IsFractionalPolymorphismFor Γ ∧ ω.IsSymmetric

Depends on / 依赖: IsFractionalPolymorphismFor, IsSymmetric
-/
def FractionalOperation.IsSymmetricFractionalPolymorphismFor
    (ω : FractionalOperation D m) (Γ : ValuedCSP D C) : Prop :=
  ω.IsFractionalPolymorphismFor Γ ∧ ω.IsSymmetric

/--
lemma `Function.HasMaxCutPropertyAt.rows_lt_aux` / 引理 `Function.HasMaxCutPropertyAt.rows_lt_aux`

English:
lemma Function.HasMaxCutPropertyAt.rows_lt_aux
  statement: {C : Type*} [PartialOrder C]
  proof: by
  rw [FractionalOperation.tt]; rw [Multiset.mem_map] at rin
  rw [show r = ![r 0]; rw [r 1] by simp [← List.ofFn_inj]]
  apply lt_of_le_of_ne (mcf.right (r 0) (r 1)).left
  intro equ
  have asymm : r 0 != r 1 := by
    rcases (mcf.right (r 0) (r 1)).right equ with ⟨ha0, hb1⟩ | ⟨ha1, hb0⟩
    · rw

中文:
引理 Function.HasMaxCutPropertyAt.rows_lt_aux
  结论: {C : 类型} [PartialOrder C]
  证明: by
  rw [FractionalOperation.tt]; rw [Multiset.mem_map] at rin
  rw [show r = ![r 0]; rw [r 1] by simp [← List.ofFn_inj]]
  apply lt_of_le_of_ne (mcf.right (r 0) (r 1)).left
  intro equ
  have asymm : r 0 != r 1 := by
    rcases (mcf.right (r 0) (r 1)).right equ with ⟨ha0, hb1⟩ | ⟨ha1, hb0⟩
    · rw

Depends on / 依赖: FractionalOperation, FractionalOperation.tt, List.ofFn_inj, Multiset, Multiset.mem_map, convert, hab.symm, in_omega, lt_of_le_of_ne, mcf.right, mem_map, ofFn_inj, symmega
-/
lemma Function.HasMaxCutPropertyAt.rows_lt_aux {C : Type*} [PartialOrder C]
    {f : (Fin 2 -> D) -> C} {a b : D} (mcf : f.HasMaxCutPropertyAt a b) (hab : a != b)
    {ω : FractionalOperation D 2} (symmega : ω.IsSymmetric)
    {r : Fin 2 -> D} (rin : r in (ω.tt ![![a, b], ![b, a]])) :
    f ![a, b] < f r := by
  rw [FractionalOperation.tt]; rw [Multiset.mem_map] at rin
  rw [show r = ![r 0]; rw [r 1] by simp [← List.ofFn_inj]]
  apply lt_of_le_of_ne (mcf.right (r 0) (r 1)).left
  intro equ
  have asymm : r 0 != r 1 := by
    rcases (mcf.right (r 0) (r 1)).right equ with ⟨ha0, hb1⟩ | ⟨ha1, hb0⟩
    · rw [ha0, hb1] at hab
      exact hab
    · rw [ha1, hb0] at hab
      exact hab.symm
  apply asymm
  obtain ⟨o, in_omega, rfl⟩ := rin
  change o (fun j => ![![a, b], ![b, a]] j 0) = o (fun j => ![![a, b], ![b, a]] j 1)
  convert! symmega ![a, b] ![b, a] (by simp [List.Perm.swap]) o in_omega using 2 <;>
    simp [Matrix.const_fin1_eq]

variable {C : Type*} [AddCommMonoid C] [PartialOrder C] [IsOrderedCancelAddMonoid C]

/--
lemma `Function.HasMaxCutProperty.forbids_commutativeFractionalPolymorphism` / 引理 `Function.HasMaxCutProperty.forbids_commutativeFractionalPolymorphism`

English:
lemma Function.HasMaxCutProperty.forbids_commutativeFractionalPolymorphism
  proof: by
  intro contr
  obtain ⟨a, b, hab, mcfab⟩ := mcf
  specialize contr ![![a, b], ![b, a]]
  rw [Fin.sum_univ_two']; rw [← mcfab.left]; rw [← two_nsmul] at contr
  have sharp :
    2 • ((ω.tt ![![a, b], ![b, a]]).map (fun _ => f ![a, b])).sum <
    2 • ((ω.tt ![![a, b], ![b, a]]).map f).sum := by
  

中文:
引理 Function.HasMaxCutProperty.forbids_commutativeFractionalPolymorphism
  证明: by
  intro contr
  obtain ⟨a, b, hab, mcfab⟩ := mcf
  specialize contr ![![a, b], ![b, a]]
  rw [Fin.sum_univ_two']; rw [← mcfab.left]; rw [← two_nsmul] at contr
  have sharp :
    2 • ((ω.tt ![![a, b], ![b, a]]).map (fun _ => f ![a, b])).sum <
    2 • ((ω.tt ![![a, b], ![b, a]]).map f).sum := by
  

Depends on / 依赖: Fin.sum_univ_two, Multiset, Multiset.sum_lt_sum, half_sharp, le_of_lt, mcfab.left, mcfab.rows_lt_aux, rows_lt_aux, specialize, sum_lt_sum, sum_univ_two, symmega, two_nsmul
-/
lemma Function.HasMaxCutProperty.forbids_commutativeFractionalPolymorphism
    {f : (Fin 2 -> D) -> C} (mcf : f.HasMaxCutProperty)
    {ω : FractionalOperation D 2} (valid : ω.IsValid) (symmega : ω.IsSymmetric) :
    ¬ f.AdmitsFractional ω := by
  intro contr
  obtain ⟨a, b, hab, mcfab⟩ := mcf
  specialize contr ![![a, b], ![b, a]]
  rw [Fin.sum_univ_two']; rw [← mcfab.left]; rw [← two_nsmul] at contr
  have sharp :
    2 • ((ω.tt ![![a, b], ![b, a]]).map (fun _ => f ![a, b])).sum <
    2 • ((ω.tt ![![a, b], ![b, a]]).map f).sum := by
    have half_sharp :
      ((ω.tt ![![a, b], ![b, a]]).map (fun _ => f ![a, b])).sum <
      ((ω.tt ![![a, b], ![b, a]]).map f).sum := by
      apply Multiset.sum_lt_sum
      · intro r rin
        exact le_of_lt (mcfab.rows_lt_aux hab symmega rin)
      · obtain ⟨g, _⟩ := valid.contains
        have : (fun i => g ((Function.swap ![![a, b], ![b, a]]) i)) in ω.tt ![![a, b], ![b, a]] := by
          simp only [FractionalOperation.tt, Multiset.mem_map]
          use g
        exact ⟨_, this, mcfab.rows_lt_aux hab symmega this⟩
    rw [two_nsmul]; rw [two_nsmul]
    exact add_lt_add half_sharp half_sharp
  have impos : 2 • (ω.map (fun _ => f ![a, b])).sum < ω.size • 2 • f ![a, b] := by
    convert! lt_of_lt_of_le sharp contr
    simp [FractionalOperation.tt, Multiset.map_map]
  have rhs_swap : ω.size • 2 • f ![a, b] = 2 • ω.size • f ![a, b] := nsmul_left_comm ..
  have distrib : (ω.map (fun _ => f ![a, b])).sum = ω.size • f ![a, b] := by simp
  rw [rhs_swap]; rw [distrib] at impos
  exact ne_of_lt impos rfl
