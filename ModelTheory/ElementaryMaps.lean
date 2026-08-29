/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.ModelTheory.Substructures

/-!
# Elementary Maps Between First-Order Structures

## Main Definitions

- A `FirstOrder.Language.ElementaryEmbedding` is an embedding that commutes with the
  realizations of formulas.
- The `FirstOrder.Language.elementaryDiagram` of a structure is the set of all sentences with
  parameters that the structure satisfies.
- `FirstOrder.Language.ElementaryEmbedding.ofModelsElementaryDiagram` is the canonical
  elementary embedding of any structure into a model of its elementary diagram.

## Main Results

- The Tarski-Vaught Test for embeddings: `FirstOrder.Language.Embedding.isElementary_of_exists`
  gives a simple criterion for an embedding to be elementary.
-/

@[expose] public section


open FirstOrder

namespace FirstOrder

namespace Language

open Structure

variable (L : Language) (M : Type*) (N : Type*) {P : Type*} {Q : Type*}
variable [L.Structure M] [L.Structure N] [L.Structure P] [L.Structure Q]

/--
Definition of `ElementaryEmbedding` / `ElementaryEmbedding` 的定义

English:
structure ElementaryEmbedding
  parameters: where
  axioms and operations (2):
    - toFun : M -> N
    - map_formula' : forall ⦃n⦄ (φ : L.Formula (Fin n)) (x : Fin n -> M), φ.Realize (toFun ∘ x) ↔ φ.Realize x  [default: by aesop]

中文:
结构 Elementary嵌入
  参数: where
  公理与运算 (2 个):
    - toFun : M -> N
    - map_formula' : 对任意 ⦃n⦄ (φ : L.公式 (有限集 n)) (x : 有限集 n -> M), φ.实数ize (toFun ∘ x) ↔ φ.实数ize x  [默认: by aesop]
-/
structure ElementaryEmbedding where
  /-- The underlying embedding -/
  toFun : M -> N
  -- Porting note:
  -- The autoparam here used to be `obviously`.
  -- We have replaced it with `aesop` but that isn't currently sufficient.
  -- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Aesop.20and.20cases
  -- If that can be improved, we should remove the proofs below.
  map_formula' :
    forall ⦃n⦄ (φ : L.Formula (Fin n)) (x : Fin n -> M), φ.Realize (toFun ∘ x) ↔ φ.Realize x := by
    aesop

@[inherit_doc FirstOrder.Language.ElementaryEmbedding]
scoped[FirstOrder] notation:25 A " ↪ₑ[" L "] " B => FirstOrder.Language.ElementaryEmbedding L A B

variable {L} {M} {N}

namespace ElementaryEmbedding

attribute [coe] toFun

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (M ↪ₑ[L] N) M N where
  body: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    simpa only [ElementaryEmbedding.mk.injEq]

@[simp]

中文:
实例 instFunLike
  签名: : 函数状 (M ↪ₑ[L] N) M N where
  定义体: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    simpa only [ElementaryEmbedding.mk.injEq]

@[simp]

Depends on / 依赖: f.toFun
-/
instance instFunLike : FunLike (M ↪ₑ[L] N) M N where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    simpa only [ElementaryEmbedding.mk.injEq]

@[simp]
/--
theorem `map_boundedFormula` / 定理 `map_boundedFormula`

English:
theorem map_boundedFormula
  statement: (f : M ↪ₑ[L] N) {α : Type*} {n : Nat} (φ : L.BoundedFormula α n)
  proof: by
  classical
    rw [← BoundedFormula.realize_restrictFreeVar' Set.Subset.rfl]; rw [Set.inclusion_eq_id]
    have h :=
      f.map_formula' ((φ.restrictFreeVar id).toFormula.relabel (Fintype.equivFin _))
        (Sum.elim (v ∘ (↑)) xs ∘ (Fintype.equivFin _).symm)
    simp only [Formula.realize_rel

中文:
定理 map_boundedFormula
  结论: (f : M ↪ₑ[L] N) {α : 类型} {n : 自然数} (φ : L.BoundedFormula α n)
  证明: by
  classical
    rw [← BoundedFormula.realize_restrictFreeVar' Set.Subset.rfl]; rw [Set.inclusion_eq_id]
    have h :=
      f.map_formula' ((φ.restrictFreeVar id).toFormula.relabel (Fintype.equivFin _))
        (Sum.elim (v ∘ (↑)) xs ∘ (Fintype.equivFin _).symm)
    simp only [Formula.realize_rel

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_restrictFreeVar, BoundedFormula.realize_toFormula, Fintype, Fintype.equivFin, Formula, Formula.realize_relabel, Function, Function.com, Function.comp_assoc, Set.Subset.rfl, Set.inclusion_eq_id, Subset, Sum.elim, _root_, _root_.Equiv.symm_comp_self, classical, comp_assoc, equivFin, f.map_formula
-/
theorem map_boundedFormula (f : M ↪ₑ[L] N) {α : Type*} {n : Nat} (φ : L.BoundedFormula α n)
    (v : α -> M) (xs : Fin n -> M) : φ.Realize (f ∘ v) (f ∘ xs) ↔ φ.Realize v xs := by
  classical
    rw [← BoundedFormula.realize_restrictFreeVar' Set.Subset.rfl]; rw [Set.inclusion_eq_id]
    have h :=
      f.map_formula' ((φ.restrictFreeVar id).toFormula.relabel (Fintype.equivFin _))
        (Sum.elim (v ∘ (↑)) xs ∘ (Fintype.equivFin _).symm)
    simp only [Formula.realize_relabel, BoundedFormula.realize_toFormula] at h
    rw [← Function.comp_assoc _ _ (Fintype.equivFin _).symm]; rw [Function.comp_assoc _ (Fintype.equivFin _).symm (Fintype.equivFin _)]; rw [_root_.Equiv.symm_comp_self]; rw [Function.comp_id]; rw [Function.comp_assoc]; rw [Sum.elim_comp_inl]; rw [Function.comp_assoc _ _ Sum.inr]; rw [Sum.elim_comp_inr]; rw [← Function.comp_assoc] at h
    refine h.trans ?_
    rw [Function.comp_assoc _ _ (Fintype.equivFin _)]; rw [_root_.Equiv.symm_comp_self]; rw [Function.comp_id]; rw [Sum.elim_comp_inl]; rw [Sum.elim_comp_inr (v ∘ Subtype.val) xs]; rw [BoundedFormula.realize_restrictFreeVar v (by simp)]

@[simp]
/--
theorem `map_formula` / 定理 `map_formula`

English:
theorem map_formula
  given: (f : M ↪ₑ[L] N) {α : Type*} (φ : L.Formula α) (x : α -> M)
  proof: by
  rw [Formula.Realize]; rw [Formula.Realize]; rw [← f.map_boundedFormula]; rw [Unique.eq_default (f ∘ default)]

中文:
定理 map_formula
  条件: (f : M ↪ₑ[L] N) {α : 类型} (φ : L.公式 α) (x : α -> M)
  证明: by
  rw [Formula.Realize]; rw [Formula.Realize]; rw [← f.map_boundedFormula]; rw [Unique.eq_default (f ∘ default)]

Depends on / 依赖: Formula, Formula.Realize, Realize, Unique, Unique.eq_default, eq_default, f.map_boundedFormula, map_boundedFormula
-/
theorem map_formula (f : M ↪ₑ[L] N) {α : Type*} (φ : L.Formula α) (x : α -> M) :
    φ.Realize (f ∘ x) ↔ φ.Realize x := by
  rw [Formula.Realize]; rw [Formula.Realize]; rw [← f.map_boundedFormula]; rw [Unique.eq_default (f ∘ default)]

/--
theorem `map_sentence` / 定理 `map_sentence`

English:
theorem map_sentence
  given: (f : M ↪ₑ[L] N) (φ : L.Sentence)
  statement: M ⊨ φ ↔ N ⊨ φ
  proof: by
  rw [Sentence.Realize]; rw [Sentence.Realize]; rw [← f.map_formula]; rw [Unique.eq_default (f ∘ default)]

中文:
定理 map_sentence
  条件: (f : M ↪ₑ[L] N) (φ : L.Sentence)
  结论: M ⊨ φ ↔ N ⊨ φ
  证明: by
  rw [Sentence.Realize]; rw [Sentence.Realize]; rw [← f.map_formula]; rw [Unique.eq_default (f ∘ default)]

Depends on / 依赖: Realize, Sentence, Sentence.Realize, Unique, Unique.eq_default, eq_default, f.map_formula, map_formula
-/
theorem map_sentence (f : M ↪ₑ[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ := by
  rw [Sentence.Realize]; rw [Sentence.Realize]; rw [← f.map_formula]; rw [Unique.eq_default (f ∘ default)]

/--
theorem `theory_model_iff` / 定理 `theory_model_iff`

English:
theorem theory_model_iff
  given: (f : M ↪ₑ[L] N) (T : L.Theory)
  statement: M ⊨ T ↔ N ⊨ T
  proof: by
  simp only [Theory.model_iff, f.map_sentence]

中文:
定理 theory_model_iff
  条件: (f : M ↪ₑ[L] N) (T : L.Theory)
  结论: M ⊨ T ↔ N ⊨ T
  证明: by
  simp only [Theory.model_iff, f.map_sentence]

Depends on / 依赖: Theory, Theory.model_iff, f.map_sentence, map_sentence, model_iff
-/
theorem theory_model_iff (f : M ↪ₑ[L] N) (T : L.Theory) : M ⊨ T ↔ N ⊨ T := by
  simp only [Theory.model_iff, f.map_sentence]

/--
theorem `elementarilyEquivalent` / 定理 `elementarilyEquivalent`

English:
theorem elementarilyEquivalent
  given: (f : M ↪ₑ[L] N)
  statement: M ≅[L] N
  proof: elementarilyEquivalent_iff.2 f.map_sentence

@[simp]

中文:
定理 elementarilyEquivalent
  条件: (f : M ↪ₑ[L] N)
  结论: M ≅[L] N
  证明: elementarilyEquivalent_iff.2 f.map_sentence

@[simp]

Depends on / 依赖: elementarilyEquivalent_iff, f.map_sentence, map_sentence
-/
theorem elementarilyEquivalent (f : M ↪ₑ[L] N) : M ≅[L] N :=
  elementarilyEquivalent_iff.2 f.map_sentence

@[simp]
/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (φ : M ↪ₑ[L] N)
  statement: Function.Injective φ
  proof: by
  intro x y
  exact (φ.map_formula ((var 0).equal (var 1)) fun i => if i = 0 then x else y).1

中文:
定理 injective
  条件: (φ : M ↪ₑ[L] N)
  结论: 函数.单射 φ
  证明: by
  intro x y
  exact (φ.map_formula ((var 0).equal (var 1)) fun i => if i = 0 then x else y).1

Depends on / 依赖: map_formula
-/
theorem injective (φ : M ↪ₑ[L] N) : Function.Injective φ := by
  intro x y
  exact (φ.map_formula ((var 0).equal (var 1)) fun i => if i = 0 then x else y).1

/--
Instance `embeddingLike` / 实例 `embeddingLike`

English:
instance embeddingLike
  signature: : EmbeddingLike (M ↪ₑ[L] N) M N
  body: { show FunLike (M ↪ₑ[L] N) M N from inferInstance with injective' := injective }

@[simp]

中文:
实例 embeddingLike
  签名: : EmbeddingLike (M ↪ₑ[L] N) M N
  定义体: { show FunLike (M ↪ₑ[L] N) M N from inferInstance with injective' := injective }

@[simp]

Depends on / 依赖: FunLike, injective
-/
instance embeddingLike : EmbeddingLike (M ↪ₑ[L] N) M N :=
  { show FunLike (M ↪ₑ[L] N) M N from inferInstance with injective' := injective }

@[simp]
/--
theorem `map_fun` / 定理 `map_fun`

English:
theorem map_fun
  given: (φ : M ↪ₑ[L] N) {n : Nat} (f : L.Functions n) (x : Fin n -> M)
  proof: by
  have h := φ.map_formula (Formula.graph f) (Fin.cons (funMap f x) x)
  rw [Formula.realize_graph]; rw [Fin.comp_cons]; rw [Formula.realize_graph] at h
  rw [eq_comm]; rw [h]

@[simp]

中文:
定理 map_fun
  条件: (φ : M ↪ₑ[L] N) {n : 自然数} (f : L.函数 n) (x : 有限集 n -> M)
  证明: by
  have h := φ.map_formula (Formula.graph f) (Fin.cons (funMap f x) x)
  rw [Formula.realize_graph]; rw [Fin.comp_cons]; rw [Formula.realize_graph] at h
  rw [eq_comm]; rw [h]

@[simp]

Depends on / 依赖: Fin.comp_cons, Fin.cons, Formula, Formula.graph, Formula.realize_graph, comp_cons, eq_comm, funMap, map_formula, realize_graph
-/
theorem map_fun (φ : M ↪ₑ[L] N) {n : Nat} (f : L.Functions n) (x : Fin n -> M) :
    φ (funMap f x) = funMap f (φ ∘ x) := by
  have h := φ.map_formula (Formula.graph f) (Fin.cons (funMap f x) x)
  rw [Formula.realize_graph]; rw [Fin.comp_cons]; rw [Formula.realize_graph] at h
  rw [eq_comm]; rw [h]

@[simp]
/--
theorem `map_rel` / 定理 `map_rel`

English:
theorem map_rel
  given: (φ : M ↪ₑ[L] N) {n : Nat} (r : L.Relations n) (x : Fin n -> M)
  proof: haveI h := φ.map_formula (r.formula var) x
  h

中文:
定理 map_rel
  条件: (φ : M ↪ₑ[L] N) {n : 自然数} (r : L.关系 n) (x : 有限集 n -> M)
  证明: haveI h := φ.map_formula (r.formula var) x
  h

Depends on / 依赖: formula, map_formula, r.formula
-/
theorem map_rel (φ : M ↪ₑ[L] N) {n : Nat} (r : L.Relations n) (x : Fin n -> M) :
    RelMap r (φ ∘ x) ↔ RelMap r x :=
  haveI h := φ.map_formula (r.formula var) x
  h

/--
Instance `strongHomClass` / 实例 `strongHomClass`

English:
instance strongHomClass
  signature: : StrongHomClass L (M ↪ₑ[L] N) M N where
  body: map_fun
  map_rel := map_rel

@[simp]

中文:
实例 strongHomClass
  签名: : Strong态射类 L (M ↪ₑ[L] N) M N where
  定义体: map_fun
  map_rel := map_rel

@[simp]

Depends on / 依赖: map_fun
-/
instance strongHomClass : StrongHomClass L (M ↪ₑ[L] N) M N where
  map_fun := map_fun
  map_rel := map_rel

@[simp]
/--
theorem `map_constants` / 定理 `map_constants`

English:
theorem map_constants
  given: (φ : M ↪ₑ[L] N) (c : L.Constants)
  statement: φ c = c
  proof: HomClass.map_constants φ c

中文:
定理 map_constants
  条件: (φ : M ↪ₑ[L] N) (c : L.Constants)
  结论: φ c = c
  证明: HomClass.map_constants φ c

Depends on / 依赖: HomClass, HomClass.map_constants, map_constants
-/
theorem map_constants (φ : M ↪ₑ[L] N) (c : L.Constants) : φ c = c :=
  HomClass.map_constants φ c

/--
Definition of `toEmbedding` / `toEmbedding` 的定义

English:
definition toEmbedding
  signature: (f : M ↪ₑ[L] N)
  body: f
  inj' := f.injective
  map_fun' {_} f x := by simp
  map_rel' {_} R x := by simp

中文:
定义 toEmbedding
  签名: (f : M ↪ₑ[L] N)
  定义体: f
  inj' := f.injective
  map_fun' {_} f x := by simp
  map_rel' {_} R x := by simp
-/
def toEmbedding (f : M ↪ₑ[L] N) : M ↪[L] N where
  toFun := f
  inj' := f.injective
  map_fun' {_} f x := by simp
  map_rel' {_} R x := by simp

/--
Definition of `toHom` / `toHom` 的定义

English:
definition toHom
  signature: (f : M ↪ₑ[L] N)
  body: f
  map_fun' {_} f x := by simp
  map_rel' {_} R x := by simp

@[simp]

中文:
定义 toHom
  签名: (f : M ↪ₑ[L] N)
  定义体: f
  map_fun' {_} f x := by simp
  map_rel' {_} R x := by simp

@[simp]
-/
def toHom (f : M ↪ₑ[L] N) : M ->[L] N where
  toFun := f
  map_fun' {_} f x := by simp
  map_rel' {_} R x := by simp

@[simp]
/--
theorem `toEmbedding_toHom` / 定理 `toEmbedding_toHom`

English:
theorem toEmbedding_toHom
  given: (f : M ↪ₑ[L] N)
  statement: f.toEmbedding.toHom = f.toHom
  proof: rfl

@[simp]

中文:
定理 toEmbedding_toHom
  条件: (f : M ↪ₑ[L] N)
  结论: f.toEmbedding.toHom = f.toHom
  证明: rfl

@[simp]
-/
theorem toEmbedding_toHom (f : M ↪ₑ[L] N) : f.toEmbedding.toHom = f.toHom :=
  rfl

@[simp]
/--
theorem `coe_toHom` / 定理 `coe_toHom`

English:
theorem coe_toHom
  given: {f : M ↪ₑ[L] N}
  statement: (f.toHom : M -> N) = (f : M -> N)
  proof: rfl

@[simp]

中文:
定理 coe_toHom
  条件: {f : M ↪ₑ[L] N}
  结论: (f.toHom : M -> N) = (f : M -> N)
  证明: rfl

@[simp]
-/
theorem coe_toHom {f : M ↪ₑ[L] N} : (f.toHom : M -> N) = (f : M -> N) :=
  rfl

@[simp]
/--
theorem `coe_toEmbedding` / 定理 `coe_toEmbedding`

English:
theorem coe_toEmbedding
  given: (f : M ↪ₑ[L] N)
  statement: (f.toEmbedding : M -> N) = (f : M -> N)
  proof: rfl

中文:
定理 coe_toEmbedding
  条件: (f : M ↪ₑ[L] N)
  结论: (f.toEmbedding : M -> N) = (f : M -> N)
  证明: rfl
-/
theorem coe_toEmbedding (f : M ↪ₑ[L] N) : (f.toEmbedding : M -> N) = (f : M -> N) :=
  rfl

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: @Function.Injective (M ↪ₑ[L] N) (M -> N) (↑)
  proof: DFunLike.coe_injective

@[ext]

中文:
定理 coe_injective
  结论: @函数.单射 (M ↪ₑ[L] N) (M -> N) (↑)
  证明: DFunLike.coe_injective

@[ext]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_injective : @Function.Injective (M ↪ₑ[L] N) (M -> N) (↑) :=
  DFunLike.coe_injective

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃f g
  statement: M ↪ₑ[L] N⦄ (h : forall x, f x = g x) : f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: ⦃f g
  结论: M ↪ₑ[L] N⦄ (h : 对任意 x, f x = g x) : f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext ⦃f g : M ↪ₑ[L] N⦄ (h : forall x, f x = g x) : f = g :=
  DFunLike.ext f g h

variable (L) (M)

/-- The identity elementary embedding from a structure to itself -/
@[refl]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : M ↪ₑ[L] M where toFun
  body: id

中文:
定义 refl
  签名: : M ↪ₑ[L] M where toFun
  定义体: id
-/
def refl : M ↪ₑ[L] M where toFun := id

variable {L} {M}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (M ↪ₑ[L] M)
  body: ⟨refl L M⟩

@[simp]

中文:
实例 :
  签名: 可居 (M ↪ₑ[L] M)
  定义体: ⟨refl L M⟩

@[simp]
-/
instance : Inhabited (M ↪ₑ[L] M) :=
  ⟨refl L M⟩

@[simp]
/--
theorem `refl_apply` / 定理 `refl_apply`

English:
theorem refl_apply
  given: (x : M)
  statement: refl L M x = x
  proof: rfl

中文:
定理 refl_apply
  条件: (x : M)
  结论: refl L M x = x
  证明: rfl
-/
theorem refl_apply (x : M) : refl L M x = x :=
  rfl

/-- Composition of elementary embeddings -/
@[trans]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (hnp : N ↪ₑ[L] P) (hmn : M ↪ₑ[L] N)
  body: hnp ∘ hmn
  map_formula' n φ x := by simp [Function.comp_assoc]

@[simp]

中文:
定义 comp
  签名: (hnp : N ↪ₑ[L] P) (hmn : M ↪ₑ[L] N)
  定义体: hnp ∘ hmn
  map_formula' n φ x := by simp [Function.comp_assoc]

@[simp]
-/
def comp (hnp : N ↪ₑ[L] P) (hmn : M ↪ₑ[L] N) : M ↪ₑ[L] P where
  toFun := hnp ∘ hmn
  map_formula' n φ x := by simp [Function.comp_assoc]

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (g : N ↪ₑ[L] P) (f : M ↪ₑ[L] N) (x : M)
  statement: g.comp f x = g (f x)
  proof: rfl

中文:
定理 comp_apply
  条件: (g : N ↪ₑ[L] P) (f : M ↪ₑ[L] N) (x : M)
  结论: g.comp f x = g (f x)
  证明: rfl
-/
theorem comp_apply (g : N ↪ₑ[L] P) (f : M ↪ₑ[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : M ↪ₑ[L] N) (g : N ↪ₑ[L] P) (h : P ↪ₑ[L] Q)
  proof: rfl

中文:
定理 comp_assoc
  条件: (f : M ↪ₑ[L] N) (g : N ↪ₑ[L] P) (h : P ↪ₑ[L] Q)
  证明: rfl
-/
theorem comp_assoc (f : M ↪ₑ[L] N) (g : N ↪ₑ[L] P) (h : P ↪ₑ[L] Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

/--
Definition of `liftWithConstants` / `liftWithConstants` 的定义

English:
definition liftWithConstants
  signature: (f : M ↪ₑ[L] N) (A : Set M)
  body: by
  refine ⟨f, ?_⟩
  intro n φ x
  have h :
    (Sum.elim (fun a => ↑(L.con a)) (⇑f ∘ x) :
      ↑A oplus Fin n -> f.toEmbedding.withConstants A) =
    f ∘ Sum.elim (fun a => ↑(L.con a)) x :=
    (Sum.comp_elim _ _ _).symm
  simpa only [Formula.Realize, ← BoundedFormula.realize_constantsVarsEquiv, 

中文:
定义 liftWithConstants
  签名: (f : M ↪ₑ[L] N) (A : 集合 M)
  定义体: by
  refine ⟨f, ?_⟩
  intro n φ x
  have h :
    (Sum.elim (fun a => ↑(L.con a)) (⇑f ∘ x) :
      ↑A oplus Fin n -> f.toEmbedding.withConstants A) =
    f ∘ Sum.elim (fun a => ↑(L.con a)) x :=
    (Sum.comp_elim _ _ _).symm
  simpa only [Formula.Realize, ← BoundedFormula.realize_constantsVarsEquiv, 

Depends on / 依赖: BoundedFormula, BoundedFormula.constantsVarsEquiv, BoundedFormula.realize_constantsVarsEquiv, Formula, Formula.Realize, L.con, Realize, Sum.comp_elim, Sum.elim, comp_elim, constantsVarsEquiv, f.map_formula, f.toEmbedding.withConstants, map_formula, realize_constantsVarsEquiv, toEmbedding, withConstants
-/
def liftWithConstants (f : M ↪ₑ[L] N) (A : Set M) :
    M ↪ₑ[L[[A]]] (f.toEmbedding.withConstants A) := by
  refine ⟨f, ?_⟩
  intro n φ x
  have h :
    (Sum.elim (fun a => ↑(L.con a)) (⇑f ∘ x) :
      ↑A oplus Fin n -> f.toEmbedding.withConstants A) =
    f ∘ Sum.elim (fun a => ↑(L.con a)) x :=
    (Sum.comp_elim _ _ _).symm
  simpa only [Formula.Realize, ← BoundedFormula.realize_constantsVarsEquiv, h] using!
    f.map_formula
      (BoundedFormula.constantsVarsEquiv φ)
      (Sum.elim (fun a => ↑(L.con a)) x)

end ElementaryEmbedding

variable (L) (M)

/--
Definition of `elementaryDiagram` / `elementaryDiagram` 的定义

English:
abbreviation elementaryDiagram
  signature: : L[[M]].Theory
  body: L[[M]].completeTheory M

中文:
缩写 elementaryDiagram
  签名: : L[[M]].Theory
  定义体: L[[M]].completeTheory M

Depends on / 依赖: completeTheory
-/
abbrev elementaryDiagram : L[[M]].Theory :=
  L[[M]].completeTheory M

set_option backward.isDefEq.respectTransparency false in
/-- The canonical elementary embedding of an `L`-structure into any model of its elementary diagram
-/
@[simps]
/--
Definition of `ElementaryEmbedding.ofModelsElementaryDiagram` / `ElementaryEmbedding.ofModelsElementaryDiagram` 的定义

English:
definition ElementaryEmbedding.ofModelsElementaryDiagram
  signature: (N : Type*) [L.Structure N] [L[[M]].Structure N]
  body: ⟨((↑) : L[[M]].Constants -> N) ∘ Sum.inr, fun n φ x => by
    refine
      _root_.trans ?_
        ((realize_iff_of_model_completeTheory M N
              (((L.lhomWithConstants M).onBoundedFormula φ).subst
                  (Constants.term ∘ Sum.inr ∘ x)).alls).trans
          ?_)
    · simp_rw [Se

中文:
定义 Elementary嵌入.ofModelsElementaryDiagram
  签名: (N : 类型) [L.结构 N] [L[[M]].结构 N]
  定义体: ⟨((↑) : L[[M]].Constants -> N) ∘ Sum.inr, fun n φ x => by
    refine
      _root_.trans ?_
        ((realize_iff_of_model_completeTheory M N
              (((L.lhomWithConstants M).onBoundedFormula φ).subst
                  (Constants.term ∘ Sum.inr ∘ x)).alls).trans
          ?_)
    · simp_rw [Se

Depends on / 依赖: BoundedFormula, BoundedFormula.realiz, BoundedFormula.realize_alls, BoundedFormula.realize_subst, Constants, Constants.term, Formula, Formula.Realize, Function, Function.comp_def, L.lhomWithConstants, LHom.realize_onBoundedFormula, Realize, Sentence, Sentence.Realize, Sum.inr, Term.realize_constants, Unique, Unique.forall_iff, _root_
-/
def ElementaryEmbedding.ofModelsElementaryDiagram (N : Type*) [L.Structure N] [L[[M]].Structure N]
    [(lhomWithConstants L M).IsExpansionOn N] [N ⊨ L.elementaryDiagram M] : M ↪ₑ[L] N :=
  ⟨((↑) : L[[M]].Constants -> N) ∘ Sum.inr, fun n φ x => by
    refine
      _root_.trans ?_
        ((realize_iff_of_model_completeTheory M N
              (((L.lhomWithConstants M).onBoundedFormula φ).subst
                  (Constants.term ∘ Sum.inr ∘ x)).alls).trans
          ?_)
    · simp_rw [Sentence.Realize, BoundedFormula.realize_alls, BoundedFormula.realize_subst,
        LHom.realize_onBoundedFormula, Formula.Realize, Unique.forall_iff, Function.comp_def,
        Term.realize_constants]
    · simp_rw [Sentence.Realize, BoundedFormula.realize_alls, BoundedFormula.realize_subst,
        LHom.realize_onBoundedFormula, Formula.Realize, Unique.forall_iff]
      rfl⟩

variable {L M}

namespace Embedding

/--
theorem `isElementary_of_exists` / 定理 `isElementary_of_exists`

English:
theorem isElementary_of_exists
  statement: (f : M ↪[L] N)
  proof: by
  suffices h : forall (n : Nat) (φ : L.BoundedFormula Empty n) (xs : Fin n -> M),
      φ.Realize (f ∘ default) (f ∘ xs) ↔ φ.Realize default xs by
    intro n φ x
    exact φ.realize_relabel_sumInr.symm.trans (_root_.trans (h n _ _) φ.realize_relabel_sumInr)
  refine fun n φ => φ.recOn ?_ ?_ ?_ ?

中文:
定理 isElementary_of_存在
  结论: (f : M ↪[L] N)
  证明: by
  suffices h : forall (n : Nat) (φ : L.BoundedFormula Empty n) (xs : Fin n -> M),
      φ.Realize (f ∘ default) (f ∘ xs) ↔ φ.Realize default xs by
    intro n φ x
    exact φ.realize_relabel_sumInr.symm.trans (_root_.trans (h n _ _) φ.realize_relabel_sumInr)
  refine fun n φ => φ.recOn ?_ ?_ ?_ ?

Depends on / 依赖: BoundedFormula, BoundedFormula.Realize, HomClass, HomClass.realize_term, Iff.rfl, L.BoundedFormula, Realize, Sum.comp_elim, _root_, _root_.trans, comp_elim, intros, realize_relabel_sumInr, realize_relabel_sumInr.symm.trans, realize_term, simp_rw
-/
theorem isElementary_of_exists (f : M ↪[L] N)
    (htv :
      forall (n : Nat) (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n -> M) (a : N),
        φ.Realize default (Fin.snoc (f ∘ x) a : _ -> N) ->
          exists b : M, φ.Realize default (Fin.snoc (f ∘ x) (f b) : _ -> N)) :
    forall {n} (φ : L.Formula (Fin n)) (x : Fin n -> M), φ.Realize (f ∘ x) ↔ φ.Realize x := by
  suffices h : forall (n : Nat) (φ : L.BoundedFormula Empty n) (xs : Fin n -> M),
      φ.Realize (f ∘ default) (f ∘ xs) ↔ φ.Realize default xs by
    intro n φ x
    exact φ.realize_relabel_sumInr.symm.trans (_root_.trans (h n _ _) φ.realize_relabel_sumInr)
  refine fun n φ => φ.recOn ?_ ?_ ?_ ?_ ?_
  · exact fun {_} _ => Iff.rfl
  · intros
    simp [BoundedFormula.Realize, ← Sum.comp_elim, HomClass.realize_term]
  · intro _ _ R ts xs
    simp only [BoundedFormula.Realize, ← Sum.comp_elim, HomClass.realize_term]
    simp_rw [← Function.comp_apply (f := (f : M -> N)),
      ← Function.comp_apply (f := Term.realize (Sum.elim default xs)),
      ← Function.comp_apply (f := (f : M -> N) ∘ Term.realize (Sum.elim default xs))]
    rw [Function.comp_assoc]; rw [map_rel f]
  · intro _ _ _ ih1 ih2 _
    simp [ih1, ih2]
  · intro n φ ih xs
    simp only [BoundedFormula.realize_all]
    refine ⟨fun h a => ?_, ?_⟩
    · rw [← ih, Fin.comp_snoc]
      exact h (f a)
    · contrapose!
      rintro ⟨a, ha⟩
      obtain ⟨b, hb⟩ := htv n φ.not xs a (by
          rw [BoundedFormula.realize_not]; rw [← Unique.eq_default (f ∘ default)]
          exact ha)
      refine ⟨b, fun h => hb (Eq.mp ?_ ((ih _).2 h))⟩
      rw [Unique.eq_default (f ∘ default)]; rw [Fin.comp_snoc]

/-- Bundles an embedding satisfying the Tarski-Vaught test as an elementary embedding. -/
@[simps]
/--
Definition of `toElementaryEmbedding` / `toElementaryEmbedding` 的定义

English:
definition toElementaryEmbedding
  signature: (f : M ↪[L] N)
  body: ⟨f, fun _ => f.isElementary_of_exists htv⟩

中文:
定义 toElementaryEmbedding
  签名: (f : M ↪[L] N)
  定义体: ⟨f, fun _ => f.isElementary_of_exists htv⟩

Depends on / 依赖: f.isElementary_of_exists, isElementary_of_exists
-/
def toElementaryEmbedding (f : M ↪[L] N)
    (htv :
      forall (n : Nat) (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n -> M) (a : N),
        φ.Realize default (Fin.snoc (f ∘ x) a : _ -> N) ->
          exists b : M, φ.Realize default (Fin.snoc (f ∘ x) (f b) : _ -> N)) :
    M ↪ₑ[L] N :=
  ⟨f, fun _ => f.isElementary_of_exists htv⟩

end Embedding

namespace Equiv

/--
Definition of `toElementaryEmbedding` / `toElementaryEmbedding` 的定义

English:
definition toElementaryEmbedding
  signature: (f : M ≃[L] N)
  body: f

@[simp]

中文:
定义 toElementaryEmbedding
  签名: (f : M ≃[L] N)
  定义体: f

@[simp]
-/
def toElementaryEmbedding (f : M ≃[L] N) : M ↪ₑ[L] N where
  toFun := f

@[simp]
/--
theorem `toElementaryEmbedding_toEmbedding` / 定理 `toElementaryEmbedding_toEmbedding`

English:
theorem toElementaryEmbedding_toEmbedding
  given: (f : M ≃[L] N)
  proof: rfl

@[simp]

中文:
定理 toElementaryEmbedding_toEmbedding
  条件: (f : M ≃[L] N)
  证明: rfl

@[simp]
-/
theorem toElementaryEmbedding_toEmbedding (f : M ≃[L] N) :
    f.toElementaryEmbedding.toEmbedding = f.toEmbedding :=
  rfl

@[simp]
/--
theorem `coe_toElementaryEmbedding` / 定理 `coe_toElementaryEmbedding`

English:
theorem coe_toElementaryEmbedding
  given: (f : M ≃[L] N)
  proof: rfl

中文:
定理 coe_toElementaryEmbedding
  条件: (f : M ≃[L] N)
  证明: rfl
-/
theorem coe_toElementaryEmbedding (f : M ≃[L] N) :
    (f.toElementaryEmbedding : M -> N) = (f : M -> N) :=
  rfl

end Equiv

@[simp]
/--
theorem `realize_term_substructure` / 定理 `realize_term_substructure`

English:
theorem realize_term_substructure
  given: {α : Type*} {S : L.Substructure M} (v : α -> S) (t : L.Term α)
  proof: HomClass.realize_term S.subtype

中文:
定理 realize_term_substructure
  条件: {α : 类型} {S : L.子结构 M} (v : α -> S) (t : L.项 α)
  证明: HomClass.realize_term S.subtype

Depends on / 依赖: HomClass, HomClass.realize_term, S.subtype, realize_term, subtype
-/
theorem realize_term_substructure {α : Type*} {S : L.Substructure M} (v : α -> S) (t : L.Term α) :
    t.realize ((↑) ∘ v) = (↑(t.realize v) : M) :=
  HomClass.realize_term S.subtype

end Language

end FirstOrder
