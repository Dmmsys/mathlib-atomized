/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Data.SetLike.Basic
public import Mathlib.Data.Rel
public import Mathlib.ModelTheory.Semantics
public import Mathlib.Tactic.FunProp

/-!
# Definable Sets

This file defines what it means for a set over a first-order structure to be definable.

## Main Definitions

- `Set.Definable` is defined so that `A.Definable L s` indicates that the
  set `s` of a finite Cartesian power of `M` is definable with parameters in `A`.
- `Set.Definable₁` is defined so that `A.Definable₁ L s` indicates that
  `(s : Set M)` is definable with parameters in `A`.
- `Set.Definable₂` is defined so that `A.Definable₂ L s` indicates that
  `(s : Set (M × M))` is definable with parameters in `A`.
- A `FirstOrder.Language.DefinableSet` is defined so that `L.DefinableSet A α` is the Boolean
  algebra of subsets of `α → M` defined by formulas with parameters in `A`.
- `Set.TermDefinable` functions are those equivalent to some term expressible in the language.
- `Set.TermDefinable₁` specialize this to case of unary functions.

## Main Results

- `L.DefinableSet A α` forms a `BooleanAlgebra`
- `Set.Definable.image_comp` shows that definability is closed under projections in finite
  dimensions.
- The `Set.TermDefinable` property is transitive, and `TermDefinable` functions are closed under
  composition.

-/

@[expose] public section


universe u v w u₁

namespace Set

variable {M : Type w} (A : Set M) (L : FirstOrder.Language.{u, v}) [L.Structure M]

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

variable {α : Type u₁} {β : Type*}

/--
Definition of `Definable` / `Definable` 的定义

English:
definition Definable
  signature: (s : Set (α -> M))
  body: exists φ : L[[A]].Formula α, s = Set.ofPred φ.Realize

中文:
定义 Definable
  签名: (s : 集合 (α -> M))
  定义体: exists φ : L[[A]].Formula α, s = Set.ofPred φ.Realize

Depends on / 依赖: Formula, Realize, Set.ofPred, ofPred
-/
def Definable (s : Set (α -> M)) : Prop :=
  exists φ : L[[A]].Formula α, s = Set.ofPred φ.Realize

variable {L} {A} {B : Set M} {s : Set (α -> M)}

/--
theorem `Definable.map_expansion` / 定理 `Definable.map_expansion`

English:
theorem Definable.map_expansion
  statement: {L' : FirstOrder.Language} [L'.Structure M] (h : A.Definable L s)
  proof: by
  obtain ⟨ψ, rfl⟩ := h
  refine ⟨(φ.addConstants A).onFormula ψ, ?_⟩
  ext x
  simp only [mem_ofPred_eq, LHom.realize_onFormula]

中文:
定理 Definable.map_expansion
  结论: {L' : FirstOrder.Language} [L'.结构 M] (h : A.Definable L s)
  证明: by
  obtain ⟨ψ, rfl⟩ := h
  refine ⟨(φ.addConstants A).onFormula ψ, ?_⟩
  ext x
  simp only [mem_ofPred_eq, LHom.realize_onFormula]

Depends on / 依赖: LHom.realize_onFormula, addConstants, mem_ofPred_eq, onFormula, realize_onFormula
-/
theorem Definable.map_expansion {L' : FirstOrder.Language} [L'.Structure M] (h : A.Definable L s)
    (φ : L ->ᴸ L') [φ.IsExpansionOn M] : A.Definable L' s := by
  obtain ⟨ψ, rfl⟩ := h
  refine ⟨(φ.addConstants A).onFormula ψ, ?_⟩
  ext x
  simp only [mem_ofPred_eq, LHom.realize_onFormula]

/--
theorem `definable_iff_exists_formula_sum` / 定理 `definable_iff_exists_formula_sum`

English:
theorem definable_iff_exists_formula_sum
  proof: by
  rw [Definable]; rw [Equiv.exists_congr_left (BoundedFormula.constantsVarsEquiv)]
  refine exists_congr (fun φ => iff_iff_eq.2 (congr_arg (s = ·) ?_))
  ext
  simp only [BoundedFormula.constantsVarsEquiv, constantsOn,
    mem_ofPred_eq, Formula.Realize]
  refine BoundedFormula.realize_mapTermRel_id ?_ (fun _ _ _ => rfl)
  intros
  simp only [Term.constantsVarsEquivLeft_symm_apply, Term.realize_varsToConstants,
    coe_con, Term.realize_relabel]
  congr 1 with a
  rcases a with (_ | _) | _ <;> rfl

中文:
定理 definable_iff_存在_formula_sum
  证明: by
  rw [Definable]; rw [Equiv.exists_congr_left (BoundedFormula.constantsVarsEquiv)]
  refine exists_congr (fun φ => iff_iff_eq.2 (congr_arg (s = ·) ?_))
  ext
  simp only [BoundedFormula.constantsVarsEquiv, constantsOn,
    mem_ofPred_eq, Formula.Realize]
  refine BoundedFormula.realize_mapTermRel_id ?_ (fun _ _ _ => rfl)
  intros
  simp only [Term.constantsVarsEquivLeft_symm_apply, Term.realize_varsToConstants,
    coe_con, Term.realize_relabel]
  congr 1 with a
  rcases a with (_ | _) | _ <;> rfl

Depends on / 依赖: BoundedFormula, BoundedFormula.constantsVarsEquiv, BoundedFormula.realize_mapTermRel_id, Definable, Equiv.exists_congr_left, Formula, Formula.Realize, Realize, Term.constantsVarsEquivLeft_symm_apply, Term.realize_relabel, Term.realize_varsToConstants, coe_con, congr_arg, constantsOn, constantsVarsEquiv, constantsVarsEquivLeft_symm_apply, exists_congr, exists_congr_left, iff_iff_eq, intros
-/
theorem definable_iff_exists_formula_sum :
    A.Definable L s ↔ exists φ : L.Formula (A oplus α), s = {v | φ.Realize (Sum.elim (↑) v)} := by
  rw [Definable]; rw [Equiv.exists_congr_left (BoundedFormula.constantsVarsEquiv)]
  refine exists_congr (fun φ => iff_iff_eq.2 (congr_arg (s = ·) ?_))
  ext
  simp only [BoundedFormula.constantsVarsEquiv, constantsOn,
    mem_ofPred_eq, Formula.Realize]
  refine BoundedFormula.realize_mapTermRel_id ?_ (fun _ _ _ => rfl)
  intros
  simp only [Term.constantsVarsEquivLeft_symm_apply, Term.realize_varsToConstants,
    coe_con, Term.realize_relabel]
  congr 1 with a
  rcases a with (_ | _) | _ <;> rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `empty_definable_iff` / 定理 `empty_definable_iff`

English:
theorem empty_definable_iff
  proof: by
  rw [Definable]; rw [Equiv.exists_congr_left (LEquiv.addEmptyConstants L (∅ : Set M)).onFormula]
  simp

中文:
定理 empty_definable_iff
  证明: by
  rw [Definable]; rw [Equiv.exists_congr_left (LEquiv.addEmptyConstants L (∅ : Set M)).onFormula]
  simp

Depends on / 依赖: Definable, Equiv.exists_congr_left, LEquiv, LEquiv.addEmptyConstants, addEmptyConstants, exists_congr_left, onFormula
-/
theorem empty_definable_iff :
    (∅ : Set M).Definable L s ↔ exists φ : L.Formula α, s = Set.ofPred φ.Realize := by
  rw [Definable]; rw [Equiv.exists_congr_left (LEquiv.addEmptyConstants L (∅ : Set M)).onFormula]
  simp

/--
theorem `definable_iff_empty_definable_with_params` / 定理 `definable_iff_empty_definable_with_params`

English:
theorem definable_iff_empty_definable_with_params
  proof: empty_definable_iff.symm

中文:
定理 definable_iff_empty_definable_with_params
  证明: empty_definable_iff.symm

Depends on / 依赖: empty_definable_iff, empty_definable_iff.symm
-/
theorem definable_iff_empty_definable_with_params :
    A.Definable L s ↔ (∅ : Set M).Definable L[[A]] s :=
  empty_definable_iff.symm

/--
theorem `Definable.mono` / 定理 `Definable.mono`

English:
theorem Definable.mono
  given: (hAs : A.Definable L s) (hAB : A subseteq B)
  statement: B.Definable L s
  proof: by
  rw [definable_iff_empty_definable_with_params] at *
  exact hAs.map_expansion (L.lhomWithConstantsMap (Set.inclusion hAB))

@[simp]

中文:
定理 Definable.mono
  条件: (hAs : A.Definable L s) (hAB : A subseteq B)
  结论: B.Definable L s
  证明: by
  rw [definable_iff_empty_definable_with_params] at *
  exact hAs.map_expansion (L.lhomWithConstantsMap (Set.inclusion hAB))

@[simp]

Depends on / 依赖: L.lhomWithConstantsMap, Set.inclusion, definable_iff_empty_definable_with_params, hAs.map_expansion, inclusion, lhomWithConstantsMap, map_expansion
-/
theorem Definable.mono (hAs : A.Definable L s) (hAB : A subseteq B) : B.Definable L s := by
  rw [definable_iff_empty_definable_with_params] at *
  exact hAs.map_expansion (L.lhomWithConstantsMap (Set.inclusion hAB))

@[simp]
/--
theorem `definable_empty` / 定理 `definable_empty`

English:
theorem definable_empty
  statement: A.Definable L (∅ : Set (α -> M))
  proof: ⟨⊥, by
    ext
    simp⟩

@[simp]

中文:
定理 definable_empty
  结论: A.Definable L (∅ : 集合 (α -> M))
  证明: ⟨⊥, by
    ext
    simp⟩

@[simp]
-/
theorem definable_empty : A.Definable L (∅ : Set (α -> M)) :=
  ⟨⊥, by
    ext
    simp⟩

@[simp]
/--
theorem `definable_univ` / 定理 `definable_univ`

English:
theorem definable_univ
  statement: A.Definable L (univ : Set (α -> M))
  proof: ⟨⊤, by
    ext
    simp⟩

@[simp]

中文:
定理 definable_univ
  结论: A.Definable L (univ : 集合 (α -> M))
  证明: ⟨⊤, by
    ext
    simp⟩

@[simp]
-/
theorem definable_univ : A.Definable L (univ : Set (α -> M)) :=
  ⟨⊤, by
    ext
    simp⟩

@[simp]
/--
theorem `Definable.inter` / 定理 `Definable.inter`

English:
theorem Definable.inter
  given: {f g : Set (α -> M)} (hf : A.Definable L f) (hg : A.Definable L g)
  proof: by
  rcases hf with ⟨φ, rfl⟩
  rcases hg with ⟨θ, rfl⟩
  refine ⟨φ ⊓ θ, ?_⟩
  ext
  simp

@[simp]

中文:
定理 Definable.inter
  条件: {f g : 集合 (α -> M)} (hf : A.Definable L f) (hg : A.Definable L g)
  证明: by
  rcases hf with ⟨φ, rfl⟩
  rcases hg with ⟨θ, rfl⟩
  refine ⟨φ ⊓ θ, ?_⟩
  ext
  simp

@[simp]
-/
theorem Definable.inter {f g : Set (α -> M)} (hf : A.Definable L f) (hg : A.Definable L g) :
    A.Definable L (f inter g) := by
  rcases hf with ⟨φ, rfl⟩
  rcases hg with ⟨θ, rfl⟩
  refine ⟨φ ⊓ θ, ?_⟩
  ext
  simp

@[simp]
/--
theorem `Definable.union` / 定理 `Definable.union`

English:
theorem Definable.union
  given: {f g : Set (α -> M)} (hf : A.Definable L f) (hg : A.Definable L g)
  proof: by
  rcases hf with ⟨φ, hφ⟩
  rcases hg with ⟨θ, hθ⟩
  refine ⟨φ ⊔ θ, ?_⟩
  ext
  rw [hφ]; rw [hθ]; rw [mem_ofPred_eq]; rw [Formula.realize_sup]; rw [mem_union]; rw [mem_ofPred_eq]; rw [mem_ofPred_eq]

中文:
定理 Definable.union
  条件: {f g : 集合 (α -> M)} (hf : A.Definable L f) (hg : A.Definable L g)
  证明: by
  rcases hf with ⟨φ, hφ⟩
  rcases hg with ⟨θ, hθ⟩
  refine ⟨φ ⊔ θ, ?_⟩
  ext
  rw [hφ]; rw [hθ]; rw [mem_ofPred_eq]; rw [Formula.realize_sup]; rw [mem_union]; rw [mem_ofPred_eq]; rw [mem_ofPred_eq]

Depends on / 依赖: Formula, Formula.realize_sup, mem_ofPred_eq, mem_union, realize_sup
-/
theorem Definable.union {f g : Set (α -> M)} (hf : A.Definable L f) (hg : A.Definable L g) :
    A.Definable L (f union g) := by
  rcases hf with ⟨φ, hφ⟩
  rcases hg with ⟨θ, hθ⟩
  refine ⟨φ ⊔ θ, ?_⟩
  ext
  rw [hφ]; rw [hθ]; rw [mem_ofPred_eq]; rw [Formula.realize_sup]; rw [mem_union]; rw [mem_ofPred_eq]; rw [mem_ofPred_eq]

/--
theorem `definable_finset_inf` / 定理 `definable_finset_inf`

English:
theorem definable_finset_inf
  statement: {ι : Type*} {f : ι -> Set (α -> M)} (hf : forall i, A.Definable L (f i))
  proof: by
  classical
    refine Finset.induction definable_univ (fun i s _ h => ?_) s
    rw [Finset.inf_insert]
    exact (hf i).inter h

中文:
定理 definable_finset_inf
  结论: {ι : 类型} {f : ι -> 集合 (α -> M)} (hf : 对任意 i, A.Definable L (f i))
  证明: by
  classical
    refine Finset.induction definable_univ (fun i s _ h => ?_) s
    rw [Finset.inf_insert]
    exact (hf i).inter h

Depends on / 依赖: Finset, Finset.induction, Finset.inf_insert, classical, definable_univ, inf_insert
-/
theorem definable_finset_inf {ι : Type*} {f : ι -> Set (α -> M)} (hf : forall i, A.Definable L (f i))
    (s : Finset ι) : A.Definable L (s.inf f) := by
  classical
    refine Finset.induction definable_univ (fun i s _ h => ?_) s
    rw [Finset.inf_insert]
    exact (hf i).inter h

/--
theorem `definable_finset_sup` / 定理 `definable_finset_sup`

English:
theorem definable_finset_sup
  statement: {ι : Type*} {f : ι -> Set (α -> M)} (hf : forall i, A.Definable L (f i))
  proof: by
  classical
    refine Finset.induction definable_empty (fun i s _ h => ?_) s
    rw [Finset.sup_insert]
    exact (hf i).union h

中文:
定理 definable_finset_sup
  结论: {ι : 类型} {f : ι -> 集合 (α -> M)} (hf : 对任意 i, A.Definable L (f i))
  证明: by
  classical
    refine Finset.induction definable_empty (fun i s _ h => ?_) s
    rw [Finset.sup_insert]
    exact (hf i).union h

Depends on / 依赖: Finset, Finset.induction, Finset.sup_insert, classical, definable_empty, sup_insert
-/
theorem definable_finset_sup {ι : Type*} {f : ι -> Set (α -> M)} (hf : forall i, A.Definable L (f i))
    (s : Finset ι) : A.Definable L (s.sup f) := by
  classical
    refine Finset.induction definable_empty (fun i s _ h => ?_) s
    rw [Finset.sup_insert]
    exact (hf i).union h

/--
theorem `definable_biInter_finset` / 定理 `definable_biInter_finset`

English:
theorem definable_biInter_finset
  statement: {ι : Type*} {f : ι -> Set (α -> M)}
  proof: by
  rw [← Finset.inf_set_eq_iInter]
  exact definable_finset_inf hf s

中文:
定理 definable_bi整数er_finset
  结论: {ι : 类型} {f : ι -> 集合 (α -> M)}
  证明: by
  rw [← Finset.inf_set_eq_iInter]
  exact definable_finset_inf hf s

Depends on / 依赖: Finset, Finset.inf_set_eq_iInter, definable_finset_inf, inf_set_eq_iInter
-/
theorem definable_biInter_finset {ι : Type*} {f : ι -> Set (α -> M)}
    (hf : forall i, A.Definable L (f i)) (s : Finset ι) : A.Definable L (⋂ i in s, f i) := by
  rw [← Finset.inf_set_eq_iInter]
  exact definable_finset_inf hf s

/--
theorem `definable_biUnion_finset` / 定理 `definable_biUnion_finset`

English:
theorem definable_biUnion_finset
  statement: {ι : Type*} {f : ι -> Set (α -> M)}
  proof: by
  rw [← Finset.sup_set_eq_biUnion]
  exact definable_finset_sup hf s

中文:
定理 definable_biUnion_finset
  结论: {ι : 类型} {f : ι -> 集合 (α -> M)}
  证明: by
  rw [← Finset.sup_set_eq_biUnion]
  exact definable_finset_sup hf s

Depends on / 依赖: Finset, Finset.sup_set_eq_biUnion, definable_finset_sup, sup_set_eq_biUnion
-/
theorem definable_biUnion_finset {ι : Type*} {f : ι -> Set (α -> M)}
    (hf : forall i, A.Definable L (f i)) (s : Finset ι) : A.Definable L (⋃ i in s, f i) := by
  rw [← Finset.sup_set_eq_biUnion]
  exact definable_finset_sup hf s

/--
theorem `definable_iInter_of_finite` / 定理 `definable_iInter_of_finite`

English:
theorem definable_iInter_of_finite
  statement: {ι : Type*} [Finite ι] {f : ι -> Set (α -> M)}
  proof: by
  have := Fintype.ofFinite ι
  convert! definable_finset_inf hf Finset.univ using 1
  simp

中文:
定理 definable_i整数er_of_finite
  结论: {ι : 类型} [有限 ι] {f : ι -> 集合 (α -> M)}
  证明: by
  have := Fintype.ofFinite ι
  convert! definable_finset_inf hf Finset.univ using 1
  simp

Depends on / 依赖: Finset, Finset.univ, Fintype, Fintype.ofFinite, convert, definable_finset_inf, ofFinite
-/
theorem definable_iInter_of_finite {ι : Type*} [Finite ι] {f : ι -> Set (α -> M)}
    (hf : forall i, A.Definable L (f i)) : A.Definable L (⋂ i, f i) := by
  have := Fintype.ofFinite ι
  convert! definable_finset_inf hf Finset.univ using 1
  simp

/--
theorem `definable_iUnion_of_finite` / 定理 `definable_iUnion_of_finite`

English:
theorem definable_iUnion_of_finite
  statement: {ι : Type*} [Finite ι] {f : ι -> Set (α -> M)}
  proof: by
  have := Fintype.ofFinite ι
  convert! definable_finset_sup hf Finset.univ using 1
  simp

@[simp]

中文:
定理 definable_iUnion_of_finite
  结论: {ι : 类型} [有限 ι] {f : ι -> 集合 (α -> M)}
  证明: by
  have := Fintype.ofFinite ι
  convert! definable_finset_sup hf Finset.univ using 1
  simp

@[simp]

Depends on / 依赖: Finset, Finset.univ, Fintype, Fintype.ofFinite, convert, definable_finset_sup, ofFinite
-/
theorem definable_iUnion_of_finite {ι : Type*} [Finite ι] {f : ι -> Set (α -> M)}
    (hf : forall i, A.Definable L (f i)) : A.Definable L (⋃ i, f i) := by
  have := Fintype.ofFinite ι
  convert! definable_finset_sup hf Finset.univ using 1
  simp

@[simp]
/--
theorem `Definable.compl` / 定理 `Definable.compl`

English:
theorem Definable.compl
  given: {s : Set (α -> M)} (hf : A.Definable L s)
  statement: A.Definable L sᶜ
  proof: by
  rcases hf with ⟨φ, hφ⟩
  refine ⟨φ.not, ?_⟩
  ext v
  rw [hφ]; rw [compl_ofPred]; rw [mem_ofPred]; rw [mem_ofPred]; rw [Formula.realize_not]

@[simp]

中文:
定理 Definable.compl
  条件: {s : 集合 (α -> M)} (hf : A.Definable L s)
  结论: A.Definable L sᶜ
  证明: by
  rcases hf with ⟨φ, hφ⟩
  refine ⟨φ.not, ?_⟩
  ext v
  rw [hφ]; rw [compl_ofPred]; rw [mem_ofPred]; rw [mem_ofPred]; rw [Formula.realize_not]

@[simp]

Depends on / 依赖: Formula, Formula.realize_not, compl_ofPred, mem_ofPred, realize_not
-/
theorem Definable.compl {s : Set (α -> M)} (hf : A.Definable L s) : A.Definable L sᶜ := by
  rcases hf with ⟨φ, hφ⟩
  refine ⟨φ.not, ?_⟩
  ext v
  rw [hφ]; rw [compl_ofPred]; rw [mem_ofPred]; rw [mem_ofPred]; rw [Formula.realize_not]

@[simp]
/--
theorem `Definable.sdiff` / 定理 `Definable.sdiff`

English:
theorem Definable.sdiff
  given: {s t : Set (α -> M)} (hs : A.Definable L s) (ht : A.Definable L t)
  proof: hs.inter ht.compl

中文:
定理 Definable.sdiff
  条件: {s t : 集合 (α -> M)} (hs : A.Definable L s) (ht : A.Definable L t)
  证明: hs.inter ht.compl

Depends on / 依赖: hs.inter, ht.compl
-/
theorem Definable.sdiff {s t : Set (α -> M)} (hs : A.Definable L s) (ht : A.Definable L t) :
    A.Definable L (s \ t) :=
  hs.inter ht.compl

/--
lemma `Definable.himp` / 引理 `Definable.himp`

English:
lemma Definable.himp
  given: {s t : Set (α -> M)} (hs : A.Definable L s) (ht : A.Definable L t)
  proof: by rw [himp_eq]; exact ht.union hs.compl

中文:
引理 Definable.himp
  条件: {s t : 集合 (α -> M)} (hs : A.Definable L s) (ht : A.Definable L t)
  证明: by rw [himp_eq]; exact ht.union hs.compl
-/
@[simp] lemma Definable.himp {s t : Set (α -> M)} (hs : A.Definable L s) (ht : A.Definable L t) :
    A.Definable L (s ⇨ t) := by rw [himp_eq]; exact ht.union hs.compl

/--
theorem `Definable.preimage_comp` / 定理 `Definable.preimage_comp`

English:
theorem Definable.preimage_comp
  given: (f : α -> β) {s : Set (α -> M)} (h : A.Definable L s)
  proof: by
  obtain ⟨φ, rfl⟩ := h
  refine ⟨φ.relabel f, ?_⟩
  ext
  simp only [Set.preimage_ofPred_eq, mem_ofPred_eq, Formula.realize_relabel]

中文:
定理 Definable.preimage_comp
  条件: (f : α -> β) {s : 集合 (α -> M)} (h : A.Definable L s)
  证明: by
  obtain ⟨φ, rfl⟩ := h
  refine ⟨φ.relabel f, ?_⟩
  ext
  simp only [Set.preimage_ofPred_eq, mem_ofPred_eq, Formula.realize_relabel]

Depends on / 依赖: Formula, Formula.realize_relabel, Set.preimage_ofPred_eq, mem_ofPred_eq, preimage_ofPred_eq, realize_relabel, relabel
-/
theorem Definable.preimage_comp (f : α -> β) {s : Set (α -> M)} (h : A.Definable L s) :
    A.Definable L ((fun g : β -> M => g ∘ f) ⁻¹' s) := by
  obtain ⟨φ, rfl⟩ := h
  refine ⟨φ.relabel f, ?_⟩
  ext
  simp only [Set.preimage_ofPred_eq, mem_ofPred_eq, Formula.realize_relabel]

/--
theorem `Definable.image_comp_equiv` / 定理 `Definable.image_comp_equiv`

English:
theorem Definable.image_comp_equiv
  given: {s : Set (β -> M)} (h : A.Definable L s) (f : α ≃ β)
  proof: by
  refine (congr rfl ?_).mp (h.preimage_comp f.symm)
  rw [image_eq_preimage_of_inverse]
  · intro i
    ext b
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  · intro i
    ext a
    simp

中文:
定理 Definable.image_comp_equiv
  条件: {s : 集合 (β -> M)} (h : A.Definable L s) (f : α ≃ β)
  证明: by
  refine (congr rfl ?_).mp (h.preimage_comp f.symm)
  rw [image_eq_preimage_of_inverse]
  · intro i
    ext b
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  · intro i
    ext a
    simp

Depends on / 依赖: Equiv.apply_symm_apply, Function, Function.comp_apply, apply_symm_apply, comp_apply, f.symm, h.preimage_comp, image_eq_preimage_of_inverse, preimage_comp
-/
theorem Definable.image_comp_equiv {s : Set (β -> M)} (h : A.Definable L s) (f : α ≃ β) :
    A.Definable L ((fun g : β -> M => g ∘ f) '' s) := by
  refine (congr rfl ?_).mp (h.preimage_comp f.symm)
  rw [image_eq_preimage_of_inverse]
  · intro i
    ext b
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  · intro i
    ext a
    simp

/--
theorem `definable_iff_finitely_definable` / 定理 `definable_iff_finitely_definable`

English:
theorem definable_iff_finitely_definable
  proof: by
  classical
  constructor
  · simp only [definable_iff_exists_formula_sum]
    rintro ⟨φ, rfl⟩
    let A0 := (φ.freeVarFinset.toLeft).image Subtype.val
    refine ⟨A0, by simp [A0], (φ.restrictFreeVar <| fun x => Sum.casesOn x.1
        (fun x hx => Sum.inl ⟨x, by simp [A0, hx]⟩) (fun x _ => Sum.inr x) x.2), ?_⟩
    ext
    simp only [Formula.Realize, mem_ofPred_eq, Finset.coe_sort_coe]
exact iff_comm.1 BoundedFormula.realize_restrictFreeVar _ (by simp)
  · rintro ⟨A0, hA0, hd⟩
    exact Definable.mono hd hA0

中文:
定理 definable_iff_finitely_definable
  证明: by
  classical
  constructor
  · simp only [definable_iff_exists_formula_sum]
    rintro ⟨φ, rfl⟩
    let A0 := (φ.freeVarFinset.toLeft).image Subtype.val
    refine ⟨A0, by simp [A0], (φ.restrictFreeVar <| fun x => Sum.casesOn x.1
        (fun x hx => Sum.inl ⟨x, by simp [A0, hx]⟩) (fun x _ => Sum.inr x) x.2), ?_⟩
    ext
    simp only [Formula.Realize, mem_ofPred_eq, Finset.coe_sort_coe]
exact iff_comm.1 BoundedFormula.realize_restrictFreeVar _ (by simp)
  · rintro ⟨A0, hA0, hd⟩
    exact Definable.mono hd hA0

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_restrictFreeVar, Definable, Definable.mono, Finset, Finset.coe_sort_coe, Formula, Formula.Realize, Realize, Subtype, Subtype.val, Sum.casesOn, Sum.inl, Sum.inr, casesOn, classical, coe_sort_coe, definable_iff_exists_formula_sum, freeVarFinset, freeVarFinset.toLeft
-/
theorem definable_iff_finitely_definable :
    A.Definable L s ↔ exists (A0 : Finset M), (A0 : Set M) subseteq A ∧
      (A0 : Set M).Definable L s := by
  classical
  constructor
  · simp only [definable_iff_exists_formula_sum]
    rintro ⟨φ, rfl⟩
    let A0 := (φ.freeVarFinset.toLeft).image Subtype.val
    refine ⟨A0, by simp [A0], (φ.restrictFreeVar <| fun x => Sum.casesOn x.1
        (fun x hx => Sum.inl ⟨x, by simp [A0, hx]⟩) (fun x _ => Sum.inr x) x.2), ?_⟩
    ext
    simp only [Formula.Realize, mem_ofPred_eq, Finset.coe_sort_coe]
exact iff_comm.1 BoundedFormula.realize_restrictFreeVar _ (by simp)
  · rintro ⟨A0, hA0, hd⟩
    exact Definable.mono hd hA0

/--
theorem `Definable.image_comp_sumInl_fin` / 定理 `Definable.image_comp_sumInl_fin`

English:
theorem Definable.image_comp_sumInl_fin
  statement: (m : Nat) {s : Set (Sum α (Fin m) -> M)}
  proof: by
  obtain ⟨φ, rfl⟩ := h
  refine ⟨(BoundedFormula.relabel id φ).exs, ?_⟩
  ext x
  simp only [Set.mem_image, mem_ofPred_eq, BoundedFormula.realize_exs,
    BoundedFormula.realize_relabel, Function.comp_id, Fin.castAdd_zero, Fin.cast_refl]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact
      ⟨y ∘ Sum.inr, (congr (congr rfl (Sum.elim_comp_inl_inr y).symm) (funext finZeroElim)).mp hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨Sum.elim x y, (congr rfl (funext finZeroElim)).mp hy, Sum.elim_comp_inl _ _⟩

中文:
定理 Definable.image_comp_sumInl_fin
  结论: (m : 自然数) {s : 集合 (和 α (有限集 m) -> M)}
  证明: by
  obtain ⟨φ, rfl⟩ := h
  refine ⟨(BoundedFormula.relabel id φ).exs, ?_⟩
  ext x
  simp only [Set.mem_image, mem_ofPred_eq, BoundedFormula.realize_exs,
    BoundedFormula.realize_relabel, Function.comp_id, Fin.castAdd_zero, Fin.cast_refl]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact
      ⟨y ∘ Sum.inr, (congr (congr rfl (Sum.elim_comp_inl_inr y).symm) (funext finZeroElim)).mp hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨Sum.elim x y, (congr rfl (funext finZeroElim)).mp hy, Sum.elim_comp_inl _ _⟩

Depends on / 依赖: BoundedFormula, BoundedFormula.realize_exs, BoundedFormula.realize_relabel, BoundedFormula.relabel, Fin.castAdd_zero, Fin.cast_refl, Function, Function.comp_id, Set.mem_image, Sum.elim, Sum.elim_comp_inl, Sum.elim_comp_inl_inr, Sum.inr, castAdd_zero, cast_refl, comp_id, elim_comp_inl, elim_comp_inl_inr, finZeroElim, mem_image
-/
theorem Definable.image_comp_sumInl_fin (m : Nat) {s : Set (Sum α (Fin m) -> M)}
    (h : A.Definable L s) : A.Definable L ((fun g : Sum α (Fin m) -> M => g ∘ Sum.inl) '' s) := by
  obtain ⟨φ, rfl⟩ := h
  refine ⟨(BoundedFormula.relabel id φ).exs, ?_⟩
  ext x
  simp only [Set.mem_image, mem_ofPred_eq, BoundedFormula.realize_exs,
    BoundedFormula.realize_relabel, Function.comp_id, Fin.castAdd_zero, Fin.cast_refl]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact
      ⟨y ∘ Sum.inr, (congr (congr rfl (Sum.elim_comp_inl_inr y).symm) (funext finZeroElim)).mp hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨Sum.elim x y, (congr rfl (funext finZeroElim)).mp hy, Sum.elim_comp_inl _ _⟩

/--
theorem `Definable.image_comp_embedding` / 定理 `Definable.image_comp_embedding`

English:
theorem Definable.image_comp_embedding
  statement: {s : Set (β -> M)} (h : A.Definable L s) (f : α ↪ β)
  proof: by
  classical
    cases nonempty_fintype β
    refine
      (congr rfl (ext fun x => ?_)).mp
        (((h.image_comp_equiv (Equiv.Set.sumCompl (range f))).image_comp_equiv
              (Equiv.sumCongr (Equiv.ofInjective f f.injective)
                (Fintype.equivFin (↥(range f)ᶜ)).symm)).image_comp_sumInl_fin
          _)
    simp only [mem_image, exists_exists_and_eq_and]
    refine exists_congr fun y => and_congr_right fun _ => Eq.congr_left (funext fun a => ?_)
    simp

中文:
定理 Definable.image_comp_embedding
  结论: {s : 集合 (β -> M)} (h : A.Definable L s) (f : α ↪ β)
  证明: by
  classical
    cases nonempty_fintype β
    refine
      (congr rfl (ext fun x => ?_)).mp
        (((h.image_comp_equiv (Equiv.Set.sumCompl (range f))).image_comp_equiv
              (Equiv.sumCongr (Equiv.ofInjective f f.injective)
                (Fintype.equivFin (↥(range f)ᶜ)).symm)).image_comp_sumInl_fin
          _)
    simp only [mem_image, exists_exists_and_eq_and]
    refine exists_congr fun y => and_congr_right fun _ => Eq.congr_left (funext fun a => ?_)
    simp

Depends on / 依赖: Eq.congr_left, Equiv.Set.sumCompl, Equiv.ofInjective, Equiv.sumCongr, Fintype, Fintype.equivFin, and_congr_right, classical, congr_left, equivFin, exists_congr, exists_exists_and_eq_and, f.injective, h.image_comp_equiv, image_comp_equiv, image_comp_sumInl_fin, injective, mem_image, nonempty_fintype, ofInjective
-/
theorem Definable.image_comp_embedding {s : Set (β -> M)} (h : A.Definable L s) (f : α ↪ β)
    [Finite β] : A.Definable L ((fun g : β -> M => g ∘ f) '' s) := by
  classical
    cases nonempty_fintype β
    refine
      (congr rfl (ext fun x => ?_)).mp
        (((h.image_comp_equiv (Equiv.Set.sumCompl (range f))).image_comp_equiv
              (Equiv.sumCongr (Equiv.ofInjective f f.injective)
                (Fintype.equivFin (↥(range f)ᶜ)).symm)).image_comp_sumInl_fin
          _)
    simp only [mem_image, exists_exists_and_eq_and]
    refine exists_congr fun y => and_congr_right fun _ => Eq.congr_left (funext fun a => ?_)
    simp

/--
theorem `Definable.image_comp` / 定理 `Definable.image_comp`

English:
theorem Definable.image_comp
  statement: {s : Set (β -> M)} (h : A.Definable L s) (f : α -> β) [Finite α]
  proof: by
  classical
    cases nonempty_fintype α
    cases nonempty_fintype β
    have h :=
      (((h.image_comp_equiv (Equiv.Set.sumCompl (range f))).image_comp_equiv
                (Equiv.sumCongr (_root_.Equiv.refl _)
                  (Fintype.equivFin _).symm)).image_comp_sumInl_fin
            _).preimage_comp
        (rangeSplitting f)
    have h' :
      A.Definable L { x : α -> M | forall a, x a = x (rangeSplitting f (rangeFactorization f a)) } := by
      have h' : forall a,
        A.Definable L { x : α -> M | x a = x (rangeSplitting f (rangeFactorization f a)) } := by
          refine fun a => ⟨(var a).equal (var (rangeSplitting f (rangeFactorization f a))), ext ?_⟩
          simp
      refine (congr rfl (ext ?_)).mp (definable_biInter_finset h' Finset.univ)
      simp
    refine (congr rfl (ext fun x => ?_)).mp (h.inter h')
    simp only [mem_inter_iff, mem_preimage, mem_image, exists_exists_and_eq_and,
      mem_ofPred_eq]
    constructor
    · rintro ⟨⟨y, ys, hy⟩, hx⟩
      refine ⟨y, ys, ?_⟩
      ext a
      rw [hx a]; rw [← Function.comp_apply (f := x)]; rw [← hy]
      simp
    · rintro ⟨y, ys, rfl⟩
      refine ⟨⟨y, ys, ?_⟩, fun a => ?_⟩
      · ext
        simp [Set.apply_rangeSplitting f]
      · rw [Function.comp_apply, Function.comp_apply, apply_rangeSplitting f,
          rangeFactorization_coe]

中文:
定理 Definable.image_comp
  结论: {s : 集合 (β -> M)} (h : A.Definable L s) (f : α -> β) [有限 α]
  证明: by
  classical
    cases nonempty_fintype α
    cases nonempty_fintype β
    have h :=
      (((h.image_comp_equiv (Equiv.Set.sumCompl (range f))).image_comp_equiv
                (Equiv.sumCongr (_root_.Equiv.refl _)
                  (Fintype.equivFin _).symm)).image_comp_sumInl_fin
            _).preimage_comp
        (rangeSplitting f)
    have h' :
      A.Definable L { x : α -> M | forall a, x a = x (rangeSplitting f (rangeFactorization f a)) } := by
      have h' : forall a,
        A.Definable L { x : α -> M | x a = x (rangeSplitting f (rangeFactorization f a)) } := by
          refine fun a => ⟨(var a).equal (var (rangeSplitting f (rangeFactorization f a))), ext ?_⟩
          simp
      refine (congr rfl (ext ?_)).mp (definable_biInter_finset h' Finset.univ)
      simp
    refine (congr rfl (ext fun x => ?_)).mp (h.inter h')
    simp only [mem_inter_iff, mem_preimage, mem_image, exists_exists_and_eq_and,
      mem_ofPred_eq]
    constructor
    · rintro ⟨⟨y, ys, hy⟩, hx⟩
      refine ⟨y, ys, ?_⟩
      ext a
      rw [hx a]; rw [← Function.comp_apply (f := x)]; rw [← hy]
      simp
    · rintro ⟨y, ys, rfl⟩
      refine ⟨⟨y, ys, ?_⟩, fun a => ?_⟩
      · ext
        simp [Set.apply_rangeSplitting f]
      · rw [Function.comp_apply, Function.comp_apply, apply_rangeSplitting f,
          rangeFactorization_coe]

Depends on / 依赖: A.Definable, Definable, Equiv.Set.sumCompl, Equiv.sumCongr, Fintype, Fintype.equivFin, _root_, _root_.Equiv.refl, classical, equivFin, h.image_comp_equiv, image_comp_equiv, image_comp_sumInl_fin, nonempty_fintype, preimage_comp, rangeFactorization, rangeSplitting, sumCompl, sumCongr
-/
theorem Definable.image_comp {s : Set (β -> M)} (h : A.Definable L s) (f : α -> β) [Finite α]
    [Finite β] : A.Definable L ((fun g : β -> M => g ∘ f) '' s) := by
  classical
    cases nonempty_fintype α
    cases nonempty_fintype β
    have h :=
      (((h.image_comp_equiv (Equiv.Set.sumCompl (range f))).image_comp_equiv
                (Equiv.sumCongr (_root_.Equiv.refl _)
                  (Fintype.equivFin _).symm)).image_comp_sumInl_fin
            _).preimage_comp
        (rangeSplitting f)
    have h' :
      A.Definable L { x : α -> M | forall a, x a = x (rangeSplitting f (rangeFactorization f a)) } := by
      have h' : forall a,
        A.Definable L { x : α -> M | x a = x (rangeSplitting f (rangeFactorization f a)) } := by
          refine fun a => ⟨(var a).equal (var (rangeSplitting f (rangeFactorization f a))), ext ?_⟩
          simp
      refine (congr rfl (ext ?_)).mp (definable_biInter_finset h' Finset.univ)
      simp
    refine (congr rfl (ext fun x => ?_)).mp (h.inter h')
    simp only [mem_inter_iff, mem_preimage, mem_image, exists_exists_and_eq_and,
      mem_ofPred_eq]
    constructor
    · rintro ⟨⟨y, ys, hy⟩, hx⟩
      refine ⟨y, ys, ?_⟩
      ext a
      rw [hx a]; rw [← Function.comp_apply (f := x)]; rw [← hy]
      simp
    · rintro ⟨y, ys, rfl⟩
      refine ⟨⟨y, ys, ?_⟩, fun a => ?_⟩
      · ext
        simp [Set.apply_rangeSplitting f]
      · rw [Function.comp_apply, Function.comp_apply, apply_rangeSplitting f,
          rangeFactorization_coe]

/--
lemma `Definable.exists_of_finite` / 引理 `Definable.exists_of_finite`

English:
lemma Definable.exists_of_finite
  statement: [Finite β] {S : Set ((α oplus β) -> M)}
  proof: by
  obtain ⟨φ, hφ⟩ := hS
  exists φ.iExs β
  ext v
  simp [hφ]

中文:
引理 Definable.存在_of_finite
  结论: [有限 β] {S : 集合 ((α oplus β) -> M)}
  证明: by
  obtain ⟨φ, hφ⟩ := hS
  exists φ.iExs β
  ext v
  simp [hφ]
-/
lemma Definable.exists_of_finite [Finite β] {S : Set ((α oplus β) -> M)}
    (hS : A.Definable L S) :
    A.Definable L { v : α -> M | exists u : β -> M, Sum.elim v u in S } := by
  obtain ⟨φ, hφ⟩ := hS
  exists φ.iExs β
  ext v
  simp [hφ]

/--
lemma `Definable.forall_of_finite` / 引理 `Definable.forall_of_finite`

English:
lemma Definable.forall_of_finite
  statement: [Finite β] {S : Set ((α oplus β) -> M)}
  proof: by
  obtain ⟨φ, hφ⟩ := hS
  exists φ.iAlls β
  ext v
  simp [hφ]

中文:
引理 Definable.对任意_of_finite
  结论: [有限 β] {S : 集合 ((α oplus β) -> M)}
  证明: by
  obtain ⟨φ, hφ⟩ := hS
  exists φ.iAlls β
  ext v
  simp [hφ]
-/
lemma Definable.forall_of_finite [Finite β] {S : Set ((α oplus β) -> M)}
    (hS : A.Definable L S) :
    A.Definable L { v : α -> M | forall u : β -> M, Sum.elim v u in S } := by
  obtain ⟨φ, hφ⟩ := hS
  exists φ.iAlls β
  ext v
  simp [hφ]

variable (L A)

/--
Definition of `Definable₁` / `Definable₁` 的定义

English:
definition Definable₁
  signature: (s : Set M)
  body: A.Definable L { x : Fin 1 -> M | x 0 in s }

中文:
定义 Definable₁
  签名: (s : 集合 M)
  定义体: A.Definable L { x : Fin 1 -> M | x 0 in s }

Depends on / 依赖: A.Definable, Definable
-/
def Definable₁ (s : Set M) : Prop :=
  A.Definable L { x : Fin 1 -> M | x 0 in s }

/--
Definition of `Definable₂` / `Definable₂` 的定义

English:
definition Definable₂
  signature: (s : Set (M × M))
  body: A.Definable L { x : Fin 2 -> M | (x 0, x 1) in s }

中文:
定义 Definable₂
  签名: (s : 集合 (M × M))
  定义体: A.Definable L { x : Fin 2 -> M | (x 0, x 1) in s }

Depends on / 依赖: A.Definable, Definable
-/
def Definable₂ (s : Set (M × M)) : Prop :=
  A.Definable L { x : Fin 2 -> M | (x 0, x 1) in s }

/--
theorem `Definable.singleton` / 定理 `Definable.singleton`

English:
theorem Definable.singleton
  given: (a : M)
  proof: by
  exists (Term.var 0).equal (L.con (⟨a, rfl⟩ : ↑({a} : Set M))).term

中文:
定理 Definable.singleton
  条件: (a : M)
  证明: by
  exists (Term.var 0).equal (L.con (⟨a, rfl⟩ : ↑({a} : Set M))).term

Depends on / 依赖: L.con, Term.var
-/
theorem Definable.singleton (a : M) :
    ({a} : Set M).Definable₁ L {a} := by
  exists (Term.var 0).equal (L.con (⟨a, rfl⟩ : ↑({a} : Set M))).term

/--
theorem `Definable.singleton_of_mem` / 定理 `Definable.singleton_of_mem`

English:
theorem Definable.singleton_of_mem
  given: {a : M} {A : Set M} (ha : a in A)
  proof: (Definable.singleton L a).mono (Set.singleton_subset_iff.mpr ha)

中文:
定理 Definable.singleton_of_mem
  条件: {a : M} {A : 集合 M} (ha : a in A)
  证明: (Definable.singleton L a).mono (Set.singleton_subset_iff.mpr ha)

Depends on / 依赖: Definable, Definable.singleton, Set.singleton_subset_iff.mpr, singleton, singleton_subset_iff
-/
theorem Definable.singleton_of_mem {a : M} {A : Set M} (ha : a in A) :
    A.Definable₁ L {a} :=
  (Definable.singleton L a).mono (Set.singleton_subset_iff.mpr ha)

/--
theorem `Definable.diagonal` / 定理 `Definable.diagonal`

English:
theorem Definable.diagonal
  given: (A : Set M)
  proof: by
  exists (Term.var 0).equal (Term.var 1)

中文:
定理 Definable.diagonal
  条件: (A : 集合 M)
  证明: by
  exists (Term.var 0).equal (Term.var 1)

Depends on / 依赖: Term.var
-/
theorem Definable.diagonal (A : Set M) :
    A.Definable₂ L (diagonal M) := by
  exists (Term.var 0).equal (Term.var 1)

end Set

namespace FirstOrder

namespace Language

open Set

variable (L : FirstOrder.Language.{u, v}) {M : Type w} [L.Structure M] (A : Set M) (α : Type u₁)

/--
Definition of `DefinableSet` / `DefinableSet` 的定义

English:
definition DefinableSet
  body: { s : Set (α -> M) // A.Definable L s }

中文:
定义 DefinableSet
  定义体: { s : Set (α -> M) // A.Definable L s }

Depends on / 依赖: A.Definable, Definable
-/
def DefinableSet :=
  { s : Set (α -> M) // A.Definable L s }

namespace DefinableSet

variable {L A α}
variable {s t : L.DefinableSet A α} {x : α -> M}

/--
Instance `instSetLike` / 实例 `instSetLike`

English:
instance instSetLike
  signature: : SetLike (L.DefinableSet A α) (α -> M) where
  body: Subtype.val
  coe_injective := Subtype.val_injective

中文:
实例 instSetLike
  签名: : 集合状 (L.DefinableSet A α) (α -> M) where
  定义体: Subtype.val
  coe_injective := Subtype.val_injective

Depends on / 依赖: Subtype, Subtype.val
-/
instance instSetLike : SetLike (L.DefinableSet A α) (α -> M) where
  coe := Subtype.val
  coe_injective := Subtype.val_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (L.DefinableSet A α)
  body: .ofSetLike (L.DefinableSet A α) (α -> M)

中文:
实例 :
  签名: 偏序 (L.DefinableSet A α)
  定义体: .ofSetLike (L.DefinableSet A α) (α -> M)

Depends on / 依赖: DefinableSet, L.DefinableSet, ofSetLike
-/
instance : PartialOrder (L.DefinableSet A α) := .ofSetLike (L.DefinableSet A α) (α -> M)

/--
Instance `instTop` / 实例 `instTop`

English:
instance instTop
  signature: : Top (L.DefinableSet A α)
  body: ⟨⟨⊤, definable_univ⟩⟩

中文:
实例 instTop
  签名: : 顶元素 (L.DefinableSet A α)
  定义体: ⟨⟨⊤, definable_univ⟩⟩

Depends on / 依赖: definable_univ
-/
instance instTop : Top (L.DefinableSet A α) :=
  ⟨⟨⊤, definable_univ⟩⟩

/--
Instance `instBot` / 实例 `instBot`

English:
instance instBot
  signature: : Bot (L.DefinableSet A α)
  body: ⟨⟨⊥, definable_empty⟩⟩

中文:
实例 instBot
  签名: : 底元素 (L.DefinableSet A α)
  定义体: ⟨⟨⊥, definable_empty⟩⟩

Depends on / 依赖: definable_empty
-/
instance instBot : Bot (L.DefinableSet A α) :=
  ⟨⟨⊥, definable_empty⟩⟩

/--
Instance `instSup` / 实例 `instSup`

English:
instance instSup
  signature: : Max (L.DefinableSet A α)
  body: ⟨fun s t => ⟨s union t, s.2.union t.2⟩⟩

中文:
实例 instSup
  签名: : 最大值 (L.DefinableSet A α)
  定义体: ⟨fun s t => ⟨s union t, s.2.union t.2⟩⟩
-/
instance instSup : Max (L.DefinableSet A α) :=
  ⟨fun s t => ⟨s union t, s.2.union t.2⟩⟩

/--
Instance `instInf` / 实例 `instInf`

English:
instance instInf
  signature: : Min (L.DefinableSet A α)
  body: ⟨fun s t => ⟨s inter t, s.2.inter t.2⟩⟩

中文:
实例 instInf
  签名: : 最小值 (L.DefinableSet A α)
  定义体: ⟨fun s t => ⟨s inter t, s.2.inter t.2⟩⟩
-/
instance instInf : Min (L.DefinableSet A α) :=
  ⟨fun s t => ⟨s inter t, s.2.inter t.2⟩⟩

/--
Instance `instCompl` / 实例 `instCompl`

English:
instance instCompl
  signature: : Compl (L.DefinableSet A α)
  body: ⟨fun s => ⟨sᶜ, s.2.compl⟩⟩

中文:
实例 instCompl
  签名: : 补集 (L.DefinableSet A α)
  定义体: ⟨fun s => ⟨sᶜ, s.2.compl⟩⟩
-/
instance instCompl : Compl (L.DefinableSet A α) :=
  ⟨fun s => ⟨sᶜ, s.2.compl⟩⟩

/--
Instance `instSDiff` / 实例 `instSDiff`

English:
instance instSDiff
  signature: : SDiff (L.DefinableSet A α)
  body: ⟨fun s t => ⟨s \ t, s.2.sdiff t.2⟩⟩

中文:
实例 instSDiff
  签名: : 对称差 (L.DefinableSet A α)
  定义体: ⟨fun s t => ⟨s \ t, s.2.sdiff t.2⟩⟩
-/
instance instSDiff : SDiff (L.DefinableSet A α) :=
  ⟨fun s t => ⟨s \ t, s.2.sdiff t.2⟩⟩

-- Why does it complain that `s ⇨ t` is noncomputable?
/--
Instance `instHImp` / 实例 `instHImp`

English:
instance instHImp
  signature: : HImp (L.DefinableSet A α) where
  body: ⟨s ⇨ t, s.2.himp t.2⟩

中文:
实例 instHImp
  签名: : HImp (L.DefinableSet A α) where
  定义体: ⟨s ⇨ t, s.2.himp t.2⟩
-/
noncomputable instance instHImp : HImp (L.DefinableSet A α) where
  himp s t := ⟨s ⇨ t, s.2.himp t.2⟩

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited (L.DefinableSet A α)
  body: ⟨⊥⟩

中文:
实例 instInhabited
  签名: : 可居 (L.DefinableSet A α)
  定义体: ⟨⊥⟩
-/
instance instInhabited : Inhabited (L.DefinableSet A α) :=
  ⟨⊥⟩

/--
theorem `le_iff` / 定理 `le_iff`

English:
theorem le_iff
  statement: s <= t ↔ (s : Set (α -> M)) <= (t : Set (α -> M))
  proof: Iff.rfl

@[simp]

中文:
定理 le_iff
  结论: s <= t ↔ (s : 集合 (α -> M)) <= (t : 集合 (α -> M))
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem le_iff : s <= t ↔ (s : Set (α -> M)) <= (t : Set (α -> M)) :=
  Iff.rfl

@[simp]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  statement: x in (⊤ : L.DefinableSet A α)
  proof: mem_univ x

@[simp]

中文:
定理 mem_top
  结论: x in (⊤ : L.DefinableSet A α)
  证明: mem_univ x

@[simp]

Depends on / 依赖: mem_univ
-/
theorem mem_top : x in (⊤ : L.DefinableSet A α) :=
  mem_univ x

@[simp]
/--
theorem `notMem_bot` / 定理 `notMem_bot`

English:
theorem notMem_bot
  given: {x : α -> M}
  statement: x ∉ (⊥ : L.DefinableSet A α)
  proof: notMem_empty x

@[simp]

中文:
定理 notMem_bot
  条件: {x : α -> M}
  结论: x ∉ (⊥ : L.DefinableSet A α)
  证明: notMem_empty x

@[simp]

Depends on / 依赖: notMem_empty
-/
theorem notMem_bot {x : α -> M} : x ∉ (⊥ : L.DefinableSet A α) :=
  notMem_empty x

@[simp]
/--
theorem `mem_sup` / 定理 `mem_sup`

English:
theorem mem_sup
  statement: x in s ⊔ t ↔ x in s ∨ x in t
  proof: Iff.rfl

@[simp]

中文:
定理 mem_sup
  结论: x in s ⊔ t ↔ x in s ∨ x in t
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_sup : x in s ⊔ t ↔ x in s ∨ x in t :=
  Iff.rfl

@[simp]
/--
theorem `mem_inf` / 定理 `mem_inf`

English:
theorem mem_inf
  statement: x in s ⊓ t ↔ x in s ∧ x in t
  proof: Iff.rfl

@[simp]

中文:
定理 mem_inf
  结论: x in s ⊓ t ↔ x in s ∧ x in t
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_inf : x in s ⊓ t ↔ x in s ∧ x in t :=
  Iff.rfl

@[simp]
/--
theorem `mem_compl` / 定理 `mem_compl`

English:
theorem mem_compl
  statement: x in sᶜ ↔ x ∉ s
  proof: Iff.rfl

@[simp]

中文:
定理 mem_compl
  结论: x in sᶜ ↔ x ∉ s
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_compl : x in sᶜ ↔ x ∉ s :=
  Iff.rfl

@[simp]
/--
theorem `mem_sdiff` / 定理 `mem_sdiff`

English:
theorem mem_sdiff
  statement: x in s \ t ↔ x in s ∧ x ∉ t
  proof: Iff.rfl

@[simp, norm_cast]

中文:
定理 mem_sdiff
  结论: x in s \ t ↔ x in s ∧ x ∉ t
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem mem_sdiff : x in s \ t ↔ x in s ∧ x ∉ t :=
  Iff.rfl

@[simp, norm_cast]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: ((⊤ : L.DefinableSet A α) : Set (α -> M)) = univ
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_top
  结论: ((⊤ : L.DefinableSet A α) : 集合 (α -> M)) = univ
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_top : ((⊤ : L.DefinableSet A α) : Set (α -> M)) = univ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ((⊥ : L.DefinableSet A α) : Set (α -> M)) = ∅
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_bot
  结论: ((⊥ : L.DefinableSet A α) : 集合 (α -> M)) = ∅
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_bot : ((⊥ : L.DefinableSet A α) : Set (α -> M)) = ∅ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  given: (s t : L.DefinableSet A α)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_sup
  条件: (s t : L.DefinableSet A α)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_sup (s t : L.DefinableSet A α) :
    ((s ⊔ t : L.DefinableSet A α) : Set (α -> M)) = (s : Set (α -> M)) union (t : Set (α -> M)) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (s t : L.DefinableSet A α)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_inf
  条件: (s t : L.DefinableSet A α)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_inf (s t : L.DefinableSet A α) :
    ((s ⊓ t : L.DefinableSet A α) : Set (α -> M)) = (s : Set (α -> M)) inter (t : Set (α -> M)) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_compl` / 定理 `coe_compl`

English:
theorem coe_compl
  given: (s : L.DefinableSet A α)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_compl
  条件: (s : L.DefinableSet A α)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_compl (s : L.DefinableSet A α) :
    ((sᶜ : L.DefinableSet A α) : Set (α -> M)) = (s : Set (α -> M))ᶜ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_sdiff` / 定理 `coe_sdiff`

English:
theorem coe_sdiff
  given: (s t : L.DefinableSet A α)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_sdiff
  条件: (s t : L.DefinableSet A α)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_sdiff (s t : L.DefinableSet A α) :
    ((s \ t : L.DefinableSet A α) : Set (α -> M)) = (s : Set (α -> M)) \ (t : Set (α -> M)) :=
  rfl

@[simp, norm_cast]
/--
lemma `coe_himp` / 引理 `coe_himp`

English:
lemma coe_himp
  given: (s t : L.DefinableSet A α)
  statement: ↑(s ⇨ t) = (s ⇨ t : Set (α -> M))
  proof: rfl

中文:
引理 coe_himp
  条件: (s t : L.DefinableSet A α)
  结论: ↑(s ⇨ t) = (s ⇨ t : 集合 (α -> M))
  证明: rfl
-/
lemma coe_himp (s t : L.DefinableSet A α) : ↑(s ⇨ t) = (s ⇨ t : Set (α -> M)) := rfl

/--
Instance `instBooleanAlgebra` / 实例 `instBooleanAlgebra`

English:
instance instBooleanAlgebra
  signature: : BooleanAlgebra (L.DefinableSet A α)
  body: Function.Injective.booleanAlgebra _ Subtype.coe_injective .rfl .rfl
    coe_sup coe_inf coe_top coe_bot coe_compl coe_sdiff coe_himp

中文:
实例 inst布尔eanAlgebra
  签名: : 布尔代数 (L.DefinableSet A α)
  定义体: Function.Injective.booleanAlgebra _ Subtype.coe_injective .rfl .rfl
    coe_sup coe_inf coe_top coe_bot coe_compl coe_sdiff coe_himp

Depends on / 依赖: Function, Function.Injective.booleanAlgebra, Injective, Subtype, Subtype.coe_injective, booleanAlgebra, coe_bot, coe_compl, coe_himp, coe_inf, coe_injective, coe_sdiff, coe_sup, coe_top
-/
noncomputable instance instBooleanAlgebra : BooleanAlgebra (L.DefinableSet A α) :=
  Function.Injective.booleanAlgebra _ Subtype.coe_injective .rfl .rfl
    coe_sup coe_inf coe_top coe_bot coe_compl coe_sdiff coe_himp

end DefinableSet

end Language

end FirstOrder

section

open FirstOrder FirstOrder.Language Set Function

variable {M : Type*} (L : Language) [L.Structure M]
variable {α β : Type*} (A : Set M)

namespace Set

/-- A function from tuples of elements of `M` to `M` is definable if its graph is definable. -/
@[fun_prop]
/--
Definition of `DefinableFun` / `DefinableFun` 的定义

English:
definition DefinableFun
  signature: (f : (α -> M) -> M)
  body: A.Definable L f.tupleGraph

中文:
定义 DefinableFun
  签名: (f : (α -> M) -> M)
  定义体: A.Definable L f.tupleGraph

Depends on / 依赖: A.Definable, Definable, f.tupleGraph, tupleGraph
-/
def DefinableFun (f : (α -> M) -> M) : Prop :=
  A.Definable L f.tupleGraph

/--
Definition of `DefinableMap` / `DefinableMap` 的定义

English:
definition DefinableMap
  signature: (F : (α -> M) -> (β -> M))
  body: forall i : β, A.DefinableFun L (fun x => F x i)

中文:
定义 DefinableMap
  签名: (F : (α -> M) -> (β -> M))
  定义体: forall i : β, A.DefinableFun L (fun x => F x i)

Depends on / 依赖: A.DefinableFun, DefinableFun
-/
def DefinableMap (F : (α -> M) -> (β -> M)) : Prop :=
  forall i : β, A.DefinableFun L (fun x => F x i)

variable {L A} {f : (α -> M) -> M}

@[fun_prop, gcongr]
/--
theorem `DefinableFun.mono` / 定理 `DefinableFun.mono`

English:
theorem DefinableFun.mono
  given: {B : Set M} (hAs : A.DefinableFun L f) (hAB : A subseteq B)
  proof: Set.Definable.mono hAs hAB

@[fun_prop]

中文:
定理 DefinableFun.mono
  条件: {B : 集合 M} (hAs : A.DefinableFun L f) (hAB : A subseteq B)
  证明: Set.Definable.mono hAs hAB

@[fun_prop]

Depends on / 依赖: Definable, Set.Definable.mono
-/
theorem DefinableFun.mono {B : Set M} (hAs : A.DefinableFun L f) (hAB : A subseteq B) :
    B.DefinableFun L f :=
  Set.Definable.mono hAs hAB

@[fun_prop]
/--
theorem `DefinableFun.of_empty` / 定理 `DefinableFun.of_empty`

English:
theorem DefinableFun.of_empty
  given: (hAs : (∅ : Set M).DefinableFun L f)
  proof: Set.Definable.mono hAs (empty_subset A)

中文:
定理 DefinableFun.of_empty
  条件: (hAs : (∅ : 集合 M).DefinableFun L f)
  证明: Set.Definable.mono hAs (empty_subset A)

Depends on / 依赖: Definable, Set.Definable.mono, empty_subset
-/
theorem DefinableFun.of_empty (hAs : (∅ : Set M).DefinableFun L f) :
    A.DefinableFun L f := Set.Definable.mono hAs (empty_subset A)

/--
theorem `empty_definableFun_iff` / 定理 `empty_definableFun_iff`

English:
theorem empty_definableFun_iff
  proof: by
  simp [DefinableFun, Set.empty_definable_iff]

中文:
定理 empty_definableFun_iff
  证明: by
  simp [DefinableFun, Set.empty_definable_iff]

Depends on / 依赖: DefinableFun, Set.empty_definable_iff, empty_definable_iff
-/
theorem empty_definableFun_iff :
    (∅ : Set M).DefinableFun L f ↔
      exists φ : L.Formula (Option α), f.tupleGraph = Set.ofPred φ.Realize := by
  simp [DefinableFun, Set.empty_definable_iff]

/--
theorem `definableFun_iff_empty_definableFun_with_params` / 定理 `definableFun_iff_empty_definableFun_with_params`

English:
theorem definableFun_iff_empty_definableFun_with_params
  proof: empty_definable_iff.symm

中文:
定理 definableFun_iff_empty_definableFun_with_params
  证明: empty_definable_iff.symm

Depends on / 依赖: empty_definable_iff, empty_definable_iff.symm
-/
theorem definableFun_iff_empty_definableFun_with_params :
    A.DefinableFun L f ↔ (∅ : Set M).DefinableFun (L[[A]]) f :=
  empty_definable_iff.symm

/-- A term is a definable function. -/
@[fun_prop]
/--
theorem `_root_.FirstOrder.Language.Term.definableFun_realize` / 定理 `_root_.FirstOrder.Language.Term.definableFun_realize`

English:
theorem _root_.FirstOrder.Language.Term.definableFun_realize
  given: (t : L.Term α)
  proof: by
  rw [empty_definableFun_iff]
  refine ⟨(t.relabel some).equal (Term.var none), ?_⟩
  ext v
  simp [tupleGraph]

中文:
定理 _root_.FirstOrder.Language.项.definableFun_realize
  条件: (t : L.项 α)
  证明: by
  rw [empty_definableFun_iff]
  refine ⟨(t.relabel some).equal (Term.var none), ?_⟩
  ext v
  simp [tupleGraph]

Depends on / 依赖: Term.var, empty_definableFun_iff, relabel, t.relabel, tupleGraph
-/
theorem _root_.FirstOrder.Language.Term.definableFun_realize (t : L.Term α) :
    (∅ : Set M).DefinableFun L (t.realize) := by
  rw [empty_definableFun_iff]
  refine ⟨(t.relabel some).equal (Term.var none), ?_⟩
  ext v
  simp [tupleGraph]

/-- A function symbol is a definable function. -/
@[fun_prop]
/--
theorem `DefinableFun.fun_symbol` / 定理 `DefinableFun.fun_symbol`

English:
theorem DefinableFun.fun_symbol
  given: {n : Nat} (f : L.Functions n)
  proof: (Term.func f Term.var).definableFun_realize

中文:
定理 DefinableFun.fun_symbol
  条件: {n : 自然数} (f : L.函数 n)
  证明: (Term.func f Term.var).definableFun_realize

Depends on / 依赖: Term.func, Term.var, definableFun_realize
-/
theorem DefinableFun.fun_symbol {n : Nat} (f : L.Functions n) :
    (∅ : Set M).DefinableFun L (Structure.funMap f) :=
  (Term.func f Term.var).definableFun_realize

variable (L)

/-- A coordinate projection is a definable function. -/
@[fun_prop]
/--
theorem `_root_.FirstOrder.Language.definableFun_var` / 定理 `_root_.FirstOrder.Language.definableFun_var`

English:
theorem _root_.FirstOrder.Language.definableFun_var
  given: (i : α)
  proof: (Term.var i).definableFun_realize

@[fun_prop]

中文:
定理 _root_.FirstOrder.Language.definableFun_var
  条件: (i : α)
  证明: (Term.var i).definableFun_realize

@[fun_prop]

Depends on / 依赖: Term.var, definableFun_realize
-/
theorem _root_.FirstOrder.Language.definableFun_var (i : α) :
    (∅ : Set M).DefinableFun L (fun v => v i) :=
  (Term.var i).definableFun_realize

@[fun_prop]
/--
theorem `DefinableFun.proj` / 定理 `DefinableFun.proj`

English:
theorem DefinableFun.proj
  given: {i : α}
  statement: A.DefinableFun L fun v => v i
  proof: of_empty L.definableFun_var i

中文:
定理 DefinableFun.proj
  条件: {i : α}
  结论: A.DefinableFun L fun v => v i
  证明: of_empty L.definableFun_var i

Depends on / 依赖: L.definableFun_var, definableFun_var, of_empty
-/
theorem DefinableFun.proj {i : α} : A.DefinableFun L fun v => v i :=
of_empty L.definableFun_var i

/-- A constant function is a definable function. -/
@[fun_prop]
/--
theorem `_root_.FirstOrder.Language.definableFun_const` / 定理 `_root_.FirstOrder.Language.definableFun_const`

English:
theorem _root_.FirstOrder.Language.definableFun_const
  statement: {A : Set M} {a : M}
  proof: by
  rw [definableFun_iff_empty_definableFun_with_params]
  exact ((L.con (⟨a,ha⟩ : ↑A)).term).definableFun_realize

中文:
定理 _root_.FirstOrder.Language.definableFun_const
  结论: {A : 集合 M} {a : M}
  证明: by
  rw [definableFun_iff_empty_definableFun_with_params]
  exact ((L.con (⟨a,ha⟩ : ↑A)).term).definableFun_realize

Depends on / 依赖: L.con, definableFun_iff_empty_definableFun_with_params, definableFun_realize
-/
theorem _root_.FirstOrder.Language.definableFun_const {A : Set M} {a : M}
    (γ : Type*) (ha : a in A) :
    A.DefinableFun L (fun _ : γ -> M => a) := by
  rw [definableFun_iff_empty_definableFun_with_params]
  exact ((L.con (⟨a,ha⟩ : ↑A)).term).definableFun_realize

variable {L}

/--
lemma `_root_.Set.Definable.preimage_map` / 引理 `_root_.Set.Definable.preimage_map`

English:
lemma _root_.Set.Definable.preimage_map
  proof: by
  have h_graph : A.Definable L { w : α oplus β -> M | forall i, F (w ∘ Sum.inl) i = w (Sum.inr i) } := by
    rw [ofPred_forall]
    refine definable_iInter_of_finite fun i => ?_
    simpa [tupleGraph] using!
      (hF i).preimage_comp (fun | none => Sum.inr i | some j => Sum.inl j)
  have h_cyl : A.Definable L { w : α oplus β -> M | w ∘ Sum.inr in S } :=
    hS.preimage_comp Sum.inr
  convert! Definable.exists_of_finite (Definable.inter h_graph h_cyl) using 1
  ext v
  simp [← funext_iff]

@[fun_prop]

中文:
引理 _root_.集合.Definable.preimage_map
  证明: by
  have h_graph : A.Definable L { w : α oplus β -> M | forall i, F (w ∘ Sum.inl) i = w (Sum.inr i) } := by
    rw [ofPred_forall]
    refine definable_iInter_of_finite fun i => ?_
    simpa [tupleGraph] using!
      (hF i).preimage_comp (fun | none => Sum.inr i | some j => Sum.inl j)
  have h_cyl : A.Definable L { w : α oplus β -> M | w ∘ Sum.inr in S } :=
    hS.preimage_comp Sum.inr
  convert! Definable.exists_of_finite (Definable.inter h_graph h_cyl) using 1
  ext v
  simp [← funext_iff]

@[fun_prop]

Depends on / 依赖: A.Definable, Definable, Definable.exists_of_finite, Definable.inter, Sum.inl, Sum.inr, convert, definable_iInter_of_finite, exists_of_finite, funext_iff, hS.preimage_comp, h_cyl, h_graph, ofPred_forall, preimage_comp, tupleGraph
-/
lemma _root_.Set.Definable.preimage_map
    {α β : Type*} [Finite β] {F : (α -> M) -> (β -> M)} (hF : A.DefinableMap L F)
    {S : Set (β -> M)} (hS : A.Definable L S) :
    A.Definable L (F ⁻¹' S) := by
  have h_graph : A.Definable L { w : α oplus β -> M | forall i, F (w ∘ Sum.inl) i = w (Sum.inr i) } := by
    rw [ofPred_forall]
    refine definable_iInter_of_finite fun i => ?_
    simpa [tupleGraph] using!
      (hF i).preimage_comp (fun | none => Sum.inr i | some j => Sum.inl j)
  have h_cyl : A.Definable L { w : α oplus β -> M | w ∘ Sum.inr in S } :=
    hS.preimage_comp Sum.inr
  convert! Definable.exists_of_finite (Definable.inter h_graph h_cyl) using 1
  ext v
  simp [← funext_iff]

@[fun_prop]
/--
theorem `DefinableFun.comp` / 定理 `DefinableFun.comp`

English:
theorem DefinableFun.comp
  statement: [Finite α] {g : (β -> M) -> α -> M}
  proof: by
  let G : (Option β -> M) -> Option α -> M := fun w j =>
    match j with
    | none => w none
    | some i => g (w ∘ some) i
  have hG : A.DefinableMap L G := by
    intro i
    cases i with
    | none => fun_prop
    | some j =>
      simpa [tupleGraph] using!
        ((hg j).preimage_comp fun | none => none | some i => some (some i))
  simpa [DefinableFun, G, tupleGraph] using! hf.preimage_map hG

@[fun_prop]

中文:
定理 DefinableFun.comp
  结论: [有限 α] {g : (β -> M) -> α -> M}
  证明: by
  let G : (Option β -> M) -> Option α -> M := fun w j =>
    match j with
    | none => w none
    | some i => g (w ∘ some) i
  have hG : A.DefinableMap L G := by
    intro i
    cases i with
    | none => fun_prop
    | some j =>
      simpa [tupleGraph] using!
        ((hg j).preimage_comp fun | none => none | some i => some (some i))
  simpa [DefinableFun, G, tupleGraph] using! hf.preimage_map hG

@[fun_prop]

Depends on / 依赖: A.DefinableMap, DefinableFun, DefinableMap, fun_prop, hf.preimage_map, preimage_comp, preimage_map, tupleGraph
-/
theorem DefinableFun.comp [Finite α] {g : (β -> M) -> α -> M}
    (hg : A.DefinableMap L g) (hf : A.DefinableFun L f) :
    A.DefinableFun L fun v => f (g v) := by
  let G : (Option β -> M) -> Option α -> M := fun w j =>
    match j with
    | none => w none
    | some i => g (w ∘ some) i
  have hG : A.DefinableMap L G := by
    intro i
    cases i with
    | none => fun_prop
    | some j =>
      simpa [tupleGraph] using!
        ((hg j).preimage_comp fun | none => none | some i => some (some i))
  simpa [DefinableFun, G, tupleGraph] using! hf.preimage_map hG

@[fun_prop]
/--
theorem `DefinableFun.ite` / 定理 `DefinableFun.ite`

English:
theorem DefinableFun.ite
  statement: {p : (α -> M) -> Prop} {g} [DecidablePred p]
  proof: by
  let P : Set (Option α -> M) := {w | p (w ∘ some)}
  have hP : A.Definable L P := hp.preimage_comp some
  simp only [DefinableFun]
  convert! (hP.inter hf).union (hP.compl.inter hg)
  ext w
  by_cases h : p (w ∘ some) <;> simp [tupleGraph, P, h]

中文:
定理 DefinableFun.ite
  结论: {p : (α -> M) -> 命题} {g} [DecidablePred p]
  证明: by
  let P : Set (Option α -> M) := {w | p (w ∘ some)}
  have hP : A.Definable L P := hp.preimage_comp some
  simp only [DefinableFun]
  convert! (hP.inter hf).union (hP.compl.inter hg)
  ext w
  by_cases h : p (w ∘ some) <;> simp [tupleGraph, P, h]

Depends on / 依赖: A.Definable, Definable, DefinableFun, convert, hP.compl.inter, hP.inter, hp.preimage_comp, preimage_comp, tupleGraph
-/
theorem DefinableFun.ite {p : (α -> M) -> Prop} {g} [DecidablePred p]
    (hp : A.Definable L (Set.ofPred p)) (hf : DefinableFun L A f) (hg : DefinableFun L A g) :
    DefinableFun L A fun v => if p v then f v else g v := by
  let P : Set (Option α -> M) := {w | p (w ∘ some)}
  have hP : A.Definable L P := hp.preimage_comp some
  simp only [DefinableFun]
  convert! (hP.inter hf).union (hP.compl.inter hg)
  ext w
  by_cases h : p (w ∘ some) <;> simp [tupleGraph, P, h]

/--
lemma `DefinableFun.ofPred_eq` / 引理 `DefinableFun.ofPred_eq`

English:
lemma DefinableFun.ofPred_eq
  statement: {f g : (α -> M) -> M}
  proof: by
  have hF : A.DefinableMap L (fun v => ![f v, g v]) := by
    simp [DefinableMap, *]
  exact (Definable.diagonal L A).preimage_map hF

@[deprecated (since := "2026-07-09")]
alias DefinableFun.setOf_eq := DefinableFun.ofPred_eq

中文:
引理 DefinableFun.ofPred_eq
  结论: {f g : (α -> M) -> M}
  证明: by
  have hF : A.DefinableMap L (fun v => ![f v, g v]) := by
    simp [DefinableMap, *]
  exact (Definable.diagonal L A).preimage_map hF

@[deprecated (since := "2026-07-09")]
alias DefinableFun.setOf_eq := DefinableFun.ofPred_eq

Depends on / 依赖: A.DefinableMap, Definable, Definable.diagonal, DefinableMap, diagonal, preimage_map
-/
lemma DefinableFun.ofPred_eq {f g : (α -> M) -> M}
    (hf : A.DefinableFun L f) (hg : A.DefinableFun L g) :
    A.Definable L {v : α -> M | f v = g v} := by
  have hF : A.DefinableMap L (fun v => ![f v, g v]) := by
    simp [DefinableMap, *]
  exact (Definable.diagonal L A).preimage_map hF

@[deprecated (since := "2026-07-09")]
alias DefinableFun.setOf_eq := DefinableFun.ofPred_eq

/--
lemma `DefinableFun.ofPred_eq_const` / 引理 `DefinableFun.ofPred_eq_const`

English:
lemma DefinableFun.ofPred_eq_const
  statement: {f : (α -> M) -> M} (hf : A.DefinableFun L f) {a : M}
  proof: hf.ofPred_eq (L.definableFun_const α ha)

@[deprecated (since := "2026-07-09")]
alias DefinableFun.setOf_eq_const := DefinableFun.ofPred_eq_const

中文:
引理 DefinableFun.ofPred_eq_const
  结论: {f : (α -> M) -> M} (hf : A.DefinableFun L f) {a : M}
  证明: hf.ofPred_eq (L.definableFun_const α ha)

@[deprecated (since := "2026-07-09")]
alias DefinableFun.setOf_eq_const := DefinableFun.ofPred_eq_const

Depends on / 依赖: L.definableFun_const, definableFun_const, hf.ofPred_eq, ofPred_eq
-/
lemma DefinableFun.ofPred_eq_const {f : (α -> M) -> M} (hf : A.DefinableFun L f) {a : M}
    (ha : a in A) :
    A.Definable L {v : α -> M | f v = a} :=
  hf.ofPred_eq (L.definableFun_const α ha)

@[deprecated (since := "2026-07-09")]
alias DefinableFun.setOf_eq_const := DefinableFun.ofPred_eq_const

end Set

end

namespace Set

variable {M : Type w} (A : Set M) (L : FirstOrder.Language.{u, v}) {L' : FirstOrder.Language}
variable [L.Structure M] [L'.Structure M]

variable {α : Type u₁} {β : Type*}

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

/-- A function from a Cartesian power of a structure to that structure is term-definable over
a set `A` when the value of the function is given by a term with constants `A`. -/
@[fun_prop]
/--
Definition of `TermDefinable` / `TermDefinable` 的定义

English:
definition TermDefinable
  signature: (f : (α -> M) -> M)
  body: exists φ : L[[A]].Term α, f = φ.realize

中文:
定义 TermDefinable
  签名: (f : (α -> M) -> M)
  定义体: exists φ : L[[A]].Term α, f = φ.realize

Depends on / 依赖: realize
-/
def TermDefinable (f : (α -> M) -> M) : Prop :=
  exists φ : L[[A]].Term α, f = φ.realize

/--
theorem `TermDefinable.definable_tupleGraph` / 定理 `TermDefinable.definable_tupleGraph`

English:
theorem TermDefinable.definable_tupleGraph
  given: {f : (α -> M) -> M} (h : A.TermDefinable L f)
  proof: by
  obtain ⟨φ, rfl⟩ := h
  use (φ.relabel some).equal (Term.var none)
  ext
  simp [Function.tupleGraph]

中文:
定理 TermDefinable.definable_tupleGraph
  条件: {f : (α -> M) -> M} (h : A.TermDefinable L f)
  证明: by
  obtain ⟨φ, rfl⟩ := h
  use (φ.relabel some).equal (Term.var none)
  ext
  simp [Function.tupleGraph]

Depends on / 依赖: Function, Function.tupleGraph, Term.var, relabel, tupleGraph
-/
theorem TermDefinable.definable_tupleGraph {f : (α -> M) -> M} (h : A.TermDefinable L f) :
    A.Definable L f.tupleGraph := by
  obtain ⟨φ, rfl⟩ := h
  use (φ.relabel some).equal (Term.var none)
  ext
  simp [Function.tupleGraph]

variable {L} {A B} {f : (α -> M) -> M}

@[fun_prop]
/--
theorem `TermDefinable.map_expansion` / 定理 `TermDefinable.map_expansion`

English:
theorem TermDefinable.map_expansion
  given: (h : A.TermDefinable L f) (φ : L ->ᴸ L') [φ.IsExpansionOn M]
  proof: by
  obtain ⟨ψ, rfl⟩ := h
  use (φ.addConstants A).onTerm ψ
  simp

中文:
定理 TermDefinable.map_expansion
  条件: (h : A.TermDefinable L f) (φ : L ->ᴸ L') [φ.是ExpansionOn M]
  证明: by
  obtain ⟨ψ, rfl⟩ := h
  use (φ.addConstants A).onTerm ψ
  simp

Depends on / 依赖: addConstants, onTerm
-/
theorem TermDefinable.map_expansion (h : A.TermDefinable L f) (φ : L ->ᴸ L') [φ.IsExpansionOn M] :
    A.TermDefinable L' f := by
  obtain ⟨ψ, rfl⟩ := h
  use (φ.addConstants A).onTerm ψ
  simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `termDefinable_empty_iff` / 定理 `termDefinable_empty_iff`

English:
theorem termDefinable_empty_iff
  proof: by
  rw [TermDefinable]; rw [Equiv.exists_congr_left (LEquiv.addEmptyConstants L (∅ : Set M)).onTerm]
  simp

中文:
定理 termDefinable_empty_iff
  证明: by
  rw [TermDefinable]; rw [Equiv.exists_congr_left (LEquiv.addEmptyConstants L (∅ : Set M)).onTerm]
  simp

Depends on / 依赖: Equiv.exists_congr_left, LEquiv, LEquiv.addEmptyConstants, TermDefinable, addEmptyConstants, exists_congr_left, onTerm
-/
theorem termDefinable_empty_iff :
    (∅ : Set M).TermDefinable L f ↔ exists φ : L.Term α, f = φ.realize := by
  rw [TermDefinable]; rw [Equiv.exists_congr_left (LEquiv.addEmptyConstants L (∅ : Set M)).onTerm]
  simp

/--
theorem `termDefinable_empty_withConstants_iff` / 定理 `termDefinable_empty_withConstants_iff`

English:
theorem termDefinable_empty_withConstants_iff
  proof: termDefinable_empty_iff

@[fun_prop]

中文:
定理 termDefinable_empty_withConstants_iff
  证明: termDefinable_empty_iff

@[fun_prop]

Depends on / 依赖: termDefinable_empty_iff
-/
theorem termDefinable_empty_withConstants_iff :
    (∅ : Set M).TermDefinable L[[A]] f ↔ A.TermDefinable L f :=
  termDefinable_empty_iff

@[fun_prop]
/--
theorem `TermDefinable.mono` / 定理 `TermDefinable.mono`

English:
theorem TermDefinable.mono
  given: {f : (α -> M) -> M} (h : A.TermDefinable L f) (hAB : A subseteq B)
  proof: by
  rw [← termDefinable_empty_withConstants_iff] at h ⊢
  exact h.map_expansion (L.lhomWithConstantsMap (Set.inclusion hAB))

中文:
定理 TermDefinable.mono
  条件: {f : (α -> M) -> M} (h : A.TermDefinable L f) (hAB : A subseteq B)
  证明: by
  rw [← termDefinable_empty_withConstants_iff] at h ⊢
  exact h.map_expansion (L.lhomWithConstantsMap (Set.inclusion hAB))

Depends on / 依赖: L.lhomWithConstantsMap, Set.inclusion, h.map_expansion, inclusion, lhomWithConstantsMap, map_expansion, termDefinable_empty_withConstants_iff
-/
theorem TermDefinable.mono {f : (α -> M) -> M} (h : A.TermDefinable L f) (hAB : A subseteq B) :
    B.TermDefinable L f := by
  rw [← termDefinable_empty_withConstants_iff] at h ⊢
  exact h.map_expansion (L.lhomWithConstantsMap (Set.inclusion hAB))

/-- TermDefinable is transitive. If f is TermDefinable in a structure S on L, and all of the
functions' realizations on S are TermDefinable on a structure T on L', then f is
TermDefinable on T in L'. -/
@[fun_prop]
/--
theorem `TermDefinable.trans` / 定理 `TermDefinable.trans`

English:
theorem TermDefinable.trans
  statement: {f : (β -> M) -> M} (h₁ : A.TermDefinable L f)
  proof: by
  obtain ⟨x, rfl⟩ := h₁
  choose c hc using @h₂
  simp only [funext_iff] at hc
  use x.substFunc c
  simp_rw [Term.realize_substFunc hc]

中文:
定理 TermDefinable.trans
  结论: {f : (β -> M) -> M} (h₁ : A.TermDefinable L f)
  证明: by
  obtain ⟨x, rfl⟩ := h₁
  choose c hc using @h₂
  simp only [funext_iff] at hc
  use x.substFunc c
  simp_rw [Term.realize_substFunc hc]

Depends on / 依赖: Term.realize_substFunc, funext_iff, realize_substFunc, simp_rw, substFunc, x.substFunc
-/
theorem TermDefinable.trans {f : (β -> M) -> M} (h₁ : A.TermDefinable L f)
    (h₂ : forall {n} (g : L[[A]].Functions n), A.TermDefinable L' g.term.realize) :
    A.TermDefinable L' f := by
  obtain ⟨x, rfl⟩ := h₁
  choose c hc using @h₂
  simp only [funext_iff] at hc
  use x.substFunc c
  simp_rw [Term.realize_substFunc hc]

variable (L) in
/-- A function from a structure to itself is term-definable over a set `A` when the
value of the function is given by a term with constants `A`. Like `TermDefinable`
but specialized for unary functions in order to write `M → M` instead of `(Unit → M) → M`. -/
@[fun_prop]
/--
Definition of `TermDefinable₁` / `TermDefinable₁` 的定义

English:
definition TermDefinable₁
  signature: (f : M -> M)
  body: A.TermDefinable L fun x => (f (x ()))

中文:
定义 TermDefinable₁
  签名: (f : M -> M)
  定义体: A.TermDefinable L fun x => (f (x ()))

Depends on / 依赖: A.TermDefinable, TermDefinable
-/
def TermDefinable₁ (f : M -> M) : Prop :=
  A.TermDefinable L fun x => (f (x ()))

/--
theorem `termDefinable₁_iff_termDefinable` / 定理 `termDefinable₁_iff_termDefinable`

English:
theorem termDefinable₁_iff_termDefinable
  given: (f : M -> M)
  statement: A.TermDefinable₁ L f ↔
  proof: by
  rfl

alias ⟨TermDefinable₁.termDefinable, TermDefinable.termDefinable₁⟩ :=
  termDefinable₁_iff_termDefinable

中文:
定理 termDefinable₁_iff_termDefinable
  条件: (f : M -> M)
  结论: A.TermDefinable₁ L f ↔
  证明: by
  rfl

alias ⟨TermDefinable₁.termDefinable, TermDefinable.termDefinable₁⟩ :=
  termDefinable₁_iff_termDefinable
-/
theorem termDefinable₁_iff_termDefinable (f : M -> M) : A.TermDefinable₁ L f ↔
    A.TermDefinable L (fun v => f (v ())) := by
  rfl

alias ⟨TermDefinable₁.termDefinable, TermDefinable.termDefinable₁⟩ :=
  termDefinable₁_iff_termDefinable

attribute [fun_prop] TermDefinable.termDefinable₁

/--
theorem `termDefinable₁_iff_exists_term` / 定理 `termDefinable₁_iff_exists_term`

English:
theorem termDefinable₁_iff_exists_term
  given: {f : M -> M}
  statement: A.TermDefinable₁ L f ↔
  proof: by
  refine exists_congr fun φ => ?_
  rw [funext_iff]; rw [funext_iff]; rw [(Equiv.funUnique Unit M).forall_congr']
  simp only [Equiv.funUnique_symm_apply, uniqueElim_const, Function.comp_apply]
  congr!

中文:
定理 termDefinable₁_iff_存在_term
  条件: {f : M -> M}
  结论: A.TermDefinable₁ L f ↔
  证明: by
  refine exists_congr fun φ => ?_
  rw [funext_iff]; rw [funext_iff]; rw [(Equiv.funUnique Unit M).forall_congr']
  simp only [Equiv.funUnique_symm_apply, uniqueElim_const, Function.comp_apply]
  congr!

Depends on / 依赖: Equiv.funUnique, Equiv.funUnique_symm_apply, Function, Function.comp_apply, comp_apply, exists_congr, forall_congr, funUnique, funUnique_symm_apply, funext_iff, uniqueElim_const
-/
theorem termDefinable₁_iff_exists_term {f : M -> M} : A.TermDefinable₁ L f ↔
    exists φ : L[[A]].Term Unit, f = φ.realize ∘ Function.const _ := by
  refine exists_congr fun φ => ?_
  rw [funext_iff]; rw [funext_iff]; rw [(Equiv.funUnique Unit M).forall_congr']
  simp only [Equiv.funUnique_symm_apply, uniqueElim_const, Function.comp_apply]
  congr!

/--
theorem `TermDefinable₁.definable₂_graph` / 定理 `TermDefinable₁.definable₂_graph`

English:
theorem TermDefinable₁.definable₂_graph
  given: {f : M -> M} (h : A.TermDefinable₁ L f)
  proof: by
  obtain ⟨t, h⟩ := h.termDefinable.definable_tupleGraph A L
  use t.relabel (Option.elim · 1 (fun _ => 0))
  ext v
  convert! Set.ext_iff.1 h (v ∘ (Option.elim · 1 (fun _ => 0)))
  simp

中文:
定理 TermDefinable₁.definable₂_graph
  条件: {f : M -> M} (h : A.TermDefinable₁ L f)
  证明: by
  obtain ⟨t, h⟩ := h.termDefinable.definable_tupleGraph A L
  use t.relabel (Option.elim · 1 (fun _ => 0))
  ext v
  convert! Set.ext_iff.1 h (v ∘ (Option.elim · 1 (fun _ => 0)))
  simp

Depends on / 依赖: Option.elim, Set.ext_iff, convert, definable_tupleGraph, ext_iff, h.termDefinable.definable_tupleGraph, relabel, t.relabel, termDefinable
-/
theorem TermDefinable₁.definable₂_graph {f : M -> M} (h : A.TermDefinable₁ L f) :
    A.Definable₂ L f.graph := by
  obtain ⟨t, h⟩ := h.termDefinable.definable_tupleGraph A L
  use t.relabel (Option.elim · 1 (fun _ => 0))
  ext v
  convert! Set.ext_iff.1 h (v ∘ (Option.elim · 1 (fun _ => 0)))
  simp

/-- The identity function is `TermDefinable₁` -/
@[fun_prop]
/--
theorem `TermDefinable₁.id` / 定理 `TermDefinable₁.id`

English:
theorem TermDefinable₁.id
  statement: A.TermDefinable₁ L id
  proof: ⟨Term.var (), rfl⟩

中文:
定理 TermDefinable₁.id
  结论: A.TermDefinable₁ L id
  证明: ⟨Term.var (), rfl⟩

Depends on / 依赖: Term.var
-/
theorem TermDefinable₁.id : A.TermDefinable₁ L id :=
  ⟨Term.var (), rfl⟩

/-- Constant functions are `TermDefinable`, assuming the constant value is a language constant. -/
@[fun_prop]
/--
theorem `TermDefinable.const` / 定理 `TermDefinable.const`

English:
theorem TermDefinable.const
  given: (C : L[[A]].Constants)
  statement: A.TermDefinable L (Function.const (α -> M) C)
  proof: ⟨C.term, by simp only [Term.realize_constants]; rfl⟩

中文:
定理 TermDefinable.const
  条件: (C : L[[A]].Constants)
  结论: A.TermDefinable L (函数.const (α -> M) C)
  证明: ⟨C.term, by simp only [Term.realize_constants]; rfl⟩

Depends on / 依赖: C.term, Term.realize_constants, realize_constants
-/
theorem TermDefinable.const (C : L[[A]].Constants) : A.TermDefinable L (Function.const (α -> M) C) :=
  ⟨C.term, by simp only [Term.realize_constants]; rfl⟩

/-- Constant functions are `TermDefinable₁`, assuming the constant value is a language constant. -/
@[fun_prop]
/--
theorem `TermDefinable₁.const` / 定理 `TermDefinable₁.const`

English:
theorem TermDefinable₁.const
  given: (C : L[[A]].Constants)
  statement: A.TermDefinable₁ L (Function.const M C)
  proof: (TermDefinable.const C).termDefinable₁

中文:
定理 TermDefinable₁.const
  条件: (C : L[[A]].Constants)
  结论: A.TermDefinable₁ L (函数.const M C)
  证明: (TermDefinable.const C).termDefinable₁

Depends on / 依赖: TermDefinable, TermDefinable.const
-/
theorem TermDefinable₁.const (C : L[[A]].Constants) : A.TermDefinable₁ L (Function.const M C) :=
  (TermDefinable.const C).termDefinable₁

/--
theorem `TermDefinable.comp` / 定理 `TermDefinable.comp`

English:
theorem TermDefinable.comp
  statement: {f : (α -> M) -> M} {g : α -> (β -> M) -> M} (hf : A.TermDefinable L f)
  proof: by
  obtain ⟨φ, rfl⟩ := hf
  choose ψ hψ using hg
  use φ.subst ψ
  simp [hψ]

中文:
定理 TermDefinable.comp
  结论: {f : (α -> M) -> M} {g : α -> (β -> M) -> M} (hf : A.TermDefinable L f)
  证明: by
  obtain ⟨φ, rfl⟩ := hf
  choose ψ hψ using hg
  use φ.subst ψ
  simp [hψ]
-/
theorem TermDefinable.comp {f : (α -> M) -> M} {g : α -> (β -> M) -> M} (hf : A.TermDefinable L f)
    (hg : forall i, A.TermDefinable L (g i)) : A.TermDefinable L (fun b => f (g · b)) := by
  obtain ⟨φ, rfl⟩ := hf
  choose ψ hψ using hg
  use φ.subst ψ
  simp [hψ]

/-- `TermDefinable₁` functions are closed under composition. -/
@[fun_prop]
/--
theorem `TermDefinable₁.comp` / 定理 `TermDefinable₁.comp`

English:
theorem TermDefinable₁.comp
  given: {f g : M -> M} (hf : A.TermDefinable₁ L f) (hg : A.TermDefinable₁ L g)
  proof: (hf.termDefinable.comp fun _ => hg.termDefinable).termDefinable₁

中文:
定理 TermDefinable₁.comp
  条件: {f g : M -> M} (hf : A.TermDefinable₁ L f) (hg : A.TermDefinable₁ L g)
  证明: (hf.termDefinable.comp fun _ => hg.termDefinable).termDefinable₁

Depends on / 依赖: hf.termDefinable.comp, hg.termDefinable, termDefinable
-/
theorem TermDefinable₁.comp {f g : M -> M} (hf : A.TermDefinable₁ L f) (hg : A.TermDefinable₁ L g) :
    A.TermDefinable₁ L (f ∘ g) :=
  (hf.termDefinable.comp fun _ => hg.termDefinable).termDefinable₁

/-- A `TermDefinable` function postcomposed with `TermDefinable₁` is `TermDefinable`. -/
@[fun_prop]
/--
theorem `TermDefinable₁.comp_termDefinable` / 定理 `TermDefinable₁.comp_termDefinable`

English:
theorem TermDefinable₁.comp_termDefinable
  statement: {f : M -> M} {g : (α -> M) -> M}
  proof: hf.termDefinable.comp fun _ => hg

中文:
定理 TermDefinable₁.comp_termDefinable
  结论: {f : M -> M} {g : (α -> M) -> M}
  证明: hf.termDefinable.comp fun _ => hg

Depends on / 依赖: hf.termDefinable.comp, termDefinable
-/
theorem TermDefinable₁.comp_termDefinable {f : M -> M} {g : (α -> M) -> M}
    (hf : A.TermDefinable₁ L f) (hg : A.TermDefinable L g) : A.TermDefinable L (f ∘ g) :=
  hf.termDefinable.comp fun _ => hg

end Set
