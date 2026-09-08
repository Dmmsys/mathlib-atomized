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

/-- A subset of a finite Cartesian product of a structure is definable over a set `A` when
  membership in the set is given by a first-order formula with parameters from `A`. -/
/-
**Set.Definable** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：Definable (s : Set (α -> M)) : Prop
参数：s : Set (α -> M)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subset of a finite Cartesian product of a structure is definable over a set `A
` when
  membership in the set is given by a first-order formula with parameters from `
A`.
-/
def Definable (s : Set (α → M)) : Prop :=
  ∃ φ : L[[A]].Formula α, s = Set.ofPred φ.Realize

variable {L} {A} {B : Set M} {s : Set (α → M)}
/-
**Set.Definable.map_expansion** 是 Mathlib 中的一个定理，位于命名空间 `Set.Definable`。
形式化陈述：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language} [inst : L.Structure M
] {α : Type u₁} {s : Set (α → M)}   {L' : FirstOrder.Language} [inst_1 : L'.Stru
cture M],   A.Definable L s → ∀ (φ : L →ᴸ L') [φ.IsExpansionOn M], A.Definable L
' s
参数：α → M；φ : L →ᴸ L'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Definable.map_expansion {L' : FirstOrder.Language} [L'.Structure M] (h : A.Definable L s)
    (φ : L →ᴸ L') [φ.IsExpansionOn M] : A.Definable L' s := by
  obtain ⟨ψ, rfl⟩ := h
  refine ⟨(φ.addConstants A).onFormula ψ, ?_⟩
  ext x
  simp only [mem_ofPred_eq, LHom.realize_onFormula]
/-
**Set.definable_iff_exists_formula_sum** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：definable_iff_exists_formula_sum : A.Definable L s ↔ exists φ : L.Formula 
(A oplus α), s = {v | φ.Realize (Sum.elim (↑) v)}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Definable.eq_1`：∀ {M : Type w} (A : Set M) (L : FirstOrder.Language)
 [inst : L.Structure M] {α : Type u₁} (s : Set (α → M)),   A.Definable L s = ∃ φ
, s = Se…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iff_iff_eq`：∀ {a b : Prop}, (a ↔ b) ↔ a = b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_mapTermRel_id`：realize_mapTer
mRel_id [L'.Structure M] {ft : forall n, L.Term (α oplus (Fin n)) -> L'.Term (β 
oplus (Fin n))} {fr : forall n, L.Relations n …
· 使用定理 `FirstOrder.Language.instIsAlgebraicConstantsOn`：∀ (α : Type u_1), (First
Order.Language.constantsOn α).IsAlgebraic
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FirstOrder.Language.Term.realize_varsToConstants`：realize_varsToConstant
s [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M] {t : L.Term (α 
oplus β)} {v : β -> M} : t.varsToConst…
· 使用定理 `FirstOrder.Language.Term.realize_relabel`：realize_relabel {t : L.Term α}
 {g : α -> β} {v : β -> M} : (t.relabel g).realize v = t.realize (v ∘ g)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem definable_iff_exists_formula_sum :
    A.Definable L s ↔ ∃ φ : L.Formula (A ⊕ α), s = {v | φ.Realize (Sum.elim (↑) v)} := by
  rw [Definable, Equiv.exists_congr_left (BoundedFormula.constantsVarsEquiv)]
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
/-
**Set.empty_definable_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：empty_definable_iff : (∅ : Set M).Definable L s ↔ exists φ : L.Formula α, 
s = Set.ofPred φ.Realize
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Definable.eq_1`：∀ {M : Type w} (A : Set M) (L : FirstOrder.Language)
 [inst : L.Structure M] {α : Type u₁} (s : Set (α → M)),   A.Definable L s = ∃ φ
, s = Se…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.instIsAlgebraicConstantsOn`：∀ (α : Type u_1), (First
Order.Language.constantsOn α).IsAlgebraic
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FirstOrder.Language.LEquiv.symm_toLHom`：∀ {L : FirstOrder.Language} {L' 
: FirstOrder.Language} (e : L ≃ᴸ L'), e.symm.toLHom = e.invLHom
· 使用定理 `FirstOrder.Language.LEquiv.addEmptyConstants_invLHom`：∀ (L : FirstOrder.
Language) (α : Type w') [ie : IsEmpty α],   (FirstOrder.Language.LEquiv.addEmpty
Constants L α).invLHom =     (FirstOrder.L…
· 使用定理 `FirstOrder.Language.LHom.setOfPred_realize_onFormula`：∀ {L : FirstOrder.
Language} {L' : FirstOrder.Language} {M : Type w} [inst : L.Structure M] {α : Ty
pe u'}   [inst_1 : L'.Structure M] (φ : L …
· 使用定理 `FirstOrder.Language.LHom.ofIsEmpty_isExpansionOn`：∀ {L : FirstOrder.Lang
uage} {L' : FirstOrder.Language} (M : Type u_1) [inst : L.Structure M] [inst_1 :
 L'.Structure M]   [inst_2 : L.IsAlgeb…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem empty_definable_iff :
    (∅ : Set M).Definable L s ↔ ∃ φ : L.Formula α, s = Set.ofPred φ.Realize := by
  rw [Definable, Equiv.exists_congr_left (LEquiv.addEmptyConstants L (∅ : Set M)).onFormula]
  simp
/-
**Set.definable_iff_empty_definable_with_params** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：definable_iff_empty_definable_with_params : A.Definable L s ↔ (∅ : Set M).
Definable L[[A]] s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.empty_definable_iff`：empty_definable_iff : (∅ : Set M).Definable L s
 ↔ exists φ : L.Formula α, s = Set.ofPred φ.Realize
-/
theorem definable_iff_empty_definable_with_params :
    A.Definable L s ↔ (∅ : Set M).Definable L[[A]] s :=
  empty_definable_iff.symm
/-
**Set.Definable.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.Definable`。
形式化陈述：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language} [inst : L.Structure M
] {α : Type u₁} {B : Set M} {s : Set (α → M)},   A.Definable L s → A ⊆ B → B.Def
inable L s
参数：α → M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.definable_iff_empty_definable_with_params`：definable_iff_empty_defin
able_with_params : A.Definable L s ↔ (∅ : Set M).Definable L[[A]] s
· 使用定理 `Set.Definable.map_expansion`：∀ {M : Type w} {A : Set M} {L : FirstOrder.
Language} [inst : L.Structure M] {α : Type u₁} {s : Set (α → M)}   {L' : FirstOr
der.Language} [in…
-/
theorem Definable.mono (hAs : A.Definable L s) (hAB : A ⊆ B) : B.Definable L s := by
  rw [definable_iff_empty_definable_with_params] at *
  exact hAs.map_expansion (L.lhomWithConstantsMap (Set.inclusion hAB))

@[simp]
/-
**Set.definable_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：definable_empty : A.Definable L (∅ : Set (α -> M))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem definable_empty : A.Definable L (∅ : Set (α → M)) :=
  ⟨⊥, by
    ext
    simp⟩

@[simp]
/-
**Set.definable_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：definable_univ : A.Definable L (univ : Set (α -> M))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem definable_univ : A.Definable L (univ : Set (α → M)) :=
  ⟨⊤, by
    ext
    simp⟩

@[simp]
/-
**Set.Definable.inter** 是 Mathlib 中的一个定理，位于命名空间 `Set.Definable`。
形式化陈述：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language} [inst : L.Structure M
] {α : Type u₁} {f g : Set (α → M)},   A.Definable L f → A.Definable L g → A.Def
inable L (f ∩ g)
参数：α → M；f ∩ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Definable.inter {f g : Set (α → M)} (hf : A.Definable L f) (hg : A.Definable L g) :
    A.Definable L (f ∩ g) := by
  rcases hf with ⟨φ, rfl⟩
  rcases hg with ⟨θ, rfl⟩
  refine ⟨φ ⊓ θ, ?_⟩
  ext
  simp

@[simp]
/-
**Set.Definable.union** 是 Mathlib 中的一个定理，位于命名空间 `Set.Definable`。
形式化陈述：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language} [inst : L.Structure M
] {α : Type u₁} {f g : Set (α → M)},   A.Definable L f → A.Definable L g → A.Def
inable L (f ∪ g)
参数：α → M；f ∪ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `FirstOrder.Language.Formula.realize_sup`：realize_sup : (φ ⊔ ψ).Realize v
 ↔ φ.Realize v ∨ ψ.Realize v
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Definable.union {f g : Set (α → M)} (hf : A.Definable L f) (hg : A.Definable L g) :
    A.Definable L (f ∪ g) := by
  rcases hf with ⟨φ, hφ⟩
  rcases hg with ⟨θ, hθ⟩
  refine ⟨φ ⊔ θ, ?_⟩
  ext
  rw [hφ, hθ, mem_ofPred_eq, Formula.realize_sup, mem_union, mem_ofPred_eq, mem_ofPred_eq]
/-
**Set.definable_finset_inf** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：definable_finset_inf {ι : Type*} {f : ι -> Set (α -> M)} (hf : forall i, A
.Definable L (f i)) (s : Finset ι) : A.Definable L (s.inf f)
参数：α -> M；hf : forall i, A.Definable L (f i)；s : Finset ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `Set.definable_univ`：definable_univ : A.Definable L (univ : Set (α -> M))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inf_insert`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] [inst_1 : OrderTop α] {s : Finset β} {f : β → α}   [inst_2 : DecidableEq β]
 {b : β…
· 使用定理 `Set.Definable.inter`：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language
} [inst : L.Structure M] {α : Type u₁} {f g : Set (α → M)},   A.Definable L f → 
A.Definab…
-/
theorem definable_finset_inf {ι : Type*} {f : ι → Set (α → M)} (hf : ∀ i, A.Definable L (f i))
    (s : Finset ι) : A.Definable L (s.inf f) := by
  classical
    refine Finset.induction definable_univ (fun i s _ h => ?_) s
    rw [Finset.inf_insert]
    exact (hf i).inter h
/-
**Set.definable_finset_sup** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：definable_finset_sup {ι : Type*} {f : ι -> Set (α -> M)} (hf : forall i, A
.Definable L (f i)) (s : Finset ι) : A.Definable L (s.sup f)
参数：α -> M；hf : forall i, A.Definable L (f i)；s : Finset ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `Set.definable_empty`：definable_empty : A.Definable L (∅ : Set (α -> M))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `Set.Definable.union`：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language
} [inst : L.Structure M] {α : Type u₁} {f g : Set (α → M)},   A.Definable L f → 
A.Definab…
-/
theorem definable_finset_sup {ι : Type*} {f : ι → Set (α → M)} (hf : ∀ i, A.Definable L (f i))
    (s : Finset ι) : A.Definable L (s.sup f) := by
  classical
    refine Finset.induction definable_empty (fun i s _ h => ?_) s
    rw [Finset.sup_insert]
    exact (hf i).union h
/-
**Set.definable_biInter_finset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：definable_biInter_finset {ι : Type*} {f : ι -> Set (α -> M)} (hf : forall 
i, A.Definable L (f i)) (s : Finset ι) : A.Definable L (⋂ i in s, f i)
参数：α -> M；hf : forall i, A.Definable L (f i)；s : Finset ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.inf_set_eq_iInter`：inf_set_eq_iInter (s : Finset α) (f : α -> Set
 β) : s.inf f = ⋂ x in s, f x
· 使用定理 `Set.definable_finset_inf`：definable_finset_inf {ι : Type*} {f : ι -> Set
 (α -> M)} (hf : forall i, A.Definable L (f i)) (s : Finset ι) : A.Definable L (
s.inf f)
-/
theorem definable_biInter_finset {ι : Type*} {f : ι → Set (α → M)}
    (hf : ∀ i, A.Definable L (f i)) (s : Finset ι) : A.Definable L (⋂ i ∈ s, f i) := by
  rw [← Finset.inf_set_eq_iInter]
  exact definable_finset_inf hf s
/-
**Set.definable_biUnion_finset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：definable_biUnion_finset {ι : Type*} {f : ι -> Set (α -> M)} (hf : forall 
i, A.Definable L (f i)) (s : Finset ι) : A.Definable L (⋃ i in s, f i)
参数：α -> M；hf : forall i, A.Definable L (f i)；s : Finset ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_set_eq_biUnion`：sup_set_eq_biUnion (s : Finset α) (f : α -> S
et β) : s.sup f = ⋃ x in s, f x
· 使用定理 `Set.definable_finset_sup`：definable_finset_sup {ι : Type*} {f : ι -> Set
 (α -> M)} (hf : forall i, A.Definable L (f i)) (s : Finset ι) : A.Definable L (
s.sup f)
-/
theorem definable_biUnion_finset {ι : Type*} {f : ι → Set (α → M)}
    (hf : ∀ i, A.Definable L (f i)) (s : Finset ι) : A.Definable L (⋃ i ∈ s, f i) := by
  rw [← Finset.sup_set_eq_biUnion]
  exact definable_finset_sup hf s
/-
**Set.definable_iInter_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：definable_iInter_of_finite {ι : Type*} [Finite ι] {f : ι -> Set (α -> M)} 
(hf : forall i, A.Definable L (f i)) : A.Definable L (⋂ i, f i)
参数：α -> M；hf : forall i, A.Definable L (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inf_set_eq_iInter`：inf_set_eq_iInter (s : Finset α) (f : α -> Set
 β) : s.inf f = ⋂ x in s, f x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_true`：iInter_true {s : True -> Set α} : iInter s = s trivial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.definable_finset_inf`：definable_finset_inf {ι : Type*} {f : ι -> Set
 (α -> M)} (hf : forall i, A.Definable L (f i)) (s : Finset ι) : A.Definable L (
s.inf f)
-/
theorem definable_iInter_of_finite {ι : Type*} [Finite ι] {f : ι → Set (α → M)}
    (hf : ∀ i, A.Definable L (f i)) : A.Definable L (⋂ i, f i) := by
  have := Fintype.ofFinite ι
  convert! definable_finset_inf hf Finset.univ using 1
  simp
/-
**Set.definable_iUnion_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：definable_iUnion_of_finite {ι : Type*} [Finite ι] {f : ι -> Set (α -> M)} 
(hf : forall i, A.Definable L (f i)) : A.Definable L (⋃ i, f i)
参数：α -> M；hf : forall i, A.Definable L (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_set_eq_biUnion`：sup_set_eq_biUnion (s : Finset α) (f : α -> S
et β) : s.sup f = ⋃ x in s, f x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.definable_finset_sup`：definable_finset_sup {ι : Type*} {f : ι -> Set
 (α -> M)} (hf : forall i, A.Definable L (f i)) (s : Finset ι) : A.Definable L (
s.sup f)
-/
theorem definable_iUnion_of_finite {ι : Type*} [Finite ι] {f : ι → Set (α → M)}
    (hf : ∀ i, A.Definable L (f i)) : A.Definable L (⋃ i, f i) := by
  have := Fintype.ofFinite ι
  convert! definable_finset_sup hf Finset.univ using 1
  simp

@[simp]
/-
**Set.Definable.compl** 是 Mathlib 中的一个定理，位于命名空间 `Set.Definable`。
形式化陈述：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language} [inst : L.Structure M
] {α : Type u₁} {s : Set (α → M)},   A.Definable L s → A.Definable L sᶜ
参数：α → M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_ofPred`：compl_ofPred {α} (p : α -> Prop) : { a | p a }ᶜ = { a 
| ¬p a }
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `FirstOrder.Language.Formula.realize_not`：realize_not : φ.not.Realize v ↔
 ¬φ.Realize v
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Definable.compl {s : Set (α → M)} (hf : A.Definable L s) : A.Definable L sᶜ := by
  rcases hf with ⟨φ, hφ⟩
  refine ⟨φ.not, ?_⟩
  ext v
  rw [hφ, compl_ofPred, mem_ofPred, mem_ofPred, Formula.realize_not]

@[simp]
/-
**Set.Definable.sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Definable`。
形式化陈述：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language} [inst : L.Structure M
] {α : Type u₁} {s t : Set (α → M)},   A.Definable L s → A.Definable L t → A.Def
inable L (s \ t)
参数：α → M；s \ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Definable.inter`：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language
} [inst : L.Structure M] {α : Type u₁} {f g : Set (α → M)},   A.Definable L f → 
A.Definab…
· 使用定理 `Set.Definable.compl`：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language
} [inst : L.Structure M] {α : Type u₁} {s : Set (α → M)},   A.Definable L s → A.
Definable…
-/
theorem Definable.sdiff {s t : Set (α → M)} (hs : A.Definable L s) (ht : A.Definable L t) :
    A.Definable L (s \ t) :=
  hs.inter ht.compl
/-
**Set.Definable.himp** 是 Mathlib 中的一个定理，位于命名空间 `Set.Definable`。
形式化陈述：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language} [inst : L.Structure M
] {α : Type u₁} {s t : Set (α → M)},   A.Definable L s → A.Definable L t → A.Def
inable L (s ⇨ t)
参数：α → M；s ⇨ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `himp_eq`：himp_eq : x ⇨ y = y ⊔ xᶜ
· 使用定理 `Set.Definable.union`：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language
} [inst : L.Structure M] {α : Type u₁} {f g : Set (α → M)},   A.Definable L f → 
A.Definab…
· 使用定理 `Set.Definable.compl`：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language
} [inst : L.Structure M] {α : Type u₁} {s : Set (α → M)},   A.Definable L s → A.
Definable…
-/
@[simp] lemma Definable.himp {s t : Set (α → M)} (hs : A.Definable L s) (ht : A.Definable L t) :
    A.Definable L (s ⇨ t) := by rw [himp_eq]; exact ht.union hs.compl
/-
**Set.Definable.preimage_comp** 是 Mathlib 中的一个定理，位于命名空间 `Set.Definable`。
形式化陈述：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language} [inst : L.Structure M
] {α : Type u₁} {β : Type u_1} (f : α → β)   {s : Set (α → M)}, A.Definable L s 
→ A.Definable L ((fun g => g ∘ f) ⁻¹' s)
参数：f : α → β；α → M；(fun g => g ∘ f) ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Definable.preimage_comp (f : α → β) {s : Set (α → M)} (h : A.Definable L s) :
    A.Definable L ((fun g : β → M => g ∘ f) ⁻¹' s) := by
  obtain ⟨φ, rfl⟩ := h
  refine ⟨φ.relabel f, ?_⟩
  ext
  simp only [Set.preimage_ofPred_eq, mem_ofPred_eq, Formula.realize_relabel]
/-
**Set.Definable.image_comp_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Set.Definable`。
形式化陈述：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language} [inst : L.Structure M
] {α : Type u₁} {β : Type u_1}   {s : Set (β → M)}, A.Definable L s → ∀ (f : α ≃
 β), A.Definable L ((fun g => g ∘ ⇑f) '' s)
参数：β → M；f : α ≃ β；(fun g => g ∘ ⇑f) '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_eq_preimage_of_inverse`：image_eq_preimage_of_inverse {f : α ->
 β} {g : β -> α} (h₁ : LeftInverse g f) (h₂ : RightInverse g f) : image f = prei
mage g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Set.Definable.preimage_comp`：∀ {M : Type w} {A : Set M} {L : FirstOrder.
Language} [inst : L.Structure M] {α : Type u₁} {β : Type u_1} (f : α → β)   {s :
 Set (α → M)}, A.…
-/
theorem Definable.image_comp_equiv {s : Set (β → M)} (h : A.Definable L s) (f : α ≃ β) :
    A.Definable L ((fun g : β → M => g ∘ f) '' s) := by
  refine (congr rfl ?_).mp (h.preimage_comp f.symm)
  rw [image_eq_preimage_of_inverse]
  · intro i
    ext b
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  · intro i
    ext a
    simp
/-
**Set.definable_iff_finitely_definable** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：definable_iff_finitely_definable : A.Definable L s ↔ exists (A0 : Finset M
), (A0 : Set M) subseteq A ∧ (A0 : Set M).Definable L s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `iff_comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用定理 `FirstOrder.Language.BoundedFormula.realize_restrictFreeVar`：realize_rest
rictFreeVar [DecidableEq α] {n : Nat} {φ : L.BoundedFormula α n} {f : φ.freeVarF
inset -> β} {v : β -> M} {xs : Fin n -> M} (v' :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Definable.mono`：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language}
 [inst : L.Structure M] {α : Type u₁} {B : Set M} {s : Set (α → M)},   A.Definab
le L s →…
-/
theorem definable_iff_finitely_definable :
    A.Definable L s ↔ ∃ (A0 : Finset M), (A0 : Set M) ⊆ A ∧
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
    exact iff_comm.1 <| BoundedFormula.realize_restrictFreeVar _ (by simp)
  · rintro ⟨A0, hA0, hd⟩
    exact Definable.mono hd hA0

/-- This lemma is only intended as a helper for `Definable.image_comp`. -/
/-
**Set.Definable.image_comp_sumInl_fin** 是 Mathlib 中的一个定理，位于命名空间 `Set.Definable`。
形式化陈述：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language} [inst : L.Structure M
] {α : Type u₁} (m : ℕ)   {s : Set (α ⊕ Fin m → M)}, A.Definable L s → A.Definab
le L ((fun g => g ∘ Sum.inl) '' s)
参数：m : ℕ；α ⊕ Fin m → M；(fun g => g ∘ Sum.inl) '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.cast_refl`：∀ (n : ℕ) (h : n = n), Fin.cast h = id
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sum.elim_comp_inl_inr`：∀ {α : Type u_1} {β : Type u_2} {γ : Sort u_3} (f
 : α ⊕ β → γ), Sum.elim (f ∘ Sum.inl) (f ∘ Sum.inr) = f
· 使用定理 `Sum.elim_comp_inl`：∀ {α : Type u_1} {γ : Sort u_2} {β : Type u_3} (f : α
 → γ) (g : β → γ), Sum.elim f g ∘ Sum.inl = f

--- 原说明 ---
This lemma is only intended as a helper for `Definable.image_comp`.
-/
theorem Definable.image_comp_sumInl_fin (m : ℕ) {s : Set (Sum α (Fin m) → M)}
    (h : A.Definable L s) : A.Definable L ((fun g : Sum α (Fin m) → M => g ∘ Sum.inl) '' s) := by
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

/-- Shows that definability is closed under finite projections. -/
/-
**Set.Definable.image_comp_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Set.Definable`。
形式化陈述：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language} [inst : L.Structure M
] {α : Type u₁} {β : Type u_1}   {s : Set (β → M)}, A.Definable L s → ∀ (f : α ↪
 β) [Finite β], A.Definable L ((fun g => g ∘ ⇑f) '' s)
参数：β → M；f : α ↪ β；(fun g => g ∘ ⇑f) '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Eq.congr_left`：∀ {α : Sort u_1} {x y z : α}, x = y → (x = z ↔ y = z)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.sumCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_11
} {β₂ : Type u_12} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (a : α₁ ⊕ β₁),   (ea.sumCongr e
b) a = Sum…
· 使用定理 `Equiv.ofInjective_apply`：∀ {α : Sort u_3} {β : Type u_4} (f : α → β) (hf
 : Function.Injective f) (a : α), (Equiv.ofInjective f hf) a = ⟨f a, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.Definable.image_comp_sumInl_fin`：∀ {M : Type w} {A : Set M} {L : Fir
stOrder.Language} [inst : L.Structure M] {α : Type u₁} (m : ℕ)   {s : Set (α ⊕ F
in m → M)}, A.Definable L…
· 使用定理 `Set.Definable.image_comp_equiv`：∀ {M : Type w} {A : Set M} {L : FirstOrd
er.Language} [inst : L.Structure M] {α : Type u₁} {β : Type u_1}   {s : Set (β →
 M)}, A.Definable L …

--- 原说明 ---
Shows that definability is closed under finite projections.
-/
theorem Definable.image_comp_embedding {s : Set (β → M)} (h : A.Definable L s) (f : α ↪ β)
    [Finite β] : A.Definable L ((fun g : β → M => g ∘ f) '' s) := by
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

/-- Shows that definability is closed under finite projections. -/
/-
**Set.Definable.image_comp** 是 Mathlib 中的一个定理，位于命名空间 `Set.Definable`。
形式化陈述：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language} [inst : L.Structure M
] {α : Type u₁} {β : Type u_1}   {s : Set (β → M)}, A.Definable L s → ∀ (f : α →
 β) [Finite α] [Finite β], A.Definable L ((fun g => g ∘ f) '' s)
参数：β → M；f : α → β；(fun g => g ∘ f) '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Set.Definable.preimage_comp`：∀ {M : Type w} {A : Set M} {L : FirstOrder.
Language} [inst : L.Structure M] {α : Type u₁} {β : Type u_1} (f : α → β)   {s :
 Set (α → M)}, A.…
· 使用定理 `Set.Definable.image_comp_sumInl_fin`：∀ {M : Type w} {A : Set M} {L : Fir
stOrder.Language} [inst : L.Structure M] {α : Type u₁} (m : ℕ)   {s : Set (α ⊕ F
in m → M)}, A.Definable L…
· 使用定理 `Set.Definable.image_comp_equiv`：∀ {M : Type w} {A : Set M} {L : FirstOrd
er.Language} [inst : L.Structure M] {α : Type u₁} {β : Type u_1}   {s : Set (β →
 M)}, A.Definable L …
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_true`：iInter_true {s : True -> Set α} : iInter s = s trivial
· 使用定理 `Set.definable_biInter_finset`：definable_biInter_finset {ι : Type*} {f : 
ι -> Set (α -> M)} (hf : forall i, A.Definable L (f i)) (s : Finset ι) : A.Defin
able L (⋂ i in s, …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Equiv.sumCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_11
} {β₂ : Type u_12} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (a : α₁ ⊕ β₁),   (ea.sumCongr e
b) a = Sum…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.apply_rangeSplitting`：apply_rangeSplitting (f : α -> β) (x : range f
) : f (rangeSplitting f x) = x
· 使用定理 `Set.rangeFactorization_coe`：rangeFactorization_coe (f : ι -> β) (a : ι) 
: (rangeFactorization f a : β) = f a
· 使用定理 `Set.Definable.inter`：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language
} [inst : L.Structure M] {α : Type u₁} {f g : Set (α → M)},   A.Definable L f → 
A.Definab…

--- 原说明 ---
Shows that definability is closed under finite projections.
-/
theorem Definable.image_comp {s : Set (β → M)} (h : A.Definable L s) (f : α → β) [Finite α]
    [Finite β] : A.Definable L ((fun g : β → M => g ∘ f) '' s) := by
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
      A.Definable L { x : α → M | ∀ a, x a = x (rangeSplitting f (rangeFactorization f a)) } := by
      have h' : ∀ a,
        A.Definable L { x : α → M | x a = x (rangeSplitting f (rangeFactorization f a)) } := by
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
      rw [hx a, ← Function.comp_apply (f := x), ← hy]
      simp
    · rintro ⟨y, ys, rfl⟩
      refine ⟨⟨y, ys, ?_⟩, fun a => ?_⟩
      · ext
        simp [Set.apply_rangeSplitting f]
      · rw [Function.comp_apply, Function.comp_apply, apply_rangeSplitting f,
          rangeFactorization_coe]

/-- Finite existential quantifiers preserve definablity. -/
/-
**Set.Definable.exists_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set.Definable`。
形式化陈述：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language} [inst : L.Structure M
] {α : Type u₁} {β : Type u_1} [Finite β]   {S : Set (α ⊕ β → M)}, A.Definable L
 S → A.Definable L {v | ∃ u, Sum.elim v u ∈ S}
参数：α ⊕ β → M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Finite existential quantifiers preserve definablity.
-/
lemma Definable.exists_of_finite [Finite β] {S : Set ((α ⊕ β) → M)}
    (hS : A.Definable L S) :
    A.Definable L { v : α → M | ∃ u : β → M, Sum.elim v u ∈ S } := by
  obtain ⟨φ, hφ⟩ := hS
  exists φ.iExs β
  ext v
  simp [hφ]

/-- Finite universal quantifiers preserve definablity. -/
/-
**Set.Definable.forall_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Set.Definable`。
形式化陈述：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language} [inst : L.Structure M
] {α : Type u₁} {β : Type u_1} [Finite β]   {S : Set (α ⊕ β → M)}, A.Definable L
 S → A.Definable L {v | ∀ (u : β → M), Sum.elim v u ∈ S}
参数：α ⊕ β → M；u : β → M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Finite universal quantifiers preserve definablity.
-/
lemma Definable.forall_of_finite [Finite β] {S : Set ((α ⊕ β) → M)}
    (hS : A.Definable L S) :
    A.Definable L { v : α → M | ∀ u : β → M, Sum.elim v u ∈ S } := by
  obtain ⟨φ, hφ⟩ := hS
  exists φ.iAlls β
  ext v
  simp [hφ]

variable (L A)

/-- A 1-dimensional version of `Definable`, for `Set M`. -/
/-
**Set.Definable** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：Definable (s : Set (α -> M)) : Prop
参数：s : Set (α -> M)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A 1-dimensional version of `Definable`, for `Set M`.
-/
def Definable₁ (s : Set M) : Prop :=
  A.Definable L { x : Fin 1 → M | x 0 ∈ s }

/-- A 2-dimensional version of `Definable`, for `Set (M × M)`. -/
/-
**Set.Definable** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：Definable (s : Set (α -> M)) : Prop
参数：s : Set (α -> M)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A 2-dimensional version of `Definable`, for `Set (M × M)`.
-/
def Definable₂ (s : Set (M × M)) : Prop :=
  A.Definable L { x : Fin 2 → M | (x 0, x 1) ∈ s }

/-- A singleton is definable by parameter as itself. -/
/-
**Set.Definable.singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set.Definable`。
形式化陈述：∀ {M : Type w} (L : FirstOrder.Language) [inst : L.Structure M] (a : M), {
a}.Definable₁ L {a}
参数：L : FirstOrder.Language；a : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
A singleton is definable by parameter as itself.
-/
theorem Definable.singleton (a : M) :
    ({a} : Set M).Definable₁ L {a} := by
  exists (Term.var 0).equal (L.con (⟨a, rfl⟩ : ↑({a} : Set M))).term

/-- A singleton `{a}` is definable over any set `A` that contains `a`. -/
/-
**Set.Definable.singleton_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set.Definable`。
形式化陈述：∀ {M : Type w} (L : FirstOrder.Language) [inst : L.Structure M] {a : M} {A
 : Set M}, a ∈ A → A.Definable₁ L {a}
参数：L : FirstOrder.Language。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Definable.mono`：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language}
 [inst : L.Structure M] {α : Type u₁} {B : Set M} {s : Set (α → M)},   A.Definab
le L s →…
· 使用定理 `Set.Definable.singleton`：∀ {M : Type w} (L : FirstOrder.Language) [inst 
: L.Structure M] (a : M), {a}.Definable₁ L {a}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s

--- 原说明 ---
A singleton `{a}` is definable over any set `A` that contains `a`.
-/
theorem Definable.singleton_of_mem {a : M} {A : Set M} (ha : a ∈ A) :
    A.Definable₁ L {a} :=
  (Definable.singleton L a).mono (Set.singleton_subset_iff.mpr ha)

/-- The 2-dimensional diagonal is definable independent from parameters. -/
/-
**Set.Definable.diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Set.Definable`。
形式化陈述：∀ {M : Type w} (L : FirstOrder.Language) [inst : L.Structure M] (A : Set M
), A.Definable₂ L (Set.diagonal M)
参数：L : FirstOrder.Language；A : Set M；Set.diagonal M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
The 2-dimensional diagonal is definable independent from parameters.
-/
theorem Definable.diagonal (A : Set M) :
    A.Definable₂ L (diagonal M) := by
  exists (Term.var 0).equal (Term.var 1)

end Set

namespace FirstOrder

namespace Language

open Set

variable (L : FirstOrder.Language.{u, v}) {M : Type w} [L.Structure M] (A : Set M) (α : Type u₁)

/-- Definable sets are subsets of finite Cartesian products of a structure such that membership is
  given by a first-order formula. -/
/-
**FirstOrder.Language.DefinableSet** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Languag
e`。
形式化陈述：DefinableSet
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Definable sets are subsets of finite Cartesian products of a structure such that
 membership is
  given by a first-order formula.
-/
def DefinableSet :=
  { s : Set (α → M) // A.Definable L s }

namespace DefinableSet

variable {L A α}
variable {s t : L.DefinableSet A α} {x : α → M}

/-
**FirstOrder.Language.DefinableSet.instSetLike** 是 Mathlib 中的一个实例，位于命名空间 `FirstO
rder.Language.DefinableSet`。
形式化陈述：instSetLike : SetLike (L.DefinableSet A α) (α -> M) where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSetLike : SetLike (L.DefinableSet A α) (α → M) where
  coe := Subtype.val
  coe_injective := Subtype.val_injective
/-
**FirstOrder.Language.DefinableSet.** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.Langua
ge.DefinableSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (L.DefinableSet A α) := .ofSetLike (L.DefinableSet A α) (α → M)
/-
**FirstOrder.Language.DefinableSet.instTop** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder
.Language.DefinableSet`。
形式化陈述：instTop : Top (L.DefinableSet A α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.definable_univ`：definable_univ : A.Definable L (univ : Set (α -> M))
-/
instance instTop : Top (L.DefinableSet A α) :=
  ⟨⟨⊤, definable_univ⟩⟩
/-
**FirstOrder.Language.DefinableSet.instBot** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder
.Language.DefinableSet`。
形式化陈述：instBot : Bot (L.DefinableSet A α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.definable_empty`：definable_empty : A.Definable L (∅ : Set (α -> M))
-/
instance instBot : Bot (L.DefinableSet A α) :=
  ⟨⟨⊥, definable_empty⟩⟩
/-
**FirstOrder.Language.DefinableSet.instSup** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder
.Language.DefinableSet`。
形式化陈述：instSup : Max (L.DefinableSet A α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSup : Max (L.DefinableSet A α) :=
  ⟨fun s t => ⟨s ∪ t, s.2.union t.2⟩⟩
/-
**FirstOrder.Language.DefinableSet.instInf** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder
.Language.DefinableSet`。
形式化陈述：instInf : Min (L.DefinableSet A α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInf : Min (L.DefinableSet A α) :=
  ⟨fun s t => ⟨s ∩ t, s.2.inter t.2⟩⟩
/-
**FirstOrder.Language.DefinableSet.instCompl** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrd
er.Language.DefinableSet`。
形式化陈述：instCompl : Compl (L.DefinableSet A α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCompl : Compl (L.DefinableSet A α) :=
  ⟨fun s => ⟨sᶜ, s.2.compl⟩⟩
/-
**FirstOrder.Language.DefinableSet.instSDiff** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrd
er.Language.DefinableSet`。
形式化陈述：instSDiff : SDiff (L.DefinableSet A α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSDiff : SDiff (L.DefinableSet A α) :=
  ⟨fun s t => ⟨s \ t, s.2.sdiff t.2⟩⟩

-- Why does it complain that `s ⇨ t` is noncomputable?
/-
**FirstOrder.Language.DefinableSet.instHImp** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrde
r.Language.DefinableSet`。
形式化陈述：instHImp : HImp (L.DefinableSet A α) where himp s t
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instHImp : HImp (L.DefinableSet A α) where
  himp s t := ⟨s ⇨ t, s.2.himp t.2⟩
/-
**FirstOrder.Language.DefinableSet.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `Firs
tOrder.Language.DefinableSet`。
形式化陈述：instInhabited : Inhabited (L.DefinableSet A α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited (L.DefinableSet A α) :=
  ⟨⊥⟩
/-
**FirstOrder.Language.DefinableSet.le_iff** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language.DefinableSet`。
形式化陈述：le_iff : s <= t ↔ (s : Set (α -> M)) <= (t : Set (α -> M))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_iff : s ≤ t ↔ (s : Set (α → M)) ≤ (t : Set (α → M)) :=
  Iff.rfl

@[simp]
/-
**FirstOrder.Language.DefinableSet.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.DefinableSet`。
形式化陈述：mem_top : x in (⊤ : L.DefinableSet A α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem mem_top : x ∈ (⊤ : L.DefinableSet A α) :=
  mem_univ x

@[simp]
/-
**FirstOrder.Language.DefinableSet.notMem_bot** 是 Mathlib 中的一个定理，位于命名空间 `FirstOr
der.Language.DefinableSet`。
形式化陈述：notMem_bot {x : α -> M} : x ∉ (⊥ : L.DefinableSet A α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
-/
theorem notMem_bot {x : α → M} : x ∉ (⊥ : L.DefinableSet A α) :=
  notMem_empty x

@[simp]
/-
**FirstOrder.Language.DefinableSet.mem_sup** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.DefinableSet`。
形式化陈述：mem_sup : x in s ⊔ t ↔ x in s ∨ x in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_sup : x ∈ s ⊔ t ↔ x ∈ s ∨ x ∈ t :=
  Iff.rfl

@[simp]
/-
**FirstOrder.Language.DefinableSet.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.DefinableSet`。
形式化陈述：mem_inf : x in s ⊓ t ↔ x in s ∧ x in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inf : x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t :=
  Iff.rfl

@[simp]
/-
**FirstOrder.Language.DefinableSet.mem_compl** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.DefinableSet`。
形式化陈述：mem_compl : x in sᶜ ↔ x ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_compl : x ∈ sᶜ ↔ x ∉ s :=
  Iff.rfl

@[simp]
/-
**FirstOrder.Language.DefinableSet.mem_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.DefinableSet`。
形式化陈述：mem_sdiff : x in s \ t ↔ x in s ∧ x ∉ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_sdiff : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t :=
  Iff.rfl

@[simp, norm_cast]
/-
**FirstOrder.Language.DefinableSet.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.DefinableSet`。
形式化陈述：coe_top : ((⊤ : L.DefinableSet A α) : Set (α -> M)) = univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : ((⊤ : L.DefinableSet A α) : Set (α → M)) = univ :=
  rfl

@[simp, norm_cast]
/-
**FirstOrder.Language.DefinableSet.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.DefinableSet`。
形式化陈述：coe_bot : ((⊥ : L.DefinableSet A α) : Set (α -> M)) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot : ((⊥ : L.DefinableSet A α) : Set (α → M)) = ∅ :=
  rfl

@[simp, norm_cast]
/-
**FirstOrder.Language.DefinableSet.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.DefinableSet`。
形式化陈述：coe_sup (s t : L.DefinableSet A α) : ((s ⊔ t : L.DefinableSet A α) : Set (
α -> M)) = (s : Set (α -> M)) union (t : Set (α -> M))
参数：s t : L.DefinableSet A α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup (s t : L.DefinableSet A α) :
    ((s ⊔ t : L.DefinableSet A α) : Set (α → M)) = (s : Set (α → M)) ∪ (t : Set (α → M)) :=
  rfl

@[simp, norm_cast]
/-
**FirstOrder.Language.DefinableSet.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder
.Language.DefinableSet`。
形式化陈述：coe_inf (s t : L.DefinableSet A α) : ((s ⊓ t : L.DefinableSet A α) : Set (
α -> M)) = (s : Set (α -> M)) inter (t : Set (α -> M))
参数：s t : L.DefinableSet A α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf (s t : L.DefinableSet A α) :
    ((s ⊓ t : L.DefinableSet A α) : Set (α → M)) = (s : Set (α → M)) ∩ (t : Set (α → M)) :=
  rfl

@[simp, norm_cast]
/-
**FirstOrder.Language.DefinableSet.coe_compl** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.DefinableSet`。
形式化陈述：coe_compl (s : L.DefinableSet A α) : ((sᶜ : L.DefinableSet A α) : Set (α -
> M)) = (s : Set (α -> M))ᶜ
参数：s : L.DefinableSet A α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_compl (s : L.DefinableSet A α) :
    ((sᶜ : L.DefinableSet A α) : Set (α → M)) = (s : Set (α → M))ᶜ :=
  rfl

@[simp, norm_cast]
/-
**FirstOrder.Language.DefinableSet.coe_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrd
er.Language.DefinableSet`。
形式化陈述：coe_sdiff (s t : L.DefinableSet A α) : ((s \ t : L.DefinableSet A α) : Set
 (α -> M)) = (s : Set (α -> M)) \ (t : Set (α -> M))
参数：s t : L.DefinableSet A α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sdiff (s t : L.DefinableSet A α) :
    ((s \ t : L.DefinableSet A α) : Set (α → M)) = (s : Set (α → M)) \ (t : Set (α → M)) :=
  rfl

@[simp, norm_cast]
/-
**FirstOrder.Language.DefinableSet.coe_himp** 是 Mathlib 中的一个引理，位于命名空间 `FirstOrde
r.Language.DefinableSet`。
形式化陈述：coe_himp (s t : L.DefinableSet A α) : ↑(s ⇨ t) = (s ⇨ t : Set (α -> M))
参数：s t : L.DefinableSet A α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_himp (s t : L.DefinableSet A α) : ↑(s ⇨ t) = (s ⇨ t : Set (α → M)) := rfl
/-
**FirstOrder.Language.DefinableSet.instBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 
`FirstOrder.Language.DefinableSet`。
形式化陈述：instBooleanAlgebra : BooleanAlgebra (L.DefinableSet A α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.DefinableSet.coe_sup`：coe_sup (s t : L.DefinableSet 
A α) : ((s ⊔ t : L.DefinableSet A α) : Set (α -> M)) = (s : Set (α -> M)) union 
(t : Set (α -> M))
· 使用定理 `FirstOrder.Language.DefinableSet.coe_inf`：coe_inf (s t : L.DefinableSet 
A α) : ((s ⊓ t : L.DefinableSet A α) : Set (α -> M)) = (s : Set (α -> M)) inter 
(t : Set (α -> M))
· 使用定理 `FirstOrder.Language.DefinableSet.coe_top`：coe_top : ((⊤ : L.DefinableSet
 A α) : Set (α -> M)) = univ
· 使用定理 `FirstOrder.Language.DefinableSet.coe_bot`：coe_bot : ((⊥ : L.DefinableSet
 A α) : Set (α -> M)) = ∅
· 使用定理 `FirstOrder.Language.DefinableSet.coe_compl`：coe_compl (s : L.DefinableSe
t A α) : ((sᶜ : L.DefinableSet A α) : Set (α -> M)) = (s : Set (α -> M))ᶜ
· 使用定理 `FirstOrder.Language.DefinableSet.coe_sdiff`：coe_sdiff (s t : L.Definable
Set A α) : ((s \ t : L.DefinableSet A α) : Set (α -> M)) = (s : Set (α -> M)) \ 
(t : Set (α -> M))
· 使用引理 `FirstOrder.Language.DefinableSet.coe_himp`：coe_himp (s t : L.DefinableSe
t A α) : ↑(s ⇨ t) = (s ⇨ t : Set (α -> M))
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
/-
**Set.DefinableFun** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：DefinableFun (f : (α -> M) -> M) : Prop
参数：f : (α -> M) -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function from tuples of elements of `M` to `M` is definable if its graph is de
finable.
-/
def DefinableFun (f : (α → M) → M) : Prop :=
  A.Definable L f.tupleGraph

/-- A family of functions is definable when each coordinate is definable. -/
/-
**Set.DefinableMap** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：DefinableMap (F : (α -> M) -> (β -> M)) : Prop
参数：F : (α -> M) -> (β -> M)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of functions is definable when each coordinate is definable.
-/
def DefinableMap (F : (α → M) → (β → M)) : Prop :=
  ∀ i : β, A.DefinableFun L (fun x => F x i)

variable {L A} {f : (α → M) → M}

@[fun_prop, gcongr]
/-
**Set.DefinableFun.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.DefinableFun`。
形式化陈述：∀ {M : Type u_1} {L : FirstOrder.Language} [inst : L.Structure M] {α : Typ
e u_2} {A : Set M} {f : (α → M) → M}   {B : Set M}, Set.DefinableFun L A f → A ⊆
 B → Set.DefinableFun L B f
参数：α → M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Definable.mono`：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language}
 [inst : L.Structure M] {α : Type u₁} {B : Set M} {s : Set (α → M)},   A.Definab
le L s →…
-/
theorem DefinableFun.mono {B : Set M} (hAs : A.DefinableFun L f) (hAB : A ⊆ B) :
    B.DefinableFun L f :=
  Set.Definable.mono hAs hAB

@[fun_prop]
/-
**Set.DefinableFun.of_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set.DefinableFun`。
形式化陈述：∀ {M : Type u_1} {L : FirstOrder.Language} [inst : L.Structure M] {α : Typ
e u_2} {A : Set M} {f : (α → M) → M},   Set.DefinableFun L ∅ f → Set.DefinableFu
n L A f
参数：α → M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Definable.mono`：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language}
 [inst : L.Structure M] {α : Type u₁} {B : Set M} {s : Set (α → M)},   A.Definab
le L s →…
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
theorem DefinableFun.of_empty (hAs : (∅ : Set M).DefinableFun L f) :
    A.DefinableFun L f := Set.Definable.mono hAs (empty_subset A)
/-
**Set.empty_definableFun_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：empty_definableFun_iff : (∅ : Set M).DefinableFun L f ↔ exists φ : L.Formu
la (Option α), f.tupleGraph = Set.ofPred φ.Realize
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem empty_definableFun_iff :
    (∅ : Set M).DefinableFun L f ↔
      ∃ φ : L.Formula (Option α), f.tupleGraph = Set.ofPred φ.Realize := by
  simp [DefinableFun, Set.empty_definable_iff]
/-
**Set.definableFun_iff_empty_definableFun_with_params** 是 Mathlib 中的一个定理，位于命名空间 
`Set`。
形式化陈述：definableFun_iff_empty_definableFun_with_params : A.DefinableFun L f ↔ (∅ 
: Set M).DefinableFun (L[[A]]) f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.empty_definable_iff`：empty_definable_iff : (∅ : Set M).Definable L s
 ↔ exists φ : L.Formula α, s = Set.ofPred φ.Realize
-/
theorem definableFun_iff_empty_definableFun_with_params :
    A.DefinableFun L f ↔ (∅ : Set M).DefinableFun (L[[A]]) f :=
  empty_definable_iff.symm

/-- A term is a definable function. -/
@[fun_prop]
/-
**Set._root_.FirstOrder.Language.Term.definableFun_realize** 是 Mathlib 中的一个定理，位于
命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A term is a definable function.
-/
theorem _root_.FirstOrder.Language.Term.definableFun_realize (t : L.Term α) :
    (∅ : Set M).DefinableFun L (t.realize) := by
  rw [empty_definableFun_iff]
  refine ⟨(t.relabel some).equal (Term.var none), ?_⟩
  ext v
  simp [tupleGraph]

/-- A function symbol is a definable function. -/
@[fun_prop]
/-
**Set.DefinableFun.fun_symbol** 是 Mathlib 中的一个定理，位于命名空间 `Set.DefinableFun`。
形式化陈述：∀ {M : Type u_1} {L : FirstOrder.Language} [inst : L.Structure M] {n : ℕ} 
(f : L.Functions n),   Set.DefinableFun L ∅ (FirstOrder.Language.Structure.funMa
p f)
参数：f : L.Functions n；FirstOrder.Language.Structure.funMap f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Term.definableFun_realize`：∀ {M : Type u_1} {L : Fir
stOrder.Language} [inst : L.Structure M] {α : Type u_2} (t : L.Term α),   Set.De
finableFun L ∅ fun v => FirstOrder.…

--- 原说明 ---
A function symbol is a definable function.
-/
theorem DefinableFun.fun_symbol {n : ℕ} (f : L.Functions n) :
    (∅ : Set M).DefinableFun L (Structure.funMap f) :=
  (Term.func f Term.var).definableFun_realize

variable (L)

/-- A coordinate projection is a definable function. -/
@[fun_prop]
/-
**Set._root_.FirstOrder.Language.definableFun_var** 是 Mathlib 中的一个定理，位于命名空间 `Set
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coordinate projection is a definable function.
-/
theorem _root_.FirstOrder.Language.definableFun_var (i : α) :
    (∅ : Set M).DefinableFun L (fun v => v i) :=
  (Term.var i).definableFun_realize

@[fun_prop]
/-
**Set.DefinableFun.proj** 是 Mathlib 中的一个定理，位于命名空间 `Set.DefinableFun`。
形式化陈述：∀ {M : Type u_1} (L : FirstOrder.Language) [inst : L.Structure M] {α : Typ
e u_2} {A : Set M} {i : α},   Set.DefinableFun L A fun v => v i
参数：L : FirstOrder.Language。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.DefinableFun.of_empty`：∀ {M : Type u_1} {L : FirstOrder.Language} [i
nst : L.Structure M] {α : Type u_2} {A : Set M} {f : (α → M) → M},   Set.Definab
leFun L ∅ f → S…
· 使用定理 `FirstOrder.Language.definableFun_var`：∀ {M : Type u_1} (L : FirstOrder.L
anguage) [inst : L.Structure M] {α : Type u_2} (i : α),   Set.DefinableFun L ∅ f
un v => v i
-/
theorem DefinableFun.proj {i : α} : A.DefinableFun L fun v => v i :=
  of_empty <| L.definableFun_var i

/-- A constant function is a definable function. -/
@[fun_prop]
/-
**Set._root_.FirstOrder.Language.definableFun_const** 是 Mathlib 中的一个定理，位于命名空间 `S
et`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constant function is a definable function.
-/
theorem _root_.FirstOrder.Language.definableFun_const {A : Set M} {a : M}
    (γ : Type*) (ha : a ∈ A) :
    A.DefinableFun L (fun _ : γ → M => a) := by
  rw [definableFun_iff_empty_definableFun_with_params]
  exact ((L.con (⟨a,ha⟩ : ↑A)).term).definableFun_realize

variable {L}

/-- The preimage of a definable set under a definable map is definable. -/
/-
**Set._root_.Set.Definable.preimage_map** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of a definable set under a definable map is definable.
-/
lemma _root_.Set.Definable.preimage_map
    {α β : Type*} [Finite β] {F : (α → M) → (β → M)} (hF : A.DefinableMap L F)
    {S : Set (β → M)} (hS : A.Definable L S) :
    A.Definable L (F ⁻¹' S) := by
  have h_graph : A.Definable L { w : α ⊕ β → M | ∀ i, F (w ∘ Sum.inl) i = w (Sum.inr i) } := by
    rw [ofPred_forall]
    refine definable_iInter_of_finite fun i => ?_
    simpa [tupleGraph] using!
      (hF i).preimage_comp (fun | none => Sum.inr i | some j => Sum.inl j)
  have h_cyl : A.Definable L { w : α ⊕ β → M | w ∘ Sum.inr ∈ S } :=
    hS.preimage_comp Sum.inr
  convert! Definable.exists_of_finite (Definable.inter h_graph h_cyl) using 1
  ext v
  simp [← funext_iff]

@[fun_prop]
/-
**Set.DefinableFun.comp** 是 Mathlib 中的一个定理，位于命名空间 `Set.DefinableFun`。
形式化陈述：∀ {M : Type u_1} {L : FirstOrder.Language} [inst : L.Structure M] {α : Typ
e u_2} {β : Type u_3} {A : Set M}   {f : (α → M) → M} [Finite α] {g : (β → M) → 
α → M},   Set.DefinableMap L A g → Set.DefinableFun L A f → Set.DefinableFun L A
 fun v => f (g v)
参数：α → M；β → M；g v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.DefinableFun.proj`：∀ {M : Type u_1} (L : FirstOrder.Language) [inst 
: L.Structure M] {α : Type u_2} {A : Set M} {i : α},   Set.DefinableFun L A fun 
v => v i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Definable.preimage_comp`：∀ {M : Type w} {A : Set M} {L : FirstOrder.
Language} [inst : L.Structure M] {α : Type u₁} {β : Type u_1} (f : α → β)   {s :
 Set (α → M)}, A.…
· 使用定理 `Set.Definable.preimage_map`：∀ {M : Type u_1} {L : FirstOrder.Language} [
inst : L.Structure M] {A : Set M} {α : Type u_4} {β : Type u_5} [Finite β]   {F 
: (α → M) → β → …
· 使用定理 `instFiniteOption`：∀ {α : Type u_3} [Finite α], Finite (Option α)
-/
theorem DefinableFun.comp [Finite α] {g : (β → M) → α → M}
    (hg : A.DefinableMap L g) (hf : A.DefinableFun L f) :
    A.DefinableFun L fun v => f (g v) := by
  let G : (Option β → M) → Option α → M := fun w j =>
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
/-
**Set.DefinableFun.ite** 是 Mathlib 中的一个定理，位于命名空间 `Set.DefinableFun`。
形式化陈述：∀ {M : Type u_1} {L : FirstOrder.Language} [inst : L.Structure M] {α : Typ
e u_2} {A : Set M} {f : (α → M) → M}   {p : (α → M) → Prop} {g : (α → M) → M} [i
nst_1 : DecidablePred p],   A.Definable L (Set.ofPred p) →     Set.DefinableFun 
L A f → Set.DefinableFun L A g → Set.DefinableFun L A fun v => if p v then f v e
lse g v
参数：α → M；α → M；α → M；Set.ofPred p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Definable.preimage_comp`：∀ {M : Type w} {A : Set M} {L : FirstOrder.
Language} [inst : L.Structure M] {α : Type u₁} {β : Type u_1} (f : α → β)   {s :
 Set (α → M)}, A.…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Set.Definable.union`：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language
} [inst : L.Structure M] {α : Type u₁} {f g : Set (α → M)},   A.Definable L f → 
A.Definab…
· 使用定理 `Set.Definable.inter`：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language
} [inst : L.Structure M] {α : Type u₁} {f g : Set (α → M)},   A.Definable L f → 
A.Definab…
· 使用定理 `Set.Definable.compl`：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language
} [inst : L.Structure M] {α : Type u₁} {s : Set (α → M)},   A.Definable L s → A.
Definable…
-/
theorem DefinableFun.ite {p : (α → M) → Prop} {g} [DecidablePred p]
    (hp : A.Definable L (Set.ofPred p)) (hf : DefinableFun L A f) (hg : DefinableFun L A g) :
    DefinableFun L A fun v => if p v then f v else g v := by
  let P : Set (Option α → M) := {w | p (w ∘ some)}
  have hP : A.Definable L P := hp.preimage_comp some
  simp only [DefinableFun]
  convert! (hP.inter hf).union (hP.compl.inter hg)
  ext w
  by_cases h : p (w ∘ some) <;> simp [tupleGraph, P, h]

/-- The set where two definable functions agree is definable. -/
/-
**Set.DefinableFun.ofPred_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set.DefinableFun`。
形式化陈述：∀ {M : Type u_1} {L : FirstOrder.Language} [inst : L.Structure M] {α : Typ
e u_2} {A : Set M} {f g : (α → M) → M},   Set.DefinableFun L A f → Set.Definable
Fun L A g → A.Definable L {v | f v = g v}
参数：α → M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.Definable.preimage_map`：∀ {M : Type u_1} {L : FirstOrder.Language} [
inst : L.Structure M] {A : Set M} {α : Type u_4} {β : Type u_5} [Finite β]   {F 
: (α → M) → β → …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Set.Definable.diagonal`：∀ {M : Type w} (L : FirstOrder.Language) [inst :
 L.Structure M] (A : Set M), A.Definable₂ L (Set.diagonal M)

--- 原说明 ---
The set where two definable functions agree is definable.
-/
lemma DefinableFun.ofPred_eq {f g : (α → M) → M}
    (hf : A.DefinableFun L f) (hg : A.DefinableFun L g) :
    A.Definable L {v : α → M | f v = g v} := by
  have hF : A.DefinableMap L (fun v => ![f v, g v]) := by
    simp [DefinableMap, *]
  exact (Definable.diagonal L A).preimage_map hF

@[deprecated (since := "2026-07-09")]
alias DefinableFun.setOf_eq := DefinableFun.ofPred_eq

/-- The preimage of a constant under a definable function is definable. -/
/-
**Set.DefinableFun.ofPred_eq_const** 是 Mathlib 中的一个定理，位于命名空间 `Set.DefinableFun`。
形式化陈述：∀ {M : Type u_1} {L : FirstOrder.Language} [inst : L.Structure M] {α : Typ
e u_2} {A : Set M} {f : (α → M) → M},   Set.DefinableFun L A f → ∀ {a : M}, a ∈ 
A → A.Definable L {v | f v = a}
参数：α → M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.DefinableFun.ofPred_eq`：∀ {M : Type u_1} {L : FirstOrder.Language} [
inst : L.Structure M] {α : Type u_2} {A : Set M} {f g : (α → M) → M},   Set.Defi
nableFun L A f →…
· 使用定理 `FirstOrder.Language.definableFun_const`：∀ {M : Type u_1} (L : FirstOrder
.Language) [inst : L.Structure M] {A : Set M} {a : M} (γ : Type u_4),   a ∈ A → 
Set.DefinableFun L A fun x =…

--- 原说明 ---
The preimage of a constant under a definable function is definable.
-/
lemma DefinableFun.ofPred_eq_const {f : (α → M) → M} (hf : A.DefinableFun L f) {a : M}
    (ha : a ∈ A) :
    A.Definable L {v : α → M | f v = a} :=
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
/-
**Set.TermDefinable** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：TermDefinable (f : (α -> M) -> M) : Prop
参数：f : (α -> M) -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function from a Cartesian power of a structure to that structure is term-defin
able over
a set `A` when the value of the function is given by a term with constants `A`.
-/
def TermDefinable (f : (α → M) → M) : Prop :=
  ∃ φ : L[[A]].Term α, f = φ.realize

/-- Every TermDefinable function has a tupleGraph that is definable. -/
/-
**Set.TermDefinable.definable_tupleGraph** 是 Mathlib 中的一个定理，位于命名空间 `Set.TermDefi
nable`。
形式化陈述：∀ {M : Type w} (A : Set M) (L : FirstOrder.Language) [inst : L.Structure M
] {α : Type u₁} {f : (α → M) → M},   A.TermDefinable L f → A.Definable L (Functi
on.tupleGraph f)
参数：A : Set M；L : FirstOrder.Language；α → M；Function.tupleGraph f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FirstOrder.Language.Term.realize_relabel`：realize_relabel {t : L.Term α}
 {g : α -> β} {v : β -> M} : (t.relabel g).realize v = t.realize (v ∘ g)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Every TermDefinable function has a tupleGraph that is definable.
-/
theorem TermDefinable.definable_tupleGraph {f : (α → M) → M} (h : A.TermDefinable L f) :
    A.Definable L f.tupleGraph := by
  obtain ⟨φ, rfl⟩ := h
  use (φ.relabel some).equal (Term.var none)
  ext
  simp [Function.tupleGraph]

variable {L} {A B} {f : (α → M) → M}

@[fun_prop]
/-
**Set.TermDefinable.map_expansion** 是 Mathlib 中的一个定理，位于命名空间 `Set.TermDefinable`。
形式化陈述：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language} {L' : FirstOrder.Lang
uage} [inst : L.Structure M]   [inst_1 : L'.Structure M] {α : Type u₁} {f : (α →
 M) → M},   A.TermDefinable L f → ∀ (φ : L →ᴸ L') [φ.IsExpansionOn M], A.TermDef
inable L' f
参数：α → M；φ : L →ᴸ L'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.LHom.realize_onTerm`：realize_onTerm [L'.Structure M]
 (φ : L ->ᴸ L') [φ.IsExpansionOn M] (t : L.Term α) (v : α -> M) : (φ.onTerm t).r
ealize v = t.realize v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem TermDefinable.map_expansion (h : A.TermDefinable L f) (φ : L →ᴸ L') [φ.IsExpansionOn M] :
    A.TermDefinable L' f := by
  obtain ⟨ψ, rfl⟩ := h
  use (φ.addConstants A).onTerm ψ
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**Set.termDefinable_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：termDefinable_empty_iff : (∅ : Set M).TermDefinable L f ↔ exists φ : L.Ter
m α, f = φ.realize
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.TermDefinable.eq_1`：∀ {M : Type w} (A : Set M) (L : FirstOrder.Langu
age) [inst : L.Structure M] {α : Type u₁} (f : (α → M) → M),   A.TermDefinable L
 f = ∃ φ, f …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.instIsAlgebraicConstantsOn`：∀ (α : Type u_1), (First
Order.Language.constantsOn α).IsAlgebraic
· 使用定理 `FirstOrder.Language.LEquiv.onTerm_symm_apply`：∀ {L : FirstOrder.Language
} {L' : FirstOrder.Language} {α : Type u'} (φ : L ≃ᴸ L') (a : L'.Term α),   φ.on
Term.symm a = φ.invLHom.onTerm a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FirstOrder.Language.LEquiv.addEmptyConstants_invLHom`：∀ (L : FirstOrder.
Language) (α : Type w') [ie : IsEmpty α],   (FirstOrder.Language.LEquiv.addEmpty
Constants L α).invLHom =     (FirstOrder.L…
· 使用定理 `FirstOrder.Language.LHom.realize_onTerm`：realize_onTerm [L'.Structure M]
 (φ : L ->ᴸ L') [φ.IsExpansionOn M] (t : L.Term α) (v : α -> M) : (φ.onTerm t).r
ealize v = t.realize v
· 使用定理 `FirstOrder.Language.LHom.ofIsEmpty_isExpansionOn`：∀ {L : FirstOrder.Lang
uage} {L' : FirstOrder.Language} (M : Type u_1) [inst : L.Structure M] [inst_1 :
 L'.Structure M]   [inst_2 : L.IsAlgeb…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem termDefinable_empty_iff :
    (∅ : Set M).TermDefinable L f ↔ ∃ φ : L.Term α, f = φ.realize := by
  rw [TermDefinable, Equiv.exists_congr_left (LEquiv.addEmptyConstants L (∅ : Set M)).onTerm]
  simp
/-
**Set.termDefinable_empty_withConstants_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：termDefinable_empty_withConstants_iff : (∅ : Set M).TermDefinable L[[A]] f
 ↔ A.TermDefinable L f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.termDefinable_empty_iff`：termDefinable_empty_iff : (∅ : Set M).TermD
efinable L f ↔ exists φ : L.Term α, f = φ.realize
-/
theorem termDefinable_empty_withConstants_iff :
    (∅ : Set M).TermDefinable L[[A]] f ↔ A.TermDefinable L f :=
  termDefinable_empty_iff

@[fun_prop]
/-
**Set.TermDefinable.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.TermDefinable`。
形式化陈述：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language} [inst : L.Structure M
] {α : Type u₁} {B : Set M} {f : (α → M) → M},   A.TermDefinable L f → A ⊆ B → B
.TermDefinable L f
参数：α → M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.termDefinable_empty_withConstants_iff`：termDefinable_empty_withConst
ants_iff : (∅ : Set M).TermDefinable L[[A]] f ↔ A.TermDefinable L f
· 使用定理 `Set.TermDefinable.map_expansion`：∀ {M : Type w} {A : Set M} {L : FirstOr
der.Language} {L' : FirstOrder.Language} [inst : L.Structure M]   [inst_1 : L'.S
tructure M] {α : Type…
-/
theorem TermDefinable.mono {f : (α → M) → M} (h : A.TermDefinable L f) (hAB : A ⊆ B) :
    B.TermDefinable L f := by
  rw [← termDefinable_empty_withConstants_iff] at h ⊢
  exact h.map_expansion (L.lhomWithConstantsMap (Set.inclusion hAB))

/-- TermDefinable is transitive. If f is TermDefinable in a structure S on L, and all of the
functions' realizations on S are TermDefinable on a structure T on L', then f is
TermDefinable on T in L'. -/
@[fun_prop]
/-
**Set.TermDefinable.trans** 是 Mathlib 中的一个定理，位于命名空间 `Set.TermDefinable`。
形式化陈述：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language} {L' : FirstOrder.Lang
uage} [inst : L.Structure M]   [inst_1 : L'.Structure M] {β : Type u_1} {f : (β 
→ M) → M},   A.TermDefinable L f →     (∀ {n : ℕ} (g : (L.withConstants ↑A).Func
tions n),         A.TermDefinable L' fun v => FirstOrder.Language.Term.realize v
 g.term) →       A.TermDefinable L' f
参数：β → M；∀ {n : ℕ} (g : (L.withConstants ↑A).Functions n),         A.TermDefinab
le L' fun v => FirstOrder.Language.Term.realize v g.term。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.Term.realize_substFunc`：realize_substFunc [L'.Struct
ure M] {c : {n : Nat} -> L.Functions n -> L'.Term (Fin n)} (hc : forall {n : Nat
} (g) (y : Fin n -> M), g.term.r…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
TermDefinable is transitive. If f is TermDefinable in a structure S on L, and al
l of the
functions' realizations on S are TermDefinable on a structure T on L', then f is
TermDefinable on T in L'.
-/
theorem TermDefinable.trans {f : (β → M) → M} (h₁ : A.TermDefinable L f)
    (h₂ : ∀ {n} (g : L[[A]].Functions n), A.TermDefinable L' g.term.realize) :
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
/-
**Set.TermDefinable** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：TermDefinable (f : (α -> M) -> M) : Prop
参数：f : (α -> M) -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function from a structure to itself is term-definable over a set `A` when the
value of the function is given by a term with constants `A`. Like `TermDefinable
`
but specialized for unary functions in order to write `M → M` instead of `(Unit 
→ M) → M`.
-/
def TermDefinable₁ (f : M → M) : Prop :=
  A.TermDefinable L fun x ↦ (f (x ()))

/-- `TermDefinable₁` is defined as `TermDefinable` on the `Unit` index type. -/
/-
**Set.termDefinable** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`TermDefinable₁` is defined as `TermDefinable` on the `Unit` index type.
-/
theorem termDefinable₁_iff_termDefinable (f : M → M) : A.TermDefinable₁ L f ↔
    A.TermDefinable L (fun v ↦ f (v ())) := by
  rfl

alias ⟨TermDefinable₁.termDefinable, TermDefinable.termDefinable₁⟩ :=
  termDefinable₁_iff_termDefinable

attribute [fun_prop] TermDefinable.termDefinable₁
/-
**Set.termDefinable** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem termDefinable₁_iff_exists_term {f : M → M} : A.TermDefinable₁ L f ↔
    ∃ φ : L[[A]].Term Unit, f = φ.realize ∘ Function.const _ := by
  refine exists_congr fun φ ↦ ?_
  rw [funext_iff, funext_iff, (Equiv.funUnique Unit M).forall_congr']
  simp only [Equiv.funUnique_symm_apply, uniqueElim_const, Function.comp_apply]
  congr!

/-- A `TermDefinable₁` function has a graph that's `Definable₂`. -/
/-
**Set.TermDefinable** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：TermDefinable (f : (α -> M) -> M) : Prop
参数：f : (α -> M) -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `TermDefinable₁` function has a graph that's `Definable₂`.
-/
theorem TermDefinable₁.definable₂_graph {f : M → M} (h : A.TermDefinable₁ L f) :
    A.Definable₂ L f.graph := by
  obtain ⟨t, h⟩ := h.termDefinable.definable_tupleGraph A L
  use t.relabel (Option.elim · 1 (fun _ ↦ 0))
  ext v
  convert! Set.ext_iff.1 h (v ∘ (Option.elim · 1 (fun _ ↦ 0)))
  simp

/-- The identity function is `TermDefinable₁` -/
@[fun_prop]
/-
**Set.TermDefinable** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：TermDefinable (f : (α -> M) -> M) : Prop
参数：f : (α -> M) -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity function is `TermDefinable₁`
-/
theorem TermDefinable₁.id : A.TermDefinable₁ L id :=
  ⟨Term.var (), rfl⟩

/-- Constant functions are `TermDefinable`, assuming the constant value is a language constant. -/
@[fun_prop]
/-
**Set.TermDefinable.const** 是 Mathlib 中的一个定理，位于命名空间 `Set.TermDefinable`。
形式化陈述：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language} [inst : L.Structure M
] {α : Type u₁}   (C : (L.withConstants ↑A).Constants), A.TermDefinable L (Funct
ion.const (α → M) ↑C)
参数：C : (L.withConstants ↑A).Constants；Function.const (α → M) ↑C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.Term.realize_constants`：realize_constants {c : L.Con
stants} {v : α -> M} : c.term.realize v = c

--- 原说明 ---
Constant functions are `TermDefinable`, assuming the constant value is a languag
e constant.
-/
theorem TermDefinable.const (C : L[[A]].Constants) : A.TermDefinable L (Function.const (α → M) C) :=
  ⟨C.term, by simp only [Term.realize_constants]; rfl⟩

/-- Constant functions are `TermDefinable₁`, assuming the constant value is a language constant. -/
@[fun_prop]
/-
**Set.TermDefinable** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：TermDefinable (f : (α -> M) -> M) : Prop
参数：f : (α -> M) -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constant functions are `TermDefinable₁`, assuming the constant value is a langua
ge constant.
-/
theorem TermDefinable₁.const (C : L[[A]].Constants) : A.TermDefinable₁ L (Function.const M C) :=
  (TermDefinable.const C).termDefinable₁

/-- A k-ary `TermDefinable` function composed with k `TermDefinable` others is `TermDefinable`. -/
/-
**Set.TermDefinable.comp** 是 Mathlib 中的一个定理，位于命名空间 `Set.TermDefinable`。
形式化陈述：∀ {M : Type w} {A : Set M} {L : FirstOrder.Language} [inst : L.Structure M
] {α : Type u₁} {β : Type u_1}   {f : (α → M) → M} {g : α → (β → M) → M},   A.Te
rmDefinable L f → (∀ (i : α), A.TermDefinable L (g i)) → A.TermDefinable L fun b
 => f fun x => g x b
参数：α → M；β → M；∀ (i : α), A.TermDefinable L (g i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `FirstOrder.Language.Term.realize_subst`：realize_subst {t : L.Term α} {tf
 : α -> L.Term β} {v : β -> M} : (t.subst tf).realize v = t.realize fun a => (tf
 a).realize v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A k-ary `TermDefinable` function composed with k `TermDefinable` others is `Term
Definable`.
-/
theorem TermDefinable.comp {f : (α → M) → M} {g : α → (β → M) → M} (hf : A.TermDefinable L f)
    (hg : ∀ i, A.TermDefinable L (g i)) : A.TermDefinable L (fun b ↦ f (g · b)) := by
  obtain ⟨φ, rfl⟩ := hf
  choose ψ hψ using hg
  use φ.subst ψ
  simp [hψ]

/-- `TermDefinable₁` functions are closed under composition. -/
@[fun_prop]
/-
**Set.TermDefinable** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：TermDefinable (f : (α -> M) -> M) : Prop
参数：f : (α -> M) -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`TermDefinable₁` functions are closed under composition.
-/
theorem TermDefinable₁.comp {f g : M → M} (hf : A.TermDefinable₁ L f) (hg : A.TermDefinable₁ L g) :
    A.TermDefinable₁ L (f ∘ g) :=
  (hf.termDefinable.comp fun _ ↦ hg.termDefinable).termDefinable₁

/-- A `TermDefinable` function postcomposed with `TermDefinable₁` is `TermDefinable`. -/
@[fun_prop]
/-
**Set.TermDefinable** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：TermDefinable (f : (α -> M) -> M) : Prop
参数：f : (α -> M) -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `TermDefinable` function postcomposed with `TermDefinable₁` is `TermDefinable`
.
-/
theorem TermDefinable₁.comp_termDefinable {f : M → M} {g : (α → M) → M}
    (hf : A.TermDefinable₁ L f) (hg : A.TermDefinable L g) : A.TermDefinable L (f ∘ g) :=
  hf.termDefinable.comp fun _ ↦ hg

end Set

