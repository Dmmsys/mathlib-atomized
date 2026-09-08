/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic.Algebraize

/-!
# Finiteness conditions in commutative algebra

In this file we define a notion of finiteness that is common in commutative algebra.

## Main declarations

- `Submodule.FG`, `Ideal.FG`
  These express that some object is finitely generated as *submodule* over some base ring.

- `Module.Finite`, `RingHom.Finite`, `AlgHom.Finite`
  all of these express that some object is finitely generated *as module* over some base ring.

-/

@[expose] public section

assert_not_exists Module.Basis Ideal.radical Matrix Subalgebra

open Function (Surjective)

namespace Submodule

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

open Set

/-- A submodule of `M` is finitely generated if it is the span of a finite subset of `M`. -/
/-
**Submodule.FG** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：FG (N : Submodule R M) : Prop
参数：N : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submodule of `M` is finitely generated if it is the span of a finite subset of
 `M`.
-/
def FG (N : Submodule R M) : Prop :=
  ∃ S : Finset M, span R ↑S = N
/-
**Submodule.fg_def** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fg_def {N : Submodule R M} : N.FG ↔ exists S : Set M, S.Finite ∧ span R S 
= N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Set.Finite.exists_finset_coe`：∀ {α : Type u} {s : Set α}, s.Finite → ∃ s
', ↑s' = s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem fg_def {N : Submodule R M} : N.FG ↔ ∃ S : Set M, S.Finite ∧ span R S = N := by
  refine ⟨fun ⟨t, h⟩ => ⟨_, t.finite_toSet, h⟩, ?_⟩
  rintro ⟨t', h, rfl⟩
  have := h.exists_finset_coe
  tauto
/-
**Submodule.fg_iff_addSubmonoid_fg** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fg_iff_addSubmonoid_fg (P : Submodule Nat M) : P.FG ↔ P.toAddSubmonoid.FG
参数：P : Submodule Nat M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem fg_iff_addSubmonoid_fg (P : Submodule ℕ M) : P.FG ↔ P.toAddSubmonoid.FG :=
  ⟨fun ⟨S, hS⟩ => ⟨S, by simpa [← span_nat_eq_addSubmonoidClosure]⟩,
    fun ⟨S, hS⟩ => ⟨S, by simpa [← span_nat_eq_addSubmonoidClosure] using hS⟩⟩
/-
**Submodule.fg_iff_addSubgroup_fg** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：fg_iff_addSubgroup_fg {G : Type*} [AddCommGroup G] (P : Submodule Int G) :
 P.FG ↔ P.toAddSubgroup.FG
参数：P : Submodule Int G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.mk.injEq`：∀ {G : Type u_3} [inst : AddGroup G] (toAddSubmono
id : AddSubmonoid G)   (neg_mem' : ∀ {x : G}, x ∈ toAddSubmonoid.carrier → -x ∈ 
toAddSubmo…
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
-/
theorem fg_iff_addSubgroup_fg {G : Type*} [AddCommGroup G] (P : Submodule ℤ G) :
    P.FG ↔ P.toAddSubgroup.FG :=
  ⟨fun ⟨S, hS⟩ => ⟨S, by simpa [← span_int_eq_addSubgroupClosure]⟩,
    fun ⟨S, hS⟩ => ⟨S, by simpa [← span_int_eq_addSubgroupClosure] using hS⟩⟩
/-
**Submodule.fg_iff_exists_fin_generating_family** 是 Mathlib 中的一个定理，位于命名空间 `Submo
dule`。
形式化陈述：fg_iff_exists_fin_generating_family {N : Submodule R M} : N.FG ↔ exists (n
 : Nat) (s : Fin n -> M), span R (range s) = N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.fg_def`：fg_def {N : Submodule R M} : N.FG ↔ exists S : Set M, 
S.Finite ∧ span R S = N
· 使用定理 `Set.Finite.fin_embedding`：∀ {α : Type u} {s : Set α}, s.Finite → ∃ n f, 
Set.range ⇑f = s
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem fg_iff_exists_fin_generating_family {N : Submodule R M} :
    N.FG ↔ ∃ (n : ℕ) (s : Fin n → M), span R (range s) = N := by
  rw [fg_def]
  constructor
  · rintro ⟨S, Sfin, hS⟩
    obtain ⟨n, f, rfl⟩ := Sfin.fin_embedding
    exact ⟨n, f, hS⟩
  · rintro ⟨n, s, hs⟩
    exact ⟨range s, finite_range s, hs⟩

universe w v u in
/-
**Submodule.fg_iff_exists_finite_generating_family** 是 Mathlib 中的一个引理，位于命名空间 `Su
bmodule`。
形式化陈述：fg_iff_exists_finite_generating_family {A : Type u} [Semiring A] {M : Type
 v} [AddCommMonoid M] [Module A M] {N : Submodule A M} : N.FG ↔ exists (G : Type
 w) (_ : Finite G) (g : G -> M), span A (range g) = N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.fg_iff_exists_fin_generating_family`：fg_iff_exists_fin_generat
ing_family {N : Submodule R M} : N.FG ↔ exists (n : Nat) (s : Fin n -> M), span 
R (range s) = N
· 使用定理 `instFiniteULift`：∀ {α : Type v} [Finite α], Finite (ULift.{u, v} α)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
-/
lemma fg_iff_exists_finite_generating_family {A : Type u} [Semiring A] {M : Type v}
    [AddCommMonoid M] [Module A M] {N : Submodule A M} :
    N.FG ↔ ∃ (G : Type w) (_ : Finite G) (g : G → M), span A (range g) = N := by
  constructor
  · intro hN
    obtain ⟨n, f, h⟩ := fg_iff_exists_fin_generating_family.mp hN
    refine ⟨ULift (Fin n), inferInstance, f ∘ ULift.down, ?_⟩
    convert! h
    ext
    simp
  · rintro ⟨G, _, g, hg⟩
    have := Fintype.ofFinite (range g)
    exact ⟨(range g).toFinset, by simpa⟩
/-
**Submodule.fg_span_iff_fg_span_finset_subset** 是 Mathlib 中的一个定理，位于命名空间 `Submodu
le`。
形式化陈述：fg_span_iff_fg_span_finset_subset (s : Set M) : (span R s).FG ↔ exists s' 
: Finset M, ↑s' subseteq s ∧ span R s = span R s'
参数：s : Set M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.subset_span_finite_of_subset_span`：subset_span_finite_of_subse
t_span {s : Set M} {t : Finset M} (ht : (t : Set M) subseteq span R s) : exists 
T : Finset M, ↑T subseteq s ∧ (t …
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem fg_span_iff_fg_span_finset_subset (s : Set M) :
    (span R s).FG ↔ ∃ s' : Finset M, ↑s' ⊆ s ∧ span R s = span R s' := by
  constructor
  · intro ⟨s'', hs''⟩
    obtain ⟨s', hs's, hss'⟩ := subset_span_finite_of_subset_span <| hs'' ▸ subset_span
    refine ⟨s', hs's, ?_⟩
    apply le_antisymm
    · rwa [← hs'', span_le]
    · rw [span_le]
      exact le_trans hs's subset_span
  · intro ⟨s', _, h⟩
    exact ⟨s', h.symm⟩

end Submodule

namespace Ideal

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- An ideal of `R` is finitely generated if it is the span of a finite subset of `R`.

This is defeq to `Submodule.FG`, but unfolds more nicely. -/
/-
**Ideal.FG** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：FG (I : Ideal R) : Prop
参数：I : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ideal of `R` is finitely generated if it is the span of a finite subset of `R
`.

This is defeq to `Submodule.FG`, but unfolds more nicely.
-/
def FG (I : Ideal R) : Prop :=
  ∃ S : Finset R, span ↑S = I

end Ideal

section ModuleAndAlgebra

variable (R A B M N : Type*)

/-- A module over a semiring is `Module.Finite` if it is finitely generated as a module. -/
/-
**Module.Finite** 是 Mathlib 中的一个归纳类型，位于命名空间 `Module`。
形式化陈述：(R : Type u_1) → (M : Type u_4) → [inst : Semiring R] → [inst_1 : AddCommM
onoid M] → [_root_.Module R M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A module over a semiring is `Module.Finite` if it is finitely generated as a mod
ule.
-/
protected class Module.Finite [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
  of_fg_top ::
    fg_top : (⊤ : Submodule R M).FG

attribute [inherit_doc Module.Finite] Module.Finite.fg_top

namespace Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- See also `Module.Finite.iff_fg` for a version when `M` is itself a submodule. -/
/-
**Module.finite_def** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finite_def {R M} [Semiring R] [AddCommMonoid M] [Module R M] : Module.Fini
te R M ↔ (⊤ : Submodule R M).FG
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…

--- 原说明 ---
See also `Module.Finite.iff_fg` for a version when `M` is itself a submodule.
-/
theorem finite_def {R M} [Semiring R] [AddCommMonoid M] [Module R M] :
    Module.Finite R M ↔ (⊤ : Submodule R M).FG :=
  ⟨(·.fg_top), .of_fg_top⟩

namespace Finite

open Submodule Set

/-
**Module.Finite.iff_addMonoid_fg** 是 Mathlib 中的一个定理，位于命名空间 `Module.Finite`。
形式化陈述：iff_addMonoid_fg {M : Type*} [AddCommMonoid M] : Module.Finite Nat M ↔ Add
Monoid.FG M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddMonoid.fg_def`：∀ {M : Type u_1} [inst : AddMonoid M], AddMonoid.FG M 
↔ ⊤.FG
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.fg_iff_addSubmonoid_fg`：fg_iff_addSubmonoid_fg (P : Submodule 
Nat M) : P.FG ↔ P.toAddSubmonoid.FG
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…
-/
theorem iff_addMonoid_fg {M : Type*} [AddCommMonoid M] : Module.Finite ℕ M ↔ AddMonoid.FG M :=
  ⟨fun h => AddMonoid.fg_def.mpr <| (fg_iff_addSubmonoid_fg ⊤).mp h.fg_top,
    fun h => of_fg_top <| (fg_iff_addSubmonoid_fg ⊤).mpr (AddMonoid.fg_def.mp h)⟩
/-
**Module.Finite.iff_addGroup_fg** 是 Mathlib 中的一个定理，位于命名空间 `Module.Finite`。
形式化陈述：iff_addGroup_fg {G : Type*} [AddCommGroup G] : Module.Finite Int G ↔ AddGr
oup.FG G
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddGroup.fg_def`：AddGroup.fg_def : AddGroup.FG H ↔ (⊤ : AddSubgroup H).F
G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.fg_iff_addSubgroup_fg`：fg_iff_addSubgroup_fg {G : Type*} [AddC
ommGroup G] (P : Submodule Int G) : P.FG ↔ P.toAddSubgroup.FG
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…
-/
theorem iff_addGroup_fg {G : Type*} [AddCommGroup G] : Module.Finite ℤ G ↔ AddGroup.FG G :=
  ⟨fun h => AddGroup.fg_def.mpr <| (fg_iff_addSubgroup_fg ⊤).mp h.fg_top,
    fun h => of_fg_top <| (fg_iff_addSubgroup_fg ⊤).mpr (AddGroup.fg_def.mp h)⟩

variable {R M N}

/-- See also `Module.Finite.exists_fin'`. -/
/-
**Module.Finite.exists_fin** 是 Mathlib 中的一个引理，位于命名空间 `Module.Finite`。
形式化陈述：exists_fin [Module.Finite R M] : exists (n : Nat) (s : Fin n -> M), span R
 (range s) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.fg_iff_exists_fin_generating_family`：fg_iff_exists_fin_generat
ing_family {N : Submodule R M} : N.FG ↔ exists (n : Nat) (s : Fin n -> M), span 
R (range s) = N
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…

--- 原说明 ---
See also `Module.Finite.exists_fin'`.
-/
lemma exists_fin [Module.Finite R M] : ∃ (n : ℕ) (s : Fin n → M), span R (range s) = ⊤ :=
  fg_iff_exists_fin_generating_family.mp fg_top

end Finite

end Module

/-
**AddMonoid.FG.to_moduleFinite_nat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddMonoid.FG.to_moduleFinite_nat {M : Type*} [AddCommMonoid M] [FG M] : Mo
dule.Finite Nat M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Finite.iff_addMonoid_fg`：iff_addMonoid_fg {M : Type*} [AddCommMon
oid M] : Module.Finite Nat M ↔ AddMonoid.FG M
-/
instance AddMonoid.FG.to_moduleFinite_nat {M : Type*} [AddCommMonoid M] [FG M] :
    Module.Finite ℕ M :=
  Module.Finite.iff_addMonoid_fg.mpr ‹_›
/-
**AddMonoid.FG.to_moduleFinite_int** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddMonoid.FG.to_moduleFinite_int {G : Type*} [AddCommGroup G] [FG G] : Mod
ule.Finite Int G
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Finite.iff_addGroup_fg`：iff_addGroup_fg {G : Type*} [AddCommGroup
 G] : Module.Finite Int G ↔ AddGroup.FG G
· 使用定理 `AddGroup.fg_iff_addMonoid_fg`：∀ {G : Type u_3} [inst : AddGroup G], AddG
roup.FG G ↔ AddMonoid.FG G
-/
instance AddMonoid.FG.to_moduleFinite_int {G : Type*} [AddCommGroup G] [FG G] :
    Module.Finite ℤ G :=
  Module.Finite.iff_addGroup_fg.mpr <| AddGroup.fg_iff_addMonoid_fg.mpr ‹_›

end ModuleAndAlgebra

namespace RingHom

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- A ring morphism `A →+* B` is `RingHom.Finite` if `B` is finitely generated as `A`-module. -/
@[algebraize Module.Finite, stacks 0563]
/-
**RingHom.Finite** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：Finite (f : A ->+* B) : Prop
参数：f : A ->+* B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring morphism `A →+* B` is `RingHom.Finite` if `B` is finitely generated as `A
`-module.
-/
def Finite (f : A →+* B) : Prop :=
  letI : Algebra A B := f.toAlgebra
  Module.Finite A B

@[simp]
/-
**RingHom.finite_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：finite_algebraMap [Algebra A B] : (algebraMap A B).Finite ↔ Module.Finite 
A B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.Finite.eq_1`：∀ {A : Type u_1} {B : Type u_2} [inst : CommRing A]
 [inst_1 : CommRing B] (f : A →+* B), f.Finite = Module.Finite A B
· 使用定理 `toAlgebra_algebraMap`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R
] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   (algebraMap R S).toAlgebra
 = inst_2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma finite_algebraMap [Algebra A B] :
    (algebraMap A B).Finite ↔ Module.Finite A B := by
  rw [Finite, toAlgebra_algebraMap]

end RingHom

namespace AlgHom

variable {R A B C : Type*} [CommRing R]
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

/-- An algebra morphism `A →ₐ[R] B` is finite if it is finite as ring morphism.
In other words, if `B` is finitely generated as `A`-module. -/
/-
**AlgHom.Finite** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：Finite (f : A ->ₐ[R] B) : Prop
参数：f : A ->ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An algebra morphism `A →ₐ[R] B` is finite if it is finite as ring morphism.
In other words, if `B` is finitely generated as `A`-module.
-/
def Finite (f : A →ₐ[R] B) : Prop :=
  f.toRingHom.Finite

end AlgHom

